import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredEightDBFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredEightDBFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredEightDBFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredEightDBFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredEightDBFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredEightDBFastPow a n * oneHundredEightDBFastPow a n * a else oneHundredEightDBFastPow a n * oneHundredEightDBFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredEightDB_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredEightDB_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredEightDB_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredEightDB_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredEightDB_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredEightDB_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredEightDB_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredEightDB_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredEightDB_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredEightDB_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredEightDB_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredEightDB_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredEightDB_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredEightDB_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredEightDB_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredEightDB_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredEightDB_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredEightDB_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredEightDB_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredEightDB_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredEightDB_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredEightDB_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredEightDB_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredEightDB_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredEightDB_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredEightDB_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredEightDB_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredEightDB_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredEightDB_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredEightDB_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredEightDB_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredEightDB_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredEightDB_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredEightDB_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredEightDB_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredEightDB_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredEightDB_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredEightDB_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredEightDB_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredEightDB_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredEightDB_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredEightDB_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredEightDB_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredEightDB_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredEightDB_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredEightDB_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredEightDB_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredEightDB_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredEightDB_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredEightDB_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredEightDB_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredEightDB_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredEightDB_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredEightDB_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredEightDB_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredEightDB_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredEightDB_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredEightDB_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredEightDB_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredEightDB_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredEightDB_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredEightDB_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredEightDB_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredEightDB_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredEightDB_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredEightDB_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredEightDB_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredEightDB_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredEightDB_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredEightDB_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredEightDB_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredEightDB_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredEightDB_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredEightDB_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredEightDB_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredEightDB_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredEightDB_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredEightDB_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredEightDB_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredEightDB_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredEightDB_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredEightDB_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredEightDB_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredEightDB_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredEightDB_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredEightDB_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredEightDB_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredEightDB_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredEightDB_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredEightDB_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredEightDB_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredEightDB_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredEightDB_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredEightDB_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredEightDB_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredEightDB_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredEightDB_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredEightDB_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredEightDB_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredEightDB_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredEightDB_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredEightDB_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredEightDB_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_oneHundredEightDB_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredEightDB_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredEightDB_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredEightDB_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredEightDB_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_oneHundredEightDB_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredEightDB_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredEightDB_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_oneHundredEightDB_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredEightDB_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredEightDB_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredEightDB_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredEightDB_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_oneHundredEightDB_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredEightDB_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_oneHundredEightDB_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredEightDB_2161 : Nat.Prime 2161 := by norm_num

private theorem prime_oneHundredEightDB_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_oneHundredEightDB_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_oneHundredEightDB_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_oneHundredEightDB_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredEightDB_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_oneHundredEightDB_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_oneHundredEightDB_2617 : Nat.Prime 2617 := by norm_num

private theorem prime_oneHundredEightDB_2659 : Nat.Prime 2659 := by norm_num

private theorem prime_oneHundredEightDB_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_oneHundredEightDB_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredEightDB_2861 : Nat.Prime 2861 := by norm_num

private theorem prime_oneHundredEightDB_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredEightDB_3167 : Nat.Prime 3167 := by norm_num

private theorem prime_oneHundredEightDB_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredEightDB_3271 : Nat.Prime 3271 := by norm_num

private theorem prime_oneHundredEightDB_3433 : Nat.Prime 3433 := by norm_num

private theorem prime_oneHundredEightDB_3541 : Nat.Prime 3541 := by norm_num

private theorem prime_oneHundredEightDB_3733 : Nat.Prime 3733 := by norm_num

private theorem prime_oneHundredEightDB_3769 : Nat.Prime 3769 := by norm_num

private theorem prime_oneHundredEightDB_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_oneHundredEightDB_4271 : Nat.Prime 4271 := by norm_num

private theorem prime_oneHundredEightDB_4391 : Nat.Prime 4391 := by norm_num

private theorem prime_oneHundredEightDB_4409 : Nat.Prime 4409 := by norm_num

private theorem prime_oneHundredEightDB_4421 : Nat.Prime 4421 := by norm_num

private theorem prime_oneHundredEightDB_4423 : Nat.Prime 4423 := by norm_num

private theorem prime_oneHundredEightDB_4513 : Nat.Prime 4513 := by norm_num

private theorem prime_oneHundredEightDB_4703 : Nat.Prime 4703 := by norm_num

private theorem prime_oneHundredEightDB_4733 : Nat.Prime 4733 := by norm_num

private theorem prime_oneHundredEightDB_4871 : Nat.Prime 4871 := by norm_num

private theorem prime_oneHundredEightDB_4993 : Nat.Prime 4993 := by norm_num

private theorem prime_oneHundredEightDB_5101 : Nat.Prime 5101 := by norm_num

private theorem prime_oneHundredEightDB_5669 : Nat.Prime 5669 := by norm_num

private theorem prime_oneHundredEightDB_5927 : Nat.Prime 5927 := by norm_num

private theorem prime_oneHundredEightDB_5981 : Nat.Prime 5981 := by norm_num

private theorem prime_oneHundredEightDB_6007 : Nat.Prime 6007 := by norm_num

private theorem prime_oneHundredEightDB_6011 : Nat.Prime 6011 := by norm_num

private theorem prime_oneHundredEightDB_6323 : Nat.Prime 6323 := by norm_num

private theorem prime_oneHundredEightDB_6373 : Nat.Prime 6373 := by norm_num

private theorem prime_oneHundredEightDB_6427 : Nat.Prime 6427 := by norm_num

private theorem prime_oneHundredEightDB_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredEightDB_6977 : Nat.Prime 6977 := by norm_num

private theorem prime_oneHundredEightDB_7039 : Nat.Prime 7039 := by norm_num

private theorem prime_oneHundredEightDB_7129 : Nat.Prime 7129 := by norm_num

private theorem prime_oneHundredEightDB_7213 : Nat.Prime 7213 := by norm_num

private theorem prime_oneHundredEightDB_7411 : Nat.Prime 7411 := by norm_num

private theorem prime_oneHundredEightDB_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredEightDB_7573 : Nat.Prime 7573 := by norm_num

private theorem prime_oneHundredEightDB_7759 : Nat.Prime 7759 := by norm_num

private theorem prime_oneHundredEightDB_8167 : Nat.Prime 8167 := by norm_num

private theorem prime_oneHundredEightDB_8209 : Nat.Prime 8209 := by norm_num

private theorem prime_oneHundredEightDB_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredEightDB_8311 : Nat.Prime 8311 := by norm_num

private theorem prime_oneHundredEightDB_8377 : Nat.Prime 8377 := by norm_num

private theorem prime_oneHundredEightDB_8761 : Nat.Prime 8761 := by norm_num

private theorem prime_oneHundredEightDB_9013 : Nat.Prime 9013 := by norm_num

private theorem prime_oneHundredEightDB_9901 : Nat.Prime 9901 := by norm_num

private theorem prime_oneHundredEightDB_10337 : Nat.Prime 10337 := by norm_num

private theorem prime_oneHundredEightDB_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredEightDB_11689 : Nat.Prime 11689 := by norm_num

private theorem prime_oneHundredEightDB_11789 : Nat.Prime 11789 := by norm_num

private theorem prime_oneHundredEightDB_11821 : Nat.Prime 11821 := by norm_num

private theorem prime_oneHundredEightDB_12239 : Nat.Prime 12239 := by norm_num

private theorem prime_oneHundredEightDB_13103 : Nat.Prime 13103 := by norm_num

private theorem prime_oneHundredEightDB_13267 : Nat.Prime 13267 := by norm_num

private theorem prime_oneHundredEightDB_13669 : Nat.Prime 13669 := by norm_num

private theorem prime_oneHundredEightDB_13997 : Nat.Prime 13997 := by norm_num

private theorem prime_oneHundredEightDB_14033 : Nat.Prime 14033 := by norm_num

private theorem prime_oneHundredEightDB_14779 : Nat.Prime 14779 := by norm_num

private theorem prime_oneHundredEightDB_15091 : Nat.Prime 15091 := by norm_num

private theorem prime_oneHundredEightDB_15809 : Nat.Prime 15809 := by norm_num

private theorem prime_oneHundredEightDB_16139 : Nat.Prime 16139 := by norm_num

private theorem prime_oneHundredEightDB_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredEightDB_17393 : Nat.Prime 17393 := by norm_num

private theorem prime_oneHundredEightDB_18701 : Nat.Prime 18701 := by norm_num

private theorem prime_oneHundredEightDB_19141 : Nat.Prime 19141 := by norm_num

private theorem prime_oneHundredEightDB_19237 : Nat.Prime 19237 := by norm_num

private theorem prime_oneHundredEightDB_19421 : Nat.Prime 19421 := by norm_num

private theorem prime_oneHundredEightDB_19813 : Nat.Prime 19813 := by norm_num

private theorem prime_oneHundredEightDB_20113 : Nat.Prime 20113 := by norm_num

private theorem prime_oneHundredEightDB_20357 : Nat.Prime 20357 := by norm_num

private theorem prime_oneHundredEightDB_20681 : Nat.Prime 20681 := by norm_num

private theorem prime_oneHundredEightDB_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredEightDB_21323 : Nat.Prime 21323 := by norm_num

private theorem prime_oneHundredEightDB_21467 : Nat.Prime 21467 := by norm_num

private theorem prime_oneHundredEightDB_21617 : Nat.Prime 21617 := by norm_num

private theorem prime_oneHundredEightDB_21991 : Nat.Prime 21991 := by norm_num

private theorem prime_oneHundredEightDB_22433 : Nat.Prime 22433 := by norm_num

private theorem prime_oneHundredEightDB_23887 : Nat.Prime 23887 := by norm_num

private theorem prime_oneHundredEightDB_23929 : Nat.Prime 23929 := by norm_num

private theorem prime_oneHundredEightDB_24181 : Nat.Prime 24181 := by norm_num

private theorem prime_oneHundredEightDB_24337 : Nat.Prime 24337 := by norm_num

private theorem prime_oneHundredEightDB_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredEightDB_25247 : Nat.Prime 25247 := by norm_num

private theorem prime_oneHundredEightDB_26849 : Nat.Prime 26849 := by norm_num

private theorem prime_oneHundredEightDB_27539 : Nat.Prime 27539 := by norm_num

private theorem prime_oneHundredEightDB_27647 : Nat.Prime 27647 := by norm_num

private theorem prime_oneHundredEightDB_28403 : Nat.Prime 28403 := by norm_num

private theorem prime_oneHundredEightDB_28573 : Nat.Prime 28573 := by norm_num

private theorem prime_oneHundredEightDB_29251 : Nat.Prime 29251 := by norm_num

private theorem prime_oneHundredEightDB_29437 : Nat.Prime 29437 := by norm_num

private theorem prime_oneHundredEightDB_29669 : Nat.Prime 29669 := by norm_num

private theorem prime_oneHundredEightDB_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredEightDB_31573 : Nat.Prime 31573 := by norm_num

private theorem prime_oneHundredEightDB_32077 : Nat.Prime 32077 := by norm_num

private theorem prime_oneHundredEightDB_33091 : Nat.Prime 33091 := by norm_num

private theorem prime_oneHundredEightDB_33617 : Nat.Prime 33617 := by norm_num

private theorem prime_oneHundredEightDB_34739 : Nat.Prime 34739 := by norm_num

private theorem prime_oneHundredEightDB_36341 : Nat.Prime 36341 := by norm_num

private theorem prime_oneHundredEightDB_37361 : Nat.Prime 37361 := by norm_num

private theorem prime_oneHundredEightDB_40487 : Nat.Prime 40487 := by norm_num

private theorem prime_oneHundredEightDB_41257 : Nat.Prime 41257 := by norm_num

private theorem prime_oneHundredEightDB_42019 : Nat.Prime 42019 := by norm_num

private theorem prime_oneHundredEightDB_42379 : Nat.Prime 42379 := by norm_num

private theorem prime_oneHundredEightDB_45377 : Nat.Prime 45377 := by norm_num

private theorem prime_oneHundredEightDB_47639 : Nat.Prime 47639 := by norm_num

private theorem prime_oneHundredEightDB_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_oneHundredEightDB_47981 : Nat.Prime 47981 := by norm_num

private theorem prime_oneHundredEightDB_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredEightDB_48121 : Nat.Prime 48121 := by norm_num

private theorem prime_oneHundredEightDB_48571 : Nat.Prime 48571 := by norm_num

private theorem prime_oneHundredEightDB_49169 : Nat.Prime 49169 := by norm_num

private theorem prime_oneHundredEightDB_49613 : Nat.Prime 49613 := by norm_num

private theorem prime_oneHundredEightDB_51461 : Nat.Prime 51461 := by norm_num

private theorem prime_oneHundredEightDB_52067 : Nat.Prime 52067 := by norm_num

private theorem prime_oneHundredEightDB_52361 : Nat.Prime 52361 := by norm_num

private theorem prime_oneHundredEightDB_53231 : Nat.Prime 53231 := by norm_num

private theorem prime_oneHundredEightDB_53279 : Nat.Prime 53279 := by norm_num

private theorem prime_oneHundredEightDB_53791 : Nat.Prime 53791 := by norm_num

private theorem prime_oneHundredEightDB_54101 : Nat.Prime 54101 := by norm_num

private theorem prime_oneHundredEightDB_55147 : Nat.Prime 55147 := by norm_num

private theorem prime_oneHundredEightDB_55207 : Nat.Prime 55207 := by norm_num

private theorem prime_oneHundredEightDB_56821 : Nat.Prime 56821 := by norm_num

private theorem prime_oneHundredEightDB_59011 : Nat.Prime 59011 := by norm_num

private theorem prime_oneHundredEightDB_60133 : Nat.Prime 60133 := by norm_num

private theorem prime_oneHundredEightDB_61027 : Nat.Prime 61027 := by norm_num

private theorem prime_oneHundredEightDB_62701 : Nat.Prime 62701 := by norm_num

private theorem prime_oneHundredEightDB_65809 : Nat.Prime 65809 := by norm_num

private theorem prime_oneHundredEightDB_66373 : Nat.Prime 66373 := by norm_num

private theorem prime_oneHundredEightDB_67943 : Nat.Prime 67943 := by norm_num

private theorem prime_oneHundredEightDB_68449 : Nat.Prime 68449 := by norm_num

private theorem prime_oneHundredEightDB_69959 : Nat.Prime 69959 := by norm_num

private theorem prime_oneHundredEightDB_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredEightDB_79423 : Nat.Prime 79423 := by norm_num

private theorem prime_oneHundredEightDB_79847 : Nat.Prime 79847 := by norm_num

private theorem prime_oneHundredEightDB_80657 : Nat.Prime 80657 := by norm_num

private theorem prime_oneHundredEightDB_81307 : Nat.Prime 81307 := by norm_num

private theorem prime_oneHundredEightDB_82153 : Nat.Prime 82153 := by norm_num

private theorem prime_oneHundredEightDB_82811 : Nat.Prime 82811 := by norm_num

private theorem prime_oneHundredEightDB_84389 : Nat.Prime 84389 := by norm_num

private theorem prime_oneHundredEightDB_85159 : Nat.Prime 85159 := by norm_num

private theorem prime_oneHundredEightDB_85621 : Nat.Prime 85621 := by norm_num

private theorem prime_oneHundredEightDB_87539 : Nat.Prime 87539 := by norm_num

private theorem prime_oneHundredEightDB_88873 : Nat.Prime 88873 := by norm_num

private theorem prime_oneHundredEightDB_89833 : Nat.Prime 89833 := by norm_num

private theorem prime_oneHundredEightDB_95617 : Nat.Prime 95617 := by norm_num

private theorem prime_oneHundredEightDB_96289 : Nat.Prime 96289 := by norm_num

private theorem prime_oneHundredEightDB_97373 : Nat.Prime 97373 := by norm_num

private theorem prime_oneHundredEightDB_98507 : Nat.Prime 98507 := by norm_num

private theorem prime_oneHundredEightDB_101929 : Nat.Prime 101929 := by norm_num

private theorem prime_oneHundredEightDB_109849 : Nat.Prime 109849 := by norm_num

private theorem prime_oneHundredEightDB_114617 : Nat.Prime 114617 := by norm_num

private theorem prime_oneHundredEightDB_120157 : Nat.Prime 120157 := by norm_num

private theorem prime_oneHundredEightDB_121661 : Nat.Prime 121661 := by norm_num

private theorem prime_oneHundredEightDB_122701 : Nat.Prime 122701 := by norm_num

private theorem prime_oneHundredEightDB_125287 : Nat.Prime 125287 := by norm_num

private theorem prime_oneHundredEightDB_127669 : Nat.Prime 127669 := by norm_num

private theorem prime_oneHundredEightDB_132169 : Nat.Prime 132169 := by norm_num

private theorem prime_oneHundredEightDB_139303 : Nat.Prime 139303 := by norm_num

private theorem prime_oneHundredEightDB_140989 : Nat.Prime 140989 := by norm_num

private theorem prime_oneHundredEightDB_141853 : Nat.Prime 141853 := by norm_num

private theorem prime_oneHundredEightDB_156593 : Nat.Prime 156593 := by norm_num

private theorem prime_oneHundredEightDB_160907 : Nat.Prime 160907 := by norm_num

private theorem prime_oneHundredEightDB_163997 : Nat.Prime 163997 := by norm_num

private theorem prime_oneHundredEightDB_168263 : Nat.Prime 168263 := by norm_num

private theorem prime_oneHundredEightDB_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredEightDB_188911 : Nat.Prime 188911 := by norm_num

private theorem prime_oneHundredEightDB_192103 : Nat.Prime 192103 := by norm_num

private theorem prime_oneHundredEightDB_211231 : Nat.Prime 211231 := by norm_num

private theorem prime_oneHundredEightDB_212467 : Nat.Prime 212467 := by norm_num

private theorem prime_oneHundredEightDB_212557 : Nat.Prime 212557 := by norm_num

private theorem prime_oneHundredEightDB_221069 : Nat.Prime 221069 := by norm_num

private theorem prime_oneHundredEightDB_221197 : Nat.Prime 221197 := by norm_num

private theorem prime_oneHundredEightDB_223283 : Nat.Prime 223283 := by norm_num

private theorem prime_oneHundredEightDB_233341 : Nat.Prime 233341 := by norm_num

private theorem prime_oneHundredEightDB_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredEightDB_248839 : Nat.Prime 248839 := by norm_num

private theorem prime_oneHundredEightDB_256057 : Nat.Prime 256057 := by norm_num

private theorem prime_oneHundredEightDB_281317 : Nat.Prime 281317 := by norm_num

private theorem prime_oneHundredEightDB_284173 : Nat.Prime 284173 := by norm_num

private theorem prime_oneHundredEightDB_284833 : Nat.Prime 284833 := by norm_num

private theorem prime_oneHundredEightDB_287387 : Nat.Prime 287387 := by norm_num

private theorem prime_oneHundredEightDB_288689 : Nat.Prime 288689 := by norm_num

private theorem prime_oneHundredEightDB_297757 : Nat.Prime 297757 := by norm_num

private theorem prime_oneHundredEightDB_300331 : Nat.Prime 300331 := by norm_num

private theorem prime_oneHundredEightDB_322319 : Nat.Prime 322319 := by norm_num

private theorem prime_oneHundredEightDB_330203 : Nat.Prime 330203 := by norm_num

private theorem prime_oneHundredEightDB_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_oneHundredEightDB_354689 : Nat.Prime 354689 := by norm_num

private theorem prime_oneHundredEightDB_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredEightDB_364747 : Nat.Prime 364747 := by norm_num

private theorem prime_oneHundredEightDB_374111 : Nat.Prime 374111 := by norm_num

private theorem prime_oneHundredEightDB_388373 : Nat.Prime 388373 := by norm_num

private theorem prime_oneHundredEightDB_405373 : Nat.Prime 405373 := by norm_num

private theorem prime_oneHundredEightDB_412127 : Nat.Prime 412127 := by norm_num

private theorem prime_oneHundredEightDB_452989 : Nat.Prime 452989 := by norm_num

private theorem prime_oneHundredEightDB_460711 : Nat.Prime 460711 := by norm_num

private theorem prime_oneHundredEightDB_462577 : Nat.Prime 462577 := by norm_num

private theorem prime_oneHundredEightDB_519119 : Nat.Prime 519119 := by norm_num

private theorem prime_oneHundredEightDB_526681 : Nat.Prime 526681 := by norm_num

private theorem prime_oneHundredEightDB_529981 : Nat.Prime 529981 := by norm_num

private theorem prime_oneHundredEightDB_565517 : Nat.Prime 565517 := by norm_num

private theorem prime_oneHundredEightDB_577427 : Nat.Prime 577427 := by norm_num

private theorem prime_oneHundredEightDB_585911 : Nat.Prime 585911 := by norm_num

private theorem prime_oneHundredEightDB_594163 : Nat.Prime 594163 := by norm_num

private theorem prime_oneHundredEightDB_637841 : Nat.Prime 637841 := by norm_num

private theorem prime_oneHundredEightDB_640933 : Nat.Prime 640933 := by norm_num

private theorem prime_oneHundredEightDB_642877 : Nat.Prime 642877 := by norm_num

private theorem prime_oneHundredEightDB_643961 : Nat.Prime 643961 := by norm_num

private theorem prime_oneHundredEightDB_701609 : Nat.Prime 701609 := by norm_num

private theorem prime_oneHundredEightDB_733813 : Nat.Prime 733813 := by norm_num

private theorem prime_oneHundredEightDB_797869 : Nat.Prime 797869 := by norm_num

private theorem prime_oneHundredEightDB_810547 : Nat.Prime 810547 := by norm_num

private theorem prime_oneHundredEightDB_831221 : Nat.Prime 831221 := by norm_num

private theorem prime_oneHundredEightDB_862409 : Nat.Prime 862409 := by norm_num

private theorem prime_oneHundredEightDB_882253 : Nat.Prime 882253 := by norm_num

private theorem prime_oneHundredEightDB_904681 : Nat.Prime 904681 := by norm_num

private theorem prime_oneHundredEightDB_1012597 : Nat.Prime 1012597 := by norm_num

private theorem prime_oneHundredEightDB_1030817 : Nat.Prime 1030817 := by norm_num

private theorem prime_oneHundredEightDB_1047139 : Nat.Prime 1047139 := by norm_num

private theorem prime_oneHundredEightDB_1152937 : Nat.Prime 1152937 := by norm_num

private theorem prime_oneHundredEightDB_1154401 : Nat.Prime 1154401 := by norm_num

private theorem prime_oneHundredEightDB_1229519 : Nat.Prime 1229519 := by norm_num

private theorem prime_oneHundredEightDB_1245779 : Nat.Prime 1245779 := by norm_num

private theorem prime_oneHundredEightDB_1300681 : Nat.Prime 1300681 := by norm_num

private theorem prime_oneHundredEightDB_1379813 : Nat.Prime 1379813 := by norm_num

private theorem prime_oneHundredEightDB_1602869 : Nat.Prime 1602869 := by norm_num

private theorem prime_oneHundredEightDB_1743487 : Nat.Prime 1743487 := by norm_num

private theorem prime_oneHundredEightDB_1775887 : Nat.Prime 1775887 := by norm_num

private theorem prime_oneHundredEightDB_1804687 : Nat.Prime 1804687 := by norm_num

private theorem prime_oneHundredEightDB_1855891 : Nat.Prime 1855891 := by norm_num

private theorem prime_oneHundredEightDB_1901651 : Nat.Prime 1901651 := by norm_num

private theorem prime_oneHundredEightDB_2006689 : Nat.Prime 2006689 := by norm_num

private theorem prime_oneHundredEightDB_2155273 : Nat.Prime 2155273 := by norm_num

private theorem prime_oneHundredEightDB_2165483 : Nat.Prime 2165483 := by norm_num

private theorem prime_oneHundredEightDB_2396701 : Nat.Prime 2396701 := by norm_num

private theorem prime_oneHundredEightDB_2579581 : Nat.Prime 2579581 := by norm_num

private theorem prime_oneHundredEightDB_2623979 : Nat.Prime 2623979 := by norm_num

private theorem prime_oneHundredEightDB_2712719 : Nat.Prime 2712719 := by norm_num

private theorem prime_oneHundredEightDB_2800219 : Nat.Prime 2800219 := by norm_num

private theorem prime_oneHundredEightDB_3267727 : Nat.Prime 3267727 := by norm_num

private theorem prime_oneHundredEightDB_3649993 : Nat.Prime 3649993 := by norm_num

private theorem prime_oneHundredEightDB_3921217 : Nat.Prime 3921217 := by norm_num

private theorem prime_oneHundredEightDB_4042939 : Nat.Prime 4042939 := by norm_num

private theorem prime_oneHundredEightDB_4049443 : Nat.Prime 4049443 := by norm_num

private theorem prime_oneHundredEightDB_4735909 : Nat.Prime 4735909 := by norm_num

private theorem prime_oneHundredEightDB_4830151 : Nat.Prime 4830151 := by norm_num

private theorem prime_oneHundredEightDB_5064539 : Nat.Prime 5064539 := by norm_num

private theorem prime_oneHundredEightDB_5143253 : Nat.Prime 5143253 := by norm_num

private theorem prime_oneHundredEightDB_5816549 : Nat.Prime 5816549 := by norm_num

private theorem prime_oneHundredEightDB_5828189 : Nat.Prime 5828189 := by norm_num

private theorem prime_oneHundredEightDB_5956133 : Nat.Prime 5956133 := by norm_num

private theorem prime_oneHundredEightDB_6074531 : Nat.Prime 6074531 := by norm_num

private theorem prime_oneHundredEightDB_6128029 : Nat.Prime 6128029 := by norm_num

private theorem prime_oneHundredEightDB_6227671 : Nat.Prime 6227671 := by norm_num

private theorem prime_oneHundredEightDB_6336347 : Nat.Prime 6336347 := by norm_num

private theorem prime_oneHundredEightDB_7545367 : Nat.Prime 7545367 := by norm_num

private theorem prime_oneHundredEightDB_8398207 : Nat.Prime 8398207 := by norm_num

private theorem prime_oneHundredEightDB_8950913 : Nat.Prime 8950913 := by norm_num

private theorem prime_oneHundredEightDB_8996327 : Nat.Prime 8996327 := by norm_num

private theorem prime_oneHundredEightDB_9281453 : Nat.Prime 9281453 := by norm_num

private theorem prime_oneHundredEightDB_9522559 : Nat.Prime 9522559 := by norm_num

private theorem prime_oneHundredEightDB_9569821 : Nat.Prime 9569821 := by norm_num

private theorem prime_oneHundredEightDB_9606671 : Nat.Prime 9606671 := by norm_num

private theorem prime_oneHundredEightDB_10210243 : Nat.Prime 10210243 := by norm_num

private theorem prime_oneHundredEightDB_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredEightDB_10895267 : Nat.Prime 10895267 := by norm_num

private theorem prime_oneHundredEightDB_11400581 : Nat.Prime 11400581 := by norm_num

private theorem prime_oneHundredEightDB_11601731 : Nat.Prime 11601731 := by norm_num

private theorem prime_oneHundredEightDB_12300311 : Nat.Prime 12300311 := by norm_num

private theorem prime_oneHundredEightDB_13680577 : Nat.Prime 13680577 := by norm_num

private theorem prime_oneHundredEightDB_14201963 : Nat.Prime 14201963 := by norm_num

private theorem prime_oneHundredEightDB_14446457 : Nat.Prime 14446457 := by norm_num

private theorem prime_oneHundredEightDB_14668343 : Nat.Prime 14668343 := by norm_num

private theorem prime_oneHundredEightDB_15978517 : Nat.Prime 15978517 := by norm_num

private theorem prime_oneHundredEightDB_16591039 : Nat.Prime 16591039 := by norm_num

private theorem prime_oneHundredEightDB_17833891 : Nat.Prime 17833891 := by norm_num

private theorem prime_oneHundredEightDB_18572501 : Nat.Prime 18572501 := by norm_num

private theorem prime_oneHundredEightDB_20226677 : Nat.Prime 20226677 := by norm_num

private theorem prime_oneHundredEightDB_21338189 : Nat.Prime 21338189 := by norm_num

private theorem prime_oneHundredEightDB_25069433 : Nat.Prime 25069433 := by norm_num

private theorem prime_oneHundredEightDB_25375709 : Nat.Prime 25375709 := by norm_num

private theorem prime_oneHundredEightDB_28293619 : Nat.Prime 28293619 := by norm_num

private theorem prime_oneHundredEightDB_31458437 : Nat.Prime 31458437 := by
  apply lucas_primality 31458437 (2 : ZMod 31458437)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (212557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (212557, 1)] : List FactorBlock).map factorBlockValue).prod) = 31458437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_37
      · exact prime_oneHundredEightDB_212557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31458437) ^ 15729218 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 31458437) ^ 850228 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 31458437) ^ 148 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_31775371 : Nat.Prime 31775371 := by
  apply lucas_primality 31775371 (2 : ZMod 31775371)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (96289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (96289, 1)] : List FactorBlock).map factorBlockValue).prod) = 31775371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_96289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31775371) ^ 15887685 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 31775371) ^ 10591790 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 31775371) ^ 6355074 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 31775371) ^ 2888670 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 31775371) ^ 330 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_32246411 : Nat.Prime 32246411 := by
  apply lucas_primality 32246411 (2 : ZMod 32246411)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (65809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (65809, 1)] : List FactorBlock).map factorBlockValue).prod) = 32246411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_65809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32246411) ^ 16123205 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 32246411) ^ 6449282 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 32246411) ^ 4606630 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 32246411) ^ 490 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_32934523 : Nat.Prime 32934523 := by
  apply lucas_primality 32934523 (3 : ZMod 32934523)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (227, 1), (24181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (227, 1), (24181, 1)] : List FactorBlock).map factorBlockValue).prod) = 32934523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_227
      · exact prime_oneHundredEightDB_24181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32934523) ^ 16467261 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32934523) ^ 10978174 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32934523) ^ 145086 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32934523) ^ 1362 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_33677233 : Nat.Prime 33677233 := by
  apply lucas_primality 33677233 (5 : ZMod 33677233)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (701609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (701609, 1)] : List FactorBlock).map factorBlockValue).prod) = 33677233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_701609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33677233) ^ 16838616 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 33677233) ^ 11225744 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 33677233) ^ 48 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_34763647 : Nat.Prime 34763647 := by
  apply lucas_primality 34763647 (3 : ZMod 34763647)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (156593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (156593, 1)] : List FactorBlock).map factorBlockValue).prod) = 34763647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_37
      · exact prime_oneHundredEightDB_156593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34763647) ^ 17381823 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 34763647) ^ 11587882 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 34763647) ^ 939558 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 34763647) ^ 222 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_37097537 : Nat.Prime 37097537 := by
  apply lucas_primality 37097537 (3 : ZMod 37097537)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) = 37097537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_4871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37097537) ^ 18548768 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 5299648 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 2182208 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 7616 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_37958111 : Nat.Prime 37958111 := by
  apply lucas_primality 37958111 (7 : ZMod 37958111)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (223283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (223283, 1)] : List FactorBlock).map factorBlockValue).prod) = 37958111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_223283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 37958111) ^ 18979055 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 37958111) ^ 7591622 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 37958111) ^ 2232830 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 37958111) ^ 170 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_38879033 : Nat.Prime 38879033 := by
  apply lucas_primality 38879033 (3 : ZMod 38879033)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (68449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (68449, 1)] : List FactorBlock).map factorBlockValue).prod) = 38879033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_71
      · exact prime_oneHundredEightDB_68449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38879033) ^ 19439516 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 38879033) ^ 547592 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 38879033) ^ 568 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_40516313 : Nat.Prime 40516313 := by
  apply lucas_primality 40516313 (3 : ZMod 40516313)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5064539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5064539, 1)] : List FactorBlock).map factorBlockValue).prod) = 40516313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5064539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 40516313) ^ 20258156 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 40516313) ^ 8 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_42135017 : Nat.Prime 42135017 := by
  apply lucas_primality 42135017 (3 : ZMod 42135017)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (73, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (73, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) = 42135017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_73
      · exact prime_oneHundredEightDB_937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42135017) ^ 21067508 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 42135017) ^ 6019288 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 42135017) ^ 3830456 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 42135017) ^ 577192 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 42135017) ^ 44968 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_42676379 : Nat.Prime 42676379 := by
  apply lucas_primality 42676379 (2 : ZMod 42676379)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21338189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21338189, 1)] : List FactorBlock).map factorBlockValue).prod) = 42676379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_21338189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 42676379) ^ 21338189 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 42676379) ^ 2 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_44618071 : Nat.Prime 44618071 := by
  apply lucas_primality 44618071 (3 : ZMod 44618071)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (212467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (212467, 1)] : List FactorBlock).map factorBlockValue).prod) = 44618071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_212467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44618071) ^ 22309035 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 44618071) ^ 14872690 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 44618071) ^ 8923614 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 44618071) ^ 6374010 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 44618071) ^ 210 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_45399371 : Nat.Prime 45399371 := by
  apply lucas_primality 45399371 (2 : ZMod 45399371)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (122701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (122701, 1)] : List FactorBlock).map factorBlockValue).prod) = 45399371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_37
      · exact prime_oneHundredEightDB_122701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45399371) ^ 22699685 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 45399371) ^ 9079874 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 45399371) ^ 1227010 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 45399371) ^ 370 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_45896161 : Nat.Prime 45896161 := by
  apply lucas_primality 45896161 (14 : ZMod 45896161)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (95617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (95617, 1)] : List FactorBlock).map factorBlockValue).prod) = 45896161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_95617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 45896161) ^ 22948080 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 45896161) ^ 15298720 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 45896161) ^ 9179232 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 45896161) ^ 480 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_49263077 : Nat.Prime 49263077 := by
  apply lucas_primality 49263077 (2 : ZMod 49263077)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (53, 1), (13669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (53, 1), (13669, 1)] : List FactorBlock).map factorBlockValue).prod) = 49263077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_53
      · exact prime_oneHundredEightDB_13669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49263077) ^ 24631538 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 49263077) ^ 2897828 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 49263077) ^ 929492 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 49263077) ^ 3604 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_50068567 : Nat.Prime 50068567 := by
  apply lucas_primality 50068567 (5 : ZMod 50068567)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1439, 1), (1933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1439, 1), (1933, 1)] : List FactorBlock).map factorBlockValue).prod) = 50068567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_1439
      · exact prime_oneHundredEightDB_1933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 50068567) ^ 25034283 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 50068567) ^ 16689522 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 50068567) ^ 34794 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 50068567) ^ 25902 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_52474501 : Nat.Prime 52474501 := by
  apply lucas_primality 52474501 (14 : ZMod 52474501)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 3), (13, 2), (23, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 3), (13, 2), (23, 1)] : List FactorBlock).map factorBlockValue).prod) = 52474501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_23
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 52474501) ^ 26237250 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 17491500 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 10494900 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 4036500 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 2281500 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_52943941 : Nat.Prime 52943941 := by
  apply lucas_primality 52943941 (2 : ZMod 52943941)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (42019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (42019, 1)] : List FactorBlock).map factorBlockValue).prod) = 52943941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_42019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52943941) ^ 26471970 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 52943941) ^ 17647980 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 52943941) ^ 10588788 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 52943941) ^ 7563420 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 52943941) ^ 1260 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_56545507 : Nat.Prime 56545507 := by
  apply lucas_primality 56545507 (2 : ZMod 56545507)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1047139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1047139, 1)] : List FactorBlock).map factorBlockValue).prod) = 56545507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_1047139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 56545507) ^ 28272753 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 56545507) ^ 18848502 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 56545507) ^ 54 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_59503181 : Nat.Prime 59503181 := by
  apply lucas_primality 59503181 (12 : ZMod 59503181)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (179, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (179, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) = 59503181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_179
      · exact prime_oneHundredEightDB_1511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 59503181) ^ 29751590 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (12 : ZMod 59503181) ^ 11900636 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (12 : ZMod 59503181) ^ 5409380 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (12 : ZMod 59503181) ^ 332420 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (12 : ZMod 59503181) ^ 39380 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_1811
      · exact prime_oneHundredEightDB_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_61405583 : Nat.Prime 61405583 := by
  apply lucas_primality 61405583 (5 : ZMod 61405583)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) = 61405583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_149
      · exact prime_oneHundredEightDB_29437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 61405583) ^ 30702791 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 8772226 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 412118 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 2086 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_62739473 : Nat.Prime 62739473 := by
  apply lucas_primality 62739473 (3 : ZMod 62739473)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3921217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3921217, 1)] : List FactorBlock).map factorBlockValue).prod) = 62739473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3921217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 62739473) ^ 31369736 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 62739473) ^ 16 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_70496453 : Nat.Prime 70496453 := by
  apply lucas_primality 70496453 (2 : ZMod 70496453)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (467, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (467, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) = 70496453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_467
      · exact prime_oneHundredEightDB_2903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70496453) ^ 35248226 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 70496453) ^ 5422804 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 70496453) ^ 150956 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 70496453) ^ 24284 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_71062319 : Nat.Prime 71062319 := by
  apply lucas_primality 71062319 (11 : ZMod 71062319)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (23, 1), (81307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (23, 1), (81307, 1)] : List FactorBlock).map factorBlockValue).prod) = 71062319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_81307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 71062319) ^ 35531159 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 71062319) ^ 3740122 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 71062319) ^ 3089666 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 71062319) ^ 874 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_79789841 : Nat.Prime 79789841 := by
  apply lucas_primality 79789841 (3 : ZMod 79789841)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (17, 1), (4513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (17, 1), (4513, 1)] : List FactorBlock).map factorBlockValue).prod) = 79789841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_4513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 79789841) ^ 39894920 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 79789841) ^ 15957968 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 79789841) ^ 6137680 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 79789841) ^ 4693520 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 79789841) ^ 17680 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_81747059 : Nat.Prime 81747059 := by
  apply lucas_primality 81747059 (2 : ZMod 81747059)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (401, 1), (101929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (401, 1), (101929, 1)] : List FactorBlock).map factorBlockValue).prod) = 81747059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_401
      · exact prime_oneHundredEightDB_101929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 81747059) ^ 40873529 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 81747059) ^ 203858 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 81747059) ^ 802 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_125356337 : Nat.Prime 125356337 := by
  apply lucas_primality 125356337 (6 : ZMod 125356337)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (157, 1), (7129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (157, 1), (7129, 1)] : List FactorBlock).map factorBlockValue).prod) = 125356337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_157
      · exact prime_oneHundredEightDB_7129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 125356337) ^ 62678168 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 125356337) ^ 17908048 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 125356337) ^ 798448 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 125356337) ^ 17584 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_125925043 : Nat.Prime 125925043 := by
  apply lucas_primality 125925043 (2 : ZMod 125925043)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3541, 1), (5927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3541, 1), (5927, 1)] : List FactorBlock).map factorBlockValue).prod) = 125925043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_3541
      · exact prime_oneHundredEightDB_5927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 125925043) ^ 62962521 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 125925043) ^ 41975014 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 125925043) ^ 35562 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 125925043) ^ 21246 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_131433079 : Nat.Prime 131433079 := by
  apply lucas_primality 131433079 (17 : ZMod 131433079)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) = 131433079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_223
      · exact prime_oneHundredEightDB_14033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 131433079) ^ 65716539 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 43811026 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 18776154 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 589386 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 9366 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_139568171 : Nat.Prime 139568171 := by
  apply lucas_primality 139568171 (2 : ZMod 139568171)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) = 139568171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_284833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139568171) ^ 69784085 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 27913634 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 19938310 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 490 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_159579683 : Nat.Prime 159579683 := by
  apply lucas_primality 159579683 (2 : ZMod 159579683)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79789841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79789841, 1)] : List FactorBlock).map factorBlockValue).prod) = 159579683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_79789841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 159579683) ^ 79789841 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 159579683) ^ 2 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_178215673 : Nat.Prime 178215673 := by
  apply lucas_primality 178215673 (5 : ZMod 178215673)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (256057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (256057, 1)] : List FactorBlock).map factorBlockValue).prod) = 178215673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_256057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 178215673) ^ 89107836 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 178215673) ^ 59405224 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 178215673) ^ 6145368 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 178215673) ^ 696 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_189006211 : Nat.Prime 189006211 := by
  apply lucas_primality 189006211 (3 : ZMod 189006211)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (233341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (233341, 1)] : List FactorBlock).map factorBlockValue).prod) = 189006211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_233341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 189006211) ^ 94503105 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 189006211) ^ 63002070 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 189006211) ^ 37801242 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 189006211) ^ 810 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_196015331 : Nat.Prime 196015331 := by
  apply lucas_primality 196015331 (7 : ZMod 196015331)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2800219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2800219, 1)] : List FactorBlock).map factorBlockValue).prod) = 196015331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_2800219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 196015331) ^ 98007665 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 196015331) ^ 39203066 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 196015331) ^ 28002190 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 196015331) ^ 70 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_202063399 : Nat.Prime 202063399 := by
  apply lucas_primality 202063399 (3 : ZMod 202063399)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (33677233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (33677233, 1)] : List FactorBlock).map factorBlockValue).prod) = 202063399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_33677233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 202063399) ^ 101031699 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 202063399) ^ 67354466 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 202063399) ^ 6 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_213150073 : Nat.Prime 213150073 := by
  apply lucas_primality 213150073 (5 : ZMod 213150073)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) = 213150073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_73
      · exact prime_oneHundredEightDB_121661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 213150073) ^ 106575036 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 71050024 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 2919864 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 1752 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_226182029 : Nat.Prime 226182029 := by
  apply lucas_primality 226182029 (2 : ZMod 226182029)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (56545507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (56545507, 1)] : List FactorBlock).map factorBlockValue).prod) = 226182029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_56545507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 226182029) ^ 113091014 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 226182029) ^ 4 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_252309923 : Nat.Prime 252309923 := by
  apply lucas_primality 252309923 (2 : ZMod 252309923)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9013, 1), (13997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9013, 1), (13997, 1)] : List FactorBlock).map factorBlockValue).prod) = 252309923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_9013
      · exact prime_oneHundredEightDB_13997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 252309923) ^ 126154961 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 252309923) ^ 27994 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 252309923) ^ 18026 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_295578463 : Nat.Prime 295578463 := by
  apply lucas_primality 295578463 (3 : ZMod 295578463)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (49263077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (49263077, 1)] : List FactorBlock).map factorBlockValue).prod) = 295578463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_49263077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 295578463) ^ 147789231 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 295578463) ^ 98526154 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 295578463) ^ 6 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_314847007 : Nat.Prime 314847007 := by
  apply lucas_primality 314847007 (5 : ZMod 314847007)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (52474501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (52474501, 1)] : List FactorBlock).map factorBlockValue).prod) = 314847007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_52474501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 314847007) ^ 157423503 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 314847007) ^ 104949002 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 314847007) ^ 6 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_320845783 : Nat.Prime 320845783 := by
  apply lucas_primality 320845783 (5 : ZMod 320845783)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (53, 1), (21467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (53, 1), (21467, 1)] : List FactorBlock).map factorBlockValue).prod) = 320845783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_53
      · exact prime_oneHundredEightDB_21467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 320845783) ^ 160422891 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 320845783) ^ 106948594 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 320845783) ^ 6826506 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 320845783) ^ 6053694 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 320845783) ^ 14946 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_402645769 : Nat.Prime 402645769 := by
  apply lucas_primality 402645769 (26 : ZMod 402645769)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (2396701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (2396701, 1)] : List FactorBlock).map factorBlockValue).prod) = 402645769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_2396701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 402645769) ^ 201322884 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (26 : ZMod 402645769) ^ 134215256 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (26 : ZMod 402645769) ^ 57520824 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (26 : ZMod 402645769) ^ 168 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_404920409 : Nat.Prime 404920409 := by
  apply lucas_primality 404920409 (3 : ZMod 404920409)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (359, 1), (140989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (359, 1), (140989, 1)] : List FactorBlock).map factorBlockValue).prod) = 404920409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_359
      · exact prime_oneHundredEightDB_140989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 404920409) ^ 202460204 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 404920409) ^ 1127912 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 404920409) ^ 2872 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_438189827 : Nat.Prime 438189827 := by
  apply lucas_primality 438189827 (2 : ZMod 438189827)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (157, 1), (48121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (157, 1), (48121, 1)] : List FactorBlock).map factorBlockValue).prod) = 438189827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_157
      · exact prime_oneHundredEightDB_48121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 438189827) ^ 219094913 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 438189827) ^ 15109994 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 438189827) ^ 2791018 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 438189827) ^ 9106 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_452722021 : Nat.Prime 452722021 := by
  apply lucas_primality 452722021 (7 : ZMod 452722021)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7545367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7545367, 1)] : List FactorBlock).map factorBlockValue).prod) = 452722021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7545367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 452722021) ^ 226361010 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 452722021) ^ 150907340 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 452722021) ^ 90544404 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 452722021) ^ 60 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_511339019 : Nat.Prime 511339019 := by
  apply lucas_primality 511339019 (2 : ZMod 511339019)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (71, 1), (67943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (71, 1), (67943, 1)] : List FactorBlock).map factorBlockValue).prod) = 511339019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_53
      · exact prime_oneHundredEightDB_71
      · exact prime_oneHundredEightDB_67943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 511339019) ^ 255669509 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 511339019) ^ 9647906 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 511339019) ^ 7201958 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 511339019) ^ 7526 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_540182551 : Nat.Prime 540182551 := by
  apply lucas_primality 540182551 (17 : ZMod 540182551)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1049, 1), (3433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1049, 1), (3433, 1)] : List FactorBlock).map factorBlockValue).prod) = 540182551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_1049
      · exact prime_oneHundredEightDB_3433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 540182551) ^ 270091275 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 180060850 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 108036510 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 514950 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 157350 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_559319647 : Nat.Prime 559319647 := by
  apply lucas_primality 559319647 (3 : ZMod 559319647)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) = 559319647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_59
      · exact prime_oneHundredEightDB_33617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 559319647) ^ 279659823 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 186439882 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 11900418 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 9479994 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 16638 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_587894707 : Nat.Prime 587894707 := by
  apply lucas_primality 587894707 (3 : ZMod 587894707)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (47, 1), (33091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (47, 1), (33091, 1)] : List FactorBlock).map factorBlockValue).prod) = 587894707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_33091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 587894707) ^ 293947353 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 587894707) ^ 195964902 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 587894707) ^ 83984958 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 587894707) ^ 12508398 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 587894707) ^ 17766 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_614504323 : Nat.Prime 614504323 := by
  apply lucas_primality 614504323 (2 : ZMod 614504323)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4733, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4733, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) = 614504323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_4733
      · exact prime_oneHundredEightDB_7213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 614504323) ^ 307252161 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 614504323) ^ 204834774 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 614504323) ^ 129834 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 614504323) ^ 85194 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_61
      · exact prime_oneHundredEightDB_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_17203
      · exact prime_oneHundredEightDB_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_799813957 : Nat.Prime 799813957 := by
  apply lucas_primality 799813957 (2 : ZMod 799813957)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1063, 1), (62701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1063, 1), (62701, 1)] : List FactorBlock).map factorBlockValue).prod) = 799813957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_1063
      · exact prime_oneHundredEightDB_62701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 799813957) ^ 399906978 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 799813957) ^ 266604652 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 799813957) ^ 752412 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 799813957) ^ 12756 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_808530187 : Nat.Prime 808530187 := by
  apply lucas_primality 808530187 (2 : ZMod 808530187)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6007, 1), (22433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6007, 1), (22433, 1)] : List FactorBlock).map factorBlockValue).prod) = 808530187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_6007
      · exact prime_oneHundredEightDB_22433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 808530187) ^ 404265093 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 808530187) ^ 269510062 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 808530187) ^ 134598 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 808530187) ^ 36042 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_841651051 : Nat.Prime 841651051 := by
  apply lucas_primality 841651051 (13 : ZMod 841651051)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (29, 1), (191, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (29, 1), (191, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) = 841651051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_191
      · exact prime_oneHundredEightDB_1013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 841651051) ^ 420825525 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (13 : ZMod 841651051) ^ 280550350 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (13 : ZMod 841651051) ^ 168330210 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (13 : ZMod 841651051) ^ 29022450 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (13 : ZMod 841651051) ^ 4406550 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (13 : ZMod 841651051) ^ 830850 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_886981163 : Nat.Prime 886981163 := by
  apply lucas_primality 886981163 (2 : ZMod 886981163)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (227, 1), (8761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (227, 1), (8761, 1)] : List FactorBlock).map factorBlockValue).prod) = 886981163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_223
      · exact prime_oneHundredEightDB_227
      · exact prime_oneHundredEightDB_8761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 886981163) ^ 443490581 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 886981163) ^ 3977494 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 886981163) ^ 3907406 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 886981163) ^ 101242 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_906208483 : Nat.Prime 906208483 := by
  apply lucas_primality 906208483 (2 : ZMod 906208483)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) = 906208483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_131
      · exact prime_oneHundredEightDB_1152937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906208483) ^ 453104241 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 302069494 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 6917622 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 786 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_945329461 : Nat.Prime 945329461 := by
  apply lucas_primality 945329461 (2 : ZMod 945329461)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (151, 2), (691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (151, 2), (691, 1)] : List FactorBlock).map factorBlockValue).prod) = 945329461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_151
      · exact prime_oneHundredEightDB_691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 945329461) ^ 472664730 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 315109820 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 189065892 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 6260460 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 1368060 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_971025637 : Nat.Prime 971025637 := by
  apply lucas_primality 971025637 (2 : ZMod 971025637)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (233, 1), (49613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (233, 1), (49613, 1)] : List FactorBlock).map factorBlockValue).prod) = 971025637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_233
      · exact prime_oneHundredEightDB_49613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 971025637) ^ 485512818 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 971025637) ^ 323675212 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 971025637) ^ 138717948 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 971025637) ^ 4167492 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 971025637) ^ 19572 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1800601883 : Nat.Prime 1800601883 := by
  apply lucas_primality 1800601883 (2 : ZMod 1800601883)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (9281453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (9281453, 1)] : List FactorBlock).map factorBlockValue).prod) = 1800601883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_97
      · exact prime_oneHundredEightDB_9281453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1800601883) ^ 900300941 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1800601883) ^ 18562906 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1800601883) ^ 194 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1889082043 : Nat.Prime 1889082043 := by
  apply lucas_primality 1889082043 (2 : ZMod 1889082043)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (314847007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (314847007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1889082043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_314847007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1889082043) ^ 944541021 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1889082043) ^ 629694014 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1889082043) ^ 6 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2097174487 : Nat.Prime 2097174487 := by
  apply lucas_primality 2097174487 (3 : ZMod 2097174487)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (31775371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (31775371, 1)] : List FactorBlock).map factorBlockValue).prod) = 2097174487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_31775371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2097174487) ^ 1048587243 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2097174487) ^ 699058162 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2097174487) ^ 190652226 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2097174487) ^ 66 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2115948589 : Nat.Prime 2115948589 := by
  apply lucas_primality 2115948589 (2 : ZMod 2115948589)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17, 1), (797869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17, 1), (797869, 1)] : List FactorBlock).map factorBlockValue).prod) = 2115948589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_797869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2115948589) ^ 1057974294 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115948589) ^ 705316196 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115948589) ^ 162765276 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115948589) ^ 124467564 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115948589) ^ 2652 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_71
      · exact prime_oneHundredEightDB_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2619477239 : Nat.Prime 2619477239 := by
  apply lucas_primality 2619477239 (7 : ZMod 2619477239)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (7411, 1), (25247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (7411, 1), (25247, 1)] : List FactorBlock).map factorBlockValue).prod) = 2619477239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_7411
      · exact prime_oneHundredEightDB_25247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2619477239) ^ 1309738619 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2619477239) ^ 374211034 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2619477239) ^ 353458 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2619477239) ^ 103754 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2802154111 : Nat.Prime 2802154111 := by
  apply lucas_primality 2802154111 (3 : ZMod 2802154111)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (467, 1), (28573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (467, 1), (28573, 1)] : List FactorBlock).map factorBlockValue).prod) = 2802154111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_467
      · exact prime_oneHundredEightDB_28573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2802154111) ^ 1401077055 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2802154111) ^ 934051370 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2802154111) ^ 560430822 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2802154111) ^ 400307730 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2802154111) ^ 6000330 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2802154111) ^ 98070 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_3113942707 : Nat.Prime 3113942707 := by
  apply lucas_primality 3113942707 (2 : ZMod 3113942707)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (83, 1), (297757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (83, 1), (297757, 1)] : List FactorBlock).map factorBlockValue).prod) = 3113942707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_83
      · exact prime_oneHundredEightDB_297757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3113942707) ^ 1556971353 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3113942707) ^ 1037980902 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3113942707) ^ 444848958 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3113942707) ^ 37517382 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3113942707) ^ 10458 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_3163746367 : Nat.Prime 3163746367 := by
  apply lucas_primality 3163746367 (3 : ZMod 3163746367)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (15978517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (15978517, 1)] : List FactorBlock).map factorBlockValue).prod) = 3163746367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_15978517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3163746367) ^ 1581873183 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3163746367) ^ 1054582122 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3163746367) ^ 287613306 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3163746367) ^ 198 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_3910831549 : Nat.Prime 3910831549 := by
  apply lucas_primality 3910831549 (2 : ZMod 3910831549)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (25069433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (25069433, 1)] : List FactorBlock).map factorBlockValue).prod) = 3910831549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_25069433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3910831549) ^ 1955415774 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3910831549) ^ 1303610516 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3910831549) ^ 300833196 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3910831549) ^ 156 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_4088445211 : Nat.Prime 4088445211 := by
  apply lucas_primality 4088445211 (3 : ZMod 4088445211)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (277, 1), (163997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (277, 1), (163997, 1)] : List FactorBlock).map factorBlockValue).prod) = 4088445211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_277
      · exact prime_oneHundredEightDB_163997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4088445211) ^ 2044222605 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4088445211) ^ 1362815070 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4088445211) ^ 817689042 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4088445211) ^ 14759730 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4088445211) ^ 24930 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_4092387857 : Nat.Prime 4092387857 := by
  apply lucas_primality 4092387857 (3 : ZMod 4092387857)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (401, 1), (637841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (401, 1), (637841, 1)] : List FactorBlock).map factorBlockValue).prod) = 4092387857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_401
      · exact prime_oneHundredEightDB_637841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4092387857) ^ 2046193928 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4092387857) ^ 10205456 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4092387857) ^ 6416 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_4292409581 : Nat.Prime 4292409581 := by
  apply lucas_primality 4292409581 (2 : ZMod 4292409581)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (53, 1), (4049443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (53, 1), (4049443, 1)] : List FactorBlock).map factorBlockValue).prod) = 4292409581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_53
      · exact prime_oneHundredEightDB_4049443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4292409581) ^ 2146204790 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4292409581) ^ 858481916 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4292409581) ^ 80988860 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4292409581) ^ 1060 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_5579255821 : Nat.Prime 5579255821 := by
  apply lucas_primality 5579255821 (2 : ZMod 5579255821)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (4042939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (4042939, 1)] : List FactorBlock).map factorBlockValue).prod) = 5579255821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_4042939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5579255821) ^ 2789627910 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5579255821) ^ 1859751940 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5579255821) ^ 1115851164 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5579255821) ^ 242576340 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 5579255821) ^ 1380 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_5637863041 : Nat.Prime 5637863041 := by
  apply lucas_primality 5637863041 (7 : ZMod 5637863041)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (23, 1), (127669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (23, 1), (127669, 1)] : List FactorBlock).map factorBlockValue).prod) = 5637863041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_127669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5637863041) ^ 2818931520 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 5637863041) ^ 1879287680 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 5637863041) ^ 1127572608 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 5637863041) ^ 245124480 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 5637863041) ^ 44160 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_31
      · exact prime_oneHundredEightDB_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_6197501251 : Nat.Prime 6197501251 := by
  apply lucas_primality 6197501251 (3 : ZMod 6197501251)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 4), (71, 1), (7759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 4), (71, 1), (7759, 1)] : List FactorBlock).map factorBlockValue).prod) = 6197501251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_71
      · exact prime_oneHundredEightDB_7759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6197501251) ^ 3098750625 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6197501251) ^ 2065833750 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6197501251) ^ 1239500250 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6197501251) ^ 87288750 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6197501251) ^ 798750 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_6265973617 : Nat.Prime 6265973617 := by
  apply lucas_primality 6265973617 (5 : ZMod 6265973617)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (227, 1), (82153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (227, 1), (82153, 1)] : List FactorBlock).map factorBlockValue).prod) = 6265973617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_227
      · exact prime_oneHundredEightDB_82153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6265973617) ^ 3132986808 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6265973617) ^ 2088657872 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6265973617) ^ 895139088 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6265973617) ^ 27603408 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6265973617) ^ 76272 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_6486735053 : Nat.Prime 6486735053 := by
  apply lucas_primality 6486735053 (2 : ZMod 6486735053)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 3), (19, 1), (248839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 3), (19, 1), (248839, 1)] : List FactorBlock).map factorBlockValue).prod) = 6486735053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_248839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6486735053) ^ 3243367526 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6486735053) ^ 926676436 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6486735053) ^ 341407108 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6486735053) ^ 26068 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_7556328173 : Nat.Prime 7556328173 := by
  apply lucas_primality 7556328173 (2 : ZMod 7556328173)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1889082043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1889082043, 1)] : List FactorBlock).map factorBlockValue).prod) = 7556328173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_1889082043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7556328173) ^ 3778164086 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7556328173) ^ 4 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_7725973261 : Nat.Prime 7725973261 := by
  apply lucas_primality 7725973261 (2 : ZMod 7725973261)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (223, 1), (577427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (223, 1), (577427, 1)] : List FactorBlock).map factorBlockValue).prod) = 7725973261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_223
      · exact prime_oneHundredEightDB_577427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7725973261) ^ 3862986630 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7725973261) ^ 2575324420 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7725973261) ^ 1545194652 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7725973261) ^ 34645620 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7725973261) ^ 13380 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_7847598419 : Nat.Prime 7847598419 := by
  apply lucas_primality 7847598419 (2 : ZMod 7847598419)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (12300311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (12300311, 1)] : List FactorBlock).map factorBlockValue).prod) = 7847598419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_12300311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7847598419) ^ 3923799209 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7847598419) ^ 713418038 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7847598419) ^ 270606842 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7847598419) ^ 638 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_10014130171 : Nat.Prime 10014130171 := by
  apply lucas_primality 10014130171 (11 : ZMod 10014130171)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (11, 1), (661, 1), (5101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (11, 1), (661, 1), (5101, 1)] : List FactorBlock).map factorBlockValue).prod) = 10014130171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_661
      · exact prime_oneHundredEightDB_5101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 10014130171) ^ 5007065085 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 10014130171) ^ 3338043390 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 10014130171) ^ 2002826034 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 10014130171) ^ 910375470 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 10014130171) ^ 15149970 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 10014130171) ^ 1963170 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_11440553653 : Nat.Prime 11440553653 := by
  apply lucas_primality 11440553653 (2 : ZMod 11440553653)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (263, 1), (109849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (263, 1), (109849, 1)] : List FactorBlock).map factorBlockValue).prod) = 11440553653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_263
      · exact prime_oneHundredEightDB_109849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11440553653) ^ 5720276826 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11440553653) ^ 3813517884 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11440553653) ^ 1040050332 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11440553653) ^ 43500204 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11440553653) ^ 104148 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_11809321819 : Nat.Prime 11809321819 := by
  apply lucas_primality 11809321819 (2 : ZMod 11809321819)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (109, 1), (2579581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (109, 1), (2579581, 1)] : List FactorBlock).map factorBlockValue).prod) = 11809321819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_109
      · exact prime_oneHundredEightDB_2579581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11809321819) ^ 5904660909 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11809321819) ^ 3936440606 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11809321819) ^ 1687045974 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11809321819) ^ 108342402 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11809321819) ^ 4578 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_11819515781 : Nat.Prime 11819515781 := by
  apply lucas_primality 11819515781 (2 : ZMod 11819515781)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (157, 1), (87539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (157, 1), (87539, 1)] : List FactorBlock).map factorBlockValue).prod) = 11819515781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_43
      · exact prime_oneHundredEightDB_157
      · exact prime_oneHundredEightDB_87539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11819515781) ^ 5909757890 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11819515781) ^ 2363903156 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11819515781) ^ 274872460 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11819515781) ^ 75283540 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11819515781) ^ 135020 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_12437760691 : Nat.Prime 12437760691 := by
  apply lucas_primality 12437760691 (10 : ZMod 12437760691)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (53, 1), (199, 1), (13103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (53, 1), (199, 1), (13103, 1)] : List FactorBlock).map factorBlockValue).prod) = 12437760691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_53
      · exact prime_oneHundredEightDB_199
      · exact prime_oneHundredEightDB_13103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 12437760691) ^ 6218880345 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 12437760691) ^ 4145920230 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 12437760691) ^ 2487552138 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 12437760691) ^ 234674730 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 12437760691) ^ 62501310 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 12437760691) ^ 949230 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_14820718709 : Nat.Prime 14820718709 := by
  apply lucas_primality 14820718709 (2 : ZMod 14820718709)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (1621, 1), (27539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (1621, 1), (27539, 1)] : List FactorBlock).map factorBlockValue).prod) = 14820718709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_83
      · exact prime_oneHundredEightDB_1621
      · exact prime_oneHundredEightDB_27539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14820718709) ^ 7410359354 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14820718709) ^ 178562876 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14820718709) ^ 9142948 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14820718709) ^ 538172 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_21561686411 : Nat.Prime 21561686411 := by
  apply lucas_primality 21561686411 (2 : ZMod 21561686411)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (196015331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (196015331, 1)] : List FactorBlock).map factorBlockValue).prod) = 21561686411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_196015331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21561686411) ^ 10780843205 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 21561686411) ^ 4312337282 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 21561686411) ^ 1960153310 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 21561686411) ^ 110 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_22639707263 : Nat.Prime 22639707263 := by
  apply lucas_primality 22639707263 (5 : ZMod 22639707263)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (41, 1), (61, 1), (443, 1), (601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (41, 1), (61, 1), (443, 1), (601, 1)] : List FactorBlock).map factorBlockValue).prod) = 22639707263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_41
      · exact prime_oneHundredEightDB_61
      · exact prime_oneHundredEightDB_443
      · exact prime_oneHundredEightDB_601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22639707263) ^ 11319853631 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 22639707263) ^ 1331747486 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 22639707263) ^ 552187982 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 22639707263) ^ 371142742 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 22639707263) ^ 51105434 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 22639707263) ^ 37670062 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_23046330287 : Nat.Prime 23046330287 := by
  apply lucas_primality 23046330287 (7 : ZMod 23046330287)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) = 23046330287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_173
      · exact prime_oneHundredEightDB_1583
      · exact prime_oneHundredEightDB_6011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23046330287) ^ 11523165143 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3292332898 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 133215782 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 14558642 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3834026 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_23093355541 : Nat.Prime 23093355541 := by
  apply lucas_primality 23093355541 (6 : ZMod 23093355541)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (43, 1), (8950913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (43, 1), (8950913, 1)] : List FactorBlock).map factorBlockValue).prod) = 23093355541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_43
      · exact prime_oneHundredEightDB_8950913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 23093355541) ^ 11546677770 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 23093355541) ^ 7697785180 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 23093355541) ^ 4618671108 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 23093355541) ^ 537054780 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 23093355541) ^ 2580 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_25790344861 : Nat.Prime 25790344861 := by
  apply lucas_primality 25790344861 (2 : ZMod 25790344861)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) = 25790344861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_61405583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25790344861) ^ 12895172430 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 8596781620 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 5158068972 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 3684334980 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 420 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_40563339811 : Nat.Prime 40563339811 := by
  apply lucas_primality 40563339811 (3 : ZMod 40563339811)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (8398207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (8398207, 1)] : List FactorBlock).map factorBlockValue).prod) = 40563339811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_8398207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40563339811) ^ 20281669905 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 40563339811) ^ 13521113270 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 40563339811) ^ 8112667962 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 40563339811) ^ 5794762830 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 40563339811) ^ 1763623470 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 40563339811) ^ 4830 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_49200684593 : Nat.Prime 49200684593 := by
  apply lucas_primality 49200684593 (3 : ZMod 49200684593)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (67, 1), (45896161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (67, 1), (45896161, 1)] : List FactorBlock).map factorBlockValue).prod) = 49200684593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_67
      · exact prime_oneHundredEightDB_45896161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 49200684593) ^ 24600342296 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 49200684593) ^ 734338576 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 49200684593) ^ 1072 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_52656538663 : Nat.Prime 52656538663 := by
  apply lucas_primality 52656538663 (3 : ZMod 52656538663)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (13, 1), (157, 1), (29251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (13, 1), (157, 1), (29251, 1)] : List FactorBlock).map factorBlockValue).prod) = 52656538663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_157
      · exact prime_oneHundredEightDB_29251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52656538663) ^ 26328269331 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52656538663) ^ 17552179554 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52656538663) ^ 7522362666 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52656538663) ^ 4050502974 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52656538663) ^ 335391966 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52656538663) ^ 1800162 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_108300455213 : Nat.Prime 108300455213 := by
  apply lucas_primality 108300455213 (2 : ZMod 108300455213)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (21323, 1), (55207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (21323, 1), (55207, 1)] : List FactorBlock).map factorBlockValue).prod) = 108300455213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_21323
      · exact prime_oneHundredEightDB_55207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 108300455213) ^ 54150227606 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 108300455213) ^ 4708715444 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 108300455213) ^ 5079044 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 108300455213) ^ 1961716 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_112854550019 : Nat.Prime 112854550019 := by
  apply lucas_primality 112854550019 (2 : ZMod 112854550019)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (23, 1), (50068567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (23, 1), (50068567, 1)] : List FactorBlock).map factorBlockValue).prod) = 112854550019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_50068567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 112854550019) ^ 56427275009 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 112854550019) ^ 16122078574 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 112854550019) ^ 4906719566 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 112854550019) ^ 2254 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_118138253869 : Nat.Prime 118138253869 := by
  apply lucas_primality 118138253869 (2 : ZMod 118138253869)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (29, 2), (1300681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (29, 2), (1300681, 1)] : List FactorBlock).map factorBlockValue).prod) = 118138253869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_1300681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 118138253869) ^ 59069126934 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 118138253869) ^ 39379417956 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 118138253869) ^ 4073732892 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 118138253869) ^ 90828 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_148945151149 : Nat.Prime 148945151149 := by
  apply lucas_primality 148945151149 (2 : ZMod 148945151149)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (223, 1), (1069, 1), (52067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (223, 1), (1069, 1), (52067, 1)] : List FactorBlock).map factorBlockValue).prod) = 148945151149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_223
      · exact prime_oneHundredEightDB_1069
      · exact prime_oneHundredEightDB_52067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 148945151149) ^ 74472575574 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 148945151149) ^ 49648383716 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 148945151149) ^ 667915476 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 148945151149) ^ 139331292 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 148945151149) ^ 2860644 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_156219162989 : Nat.Prime 156219162989 := by
  apply lucas_primality 156219162989 (2 : ZMod 156219162989)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (5579255821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (5579255821, 1)] : List FactorBlock).map factorBlockValue).prod) = 156219162989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_5579255821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 156219162989) ^ 78109581494 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 156219162989) ^ 22317023284 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 156219162989) ^ 28 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_157705373099 : Nat.Prime 157705373099 := by
  apply lucas_primality 157705373099 (2 : ZMod 157705373099)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13, 1), (71, 1), (1743487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13, 1), (71, 1), (1743487, 1)] : List FactorBlock).map factorBlockValue).prod) = 157705373099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_71
      · exact prime_oneHundredEightDB_1743487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 157705373099) ^ 78852686549 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 22529339014 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 12131182546 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 2221202438 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 90454 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_177602339353 : Nat.Prime 177602339353 := by
  apply lucas_primality 177602339353 (5 : ZMod 177602339353)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (163, 1), (45399371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (163, 1), (45399371, 1)] : List FactorBlock).map factorBlockValue).prod) = 177602339353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_163
      · exact prime_oneHundredEightDB_45399371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 177602339353) ^ 88801169676 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 177602339353) ^ 59200779784 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 177602339353) ^ 1089584904 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 177602339353) ^ 3912 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_184344882637 : Nat.Prime 184344882637 := by
  apply lucas_primality 184344882637 (2 : ZMod 184344882637)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (808530187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (808530187, 1)] : List FactorBlock).map factorBlockValue).prod) = 184344882637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_808530187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 184344882637) ^ 92172441318 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 184344882637) ^ 61448294212 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 184344882637) ^ 9702362244 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 184344882637) ^ 228 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_238024728587 : Nat.Prime 238024728587 := by
  apply lucas_primality 238024728587 (5 : ZMod 238024728587)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (71, 1), (137, 1), (643961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (71, 1), (137, 1), (643961, 1)] : List FactorBlock).map factorBlockValue).prod) = 238024728587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_71
      · exact prime_oneHundredEightDB_137
      · exact prime_oneHundredEightDB_643961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 238024728587) ^ 119012364293 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 12527617294 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 3352460966 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 1737406778 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 369626 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_323947351769 : Nat.Prime 323947351769 := by
  apply lucas_primality 323947351769 (3 : ZMod 323947351769)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2803, 1), (14446457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2803, 1), (14446457, 1)] : List FactorBlock).map factorBlockValue).prod) = 323947351769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_2803
      · exact prime_oneHundredEightDB_14446457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 323947351769) ^ 161973675884 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 323947351769) ^ 115571656 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 323947351769) ^ 22424 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_414808869521 : Nat.Prime 414808869521 := by
  apply lucas_primality 414808869521 (6 : ZMod 414808869521)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (23, 1), (131, 1), (461, 1), (3733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (23, 1), (131, 1), (461, 1), (3733, 1)] : List FactorBlock).map factorBlockValue).prod) = 414808869521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_131
      · exact prime_oneHundredEightDB_461
      · exact prime_oneHundredEightDB_3733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 414808869521) ^ 207404434760 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 414808869521) ^ 82961773904 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 414808869521) ^ 18035168240 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 414808869521) ^ 3166479920 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 414808869521) ^ 899802320 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 414808869521) ^ 111119440 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_554082697409 : Nat.Prime 554082697409 := by
  apply lucas_primality 554082697409 (3 : ZMod 554082697409)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (19, 1), (3271, 1), (139303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (19, 1), (3271, 1), (139303, 1)] : List FactorBlock).map factorBlockValue).prod) = 554082697409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_3271
      · exact prime_oneHundredEightDB_139303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 554082697409) ^ 277041348704 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 554082697409) ^ 29162247232 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 554082697409) ^ 169392448 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 554082697409) ^ 3977536 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_749523766273 : Nat.Prime 749523766273 := by
  apply lucas_primality 749523766273 (5 : ZMod 749523766273)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) = 749523766273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_821
      · exact prime_oneHundredEightDB_6323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 749523766273) ^ 374761883136 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 249841255424 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 15947314176 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 912940032 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 118539264 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_815029461469 : Nat.Prime 815029461469 := by
  apply lucas_primality 815029461469 (6 : ZMod 815029461469)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (22639707263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (22639707263, 1)] : List FactorBlock).map factorBlockValue).prod) = 815029461469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_22639707263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 815029461469) ^ 407514730734 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 815029461469) ^ 271676487156 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 815029461469) ^ 36 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_829617739043 : Nat.Prime 829617739043 := by
  apply lucas_primality 829617739043 (2 : ZMod 829617739043)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (414808869521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (414808869521, 1)] : List FactorBlock).map factorBlockValue).prod) = 829617739043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_414808869521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 829617739043) ^ 414808869521 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 829617739043) ^ 2 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1113669885941 : Nat.Prime 1113669885941 := by
  apply lucas_primality 1113669885941 (2 : ZMod 1113669885941)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (127, 1), (1279, 1), (11821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (127, 1), (1279, 1), (11821, 1)] : List FactorBlock).map factorBlockValue).prod) = 1113669885941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_127
      · exact prime_oneHundredEightDB_1279
      · exact prime_oneHundredEightDB_11821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1113669885941) ^ 556834942970 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113669885941) ^ 222733977188 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113669885941) ^ 38402409860 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113669885941) ^ 8769054220 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113669885941) ^ 870734860 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113669885941) ^ 94211140 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1236816770621 : Nat.Prime 1236816770621 := by
  apply lucas_primality 1236816770621 (2 : ZMod 1236816770621)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (347, 1), (178215673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (347, 1), (178215673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1236816770621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_347
      · exact prime_oneHundredEightDB_178215673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1236816770621) ^ 618408385310 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1236816770621) ^ 247363354124 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1236816770621) ^ 3564313460 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1236816770621) ^ 6940 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1476020537791 : Nat.Prime 1476020537791 := by
  apply lucas_primality 1476020537791 (3 : ZMod 1476020537791)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (49200684593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (49200684593, 1)] : List FactorBlock).map factorBlockValue).prod) = 1476020537791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_49200684593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1476020537791) ^ 738010268895 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1476020537791) ^ 492006845930 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1476020537791) ^ 295204107558 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1476020537791) ^ 30 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1491301720847 : Nat.Prime 1491301720847 := by
  apply lucas_primality 1491301720847 (7 : ZMod 1491301720847)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (6265973617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (6265973617, 1)] : List FactorBlock).map factorBlockValue).prod) = 1491301720847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_6265973617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1491301720847) ^ 745650860423 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1491301720847) ^ 213043102978 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1491301720847) ^ 87723630638 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1491301720847) ^ 238 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1619759629171 : Nat.Prime 1619759629171 := by
  apply lucas_primality 1619759629171 (3 : ZMod 1619759629171)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (8311, 1), (2165483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (8311, 1), (2165483, 1)] : List FactorBlock).map factorBlockValue).prod) = 1619759629171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_8311
      · exact prime_oneHundredEightDB_2165483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1619759629171) ^ 809879814585 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1619759629171) ^ 539919876390 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1619759629171) ^ 323951925834 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1619759629171) ^ 194893470 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1619759629171) ^ 747990 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1703660272063 : Nat.Prime 1703660272063 := by
  apply lucas_primality 1703660272063 (5 : ZMod 1703660272063)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (40563339811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (40563339811, 1)] : List FactorBlock).map factorBlockValue).prod) = 1703660272063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_40563339811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1703660272063) ^ 851830136031 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1703660272063) ^ 567886757354 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1703660272063) ^ 243380038866 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1703660272063) ^ 42 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2517652494991 : Nat.Prime 2517652494991 := by
  apply lucas_primality 2517652494991 (3 : ZMod 2517652494991)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (107, 1), (4993, 1), (52361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (107, 1), (4993, 1), (52361, 1)] : List FactorBlock).map factorBlockValue).prod) = 2517652494991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_107
      · exact prime_oneHundredEightDB_4993
      · exact prime_oneHundredEightDB_52361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2517652494991) ^ 1258826247495 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 839217498330 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 503530498998 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 23529462570 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 504236430 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 48082590 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_3501634450421 : Nat.Prime 3501634450421 := by
  apply lucas_primality 3501634450421 (2 : ZMod 3501634450421)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (15091, 1), (11601731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (15091, 1), (11601731, 1)] : List FactorBlock).map factorBlockValue).prod) = 3501634450421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_15091
      · exact prime_oneHundredEightDB_11601731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3501634450421) ^ 1750817225210 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3501634450421) ^ 700326890084 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3501634450421) ^ 232034620 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3501634450421) ^ 301820 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_3662228970263 : Nat.Prime 3662228970263 := by
  apply lucas_primality 3662228970263 (5 : ZMod 3662228970263)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3662228970263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_71
      · exact prime_oneHundredEightDB_25790344861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3662228970263) ^ 1831114485131 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 51580689722 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 142 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_3687111941479 : Nat.Prime 3687111941479 := by
  apply lucas_primality 3687111941479 (3 : ZMod 3687111941479)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3687111941479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_37
      · exact prime_oneHundredEightDB_139568171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3687111941479) ^ 1843555970739 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 1229037313826 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 526730277354 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 216888937734 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 99651674094 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 26418 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_3797081613103 : Nat.Prime 3797081613103 := by
  apply lucas_primality 3797081613103 (5 : ZMod 3797081613103)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (733813, 1), (862409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (733813, 1), (862409, 1)] : List FactorBlock).map factorBlockValue).prod) = 3797081613103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_733813
      · exact prime_oneHundredEightDB_862409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3797081613103) ^ 1898540806551 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3797081613103) ^ 1265693871034 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3797081613103) ^ 5174454 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3797081613103) ^ 4402878 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_4014078193691 : Nat.Prime 4014078193691 := by
  apply lucas_primality 4014078193691 (2 : ZMod 4014078193691)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) = 4014078193691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_829
      · exact prime_oneHundredEightDB_1051
      · exact prime_oneHundredEightDB_460711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4014078193691) ^ 2007039096845 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 802815638738 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 4842072610 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 3819294190 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 8712790 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_4147273733311 : Nat.Prime 4147273733311 := by
  apply lucas_primality 4147273733311 (3 : ZMod 4147273733311)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (8209, 1), (330203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (8209, 1), (330203, 1)] : List FactorBlock).map factorBlockValue).prod) = 4147273733311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_8209
      · exact prime_oneHundredEightDB_330203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4147273733311) ^ 2073636866655 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4147273733311) ^ 1382424577770 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4147273733311) ^ 829454746662 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4147273733311) ^ 243957278430 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4147273733311) ^ 505210590 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4147273733311) ^ 12559770 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_7104093574121 : Nat.Prime 7104093574121 := by
  apply lucas_primality 7104093574121 (3 : ZMod 7104093574121)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (177602339353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (177602339353, 1)] : List FactorBlock).map factorBlockValue).prod) = 7104093574121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_177602339353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7104093574121) ^ 3552046787060 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7104093574121) ^ 1420818714824 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7104093574121) ^ 40 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_8548463135521 : Nat.Prime 8548463135521 := by
  apply lucas_primality 8548463135521 (31 : ZMod 8548463135521)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 6), (5, 1), (7, 1), (11, 1), (23, 1), (29, 1), (1427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 6), (5, 1), (7, 1), (11, 1), (23, 1), (29, 1), (1427, 1)] : List FactorBlock).map factorBlockValue).prod) = 8548463135521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_1427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 8548463135521) ^ 4274231567760 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (31 : ZMod 8548463135521) ^ 2849487711840 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (31 : ZMod 8548463135521) ^ 1709692627104 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (31 : ZMod 8548463135521) ^ 1221209019360 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (31 : ZMod 8548463135521) ^ 777133012320 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (31 : ZMod 8548463135521) ^ 371672310240 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (31 : ZMod 8548463135521) ^ 294774590880 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (31 : ZMod 8548463135521) ^ 5990513760 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_11013696930283 : Nat.Prime 11013696930283 := by
  apply lucas_primality 11013696930283 (5 : ZMod 11013696930283)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (347, 1), (23929, 1), (221069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (347, 1), (23929, 1), (221069, 1)] : List FactorBlock).map factorBlockValue).prod) = 11013696930283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_347
      · exact prime_oneHundredEightDB_23929
      · exact prime_oneHundredEightDB_221069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11013696930283) ^ 5506848465141 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 3671232310094 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 31739760606 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 460265658 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 49820178 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_11446482564799 : Nat.Prime 11446482564799 := by
  apply lucas_primality 11446482564799 (7 : ZMod 11446482564799)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (463, 1), (937, 1), (141853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (463, 1), (937, 1), (141853, 1)] : List FactorBlock).map factorBlockValue).prod) = 11446482564799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_31
      · exact prime_oneHundredEightDB_463
      · exact prime_oneHundredEightDB_937
      · exact prime_oneHundredEightDB_141853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11446482564799) ^ 5723241282399 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 11446482564799) ^ 3815494188266 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 11446482564799) ^ 369241373058 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 11446482564799) ^ 24722424546 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 11446482564799) ^ 12216096654 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 11446482564799) ^ 80692566 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_11765675112199 : Nat.Prime 11765675112199 := by
  apply lucas_primality 11765675112199 (3 : ZMod 11765675112199)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (9901, 1), (28293619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (9901, 1), (28293619, 1)] : List FactorBlock).map factorBlockValue).prod) = 11765675112199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_9901
      · exact prime_oneHundredEightDB_28293619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11765675112199) ^ 5882837556099 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11765675112199) ^ 3921891704066 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11765675112199) ^ 1680810730314 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11765675112199) ^ 1188331998 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11765675112199) ^ 415842 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_12552271877179 : Nat.Prime 12552271877179 := by
  apply lucas_primality 12552271877179 (3 : ZMod 12552271877179)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (29, 2), (31, 1), (810547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (29, 2), (31, 1), (810547, 1)] : List FactorBlock).map factorBlockValue).prod) = 12552271877179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_31
      · exact prime_oneHundredEightDB_810547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12552271877179) ^ 6276135938589 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 12552271877179) ^ 4184090625726 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 12552271877179) ^ 1141115625198 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 12552271877179) ^ 432836961282 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 12552271877179) ^ 404911996038 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 12552271877179) ^ 15486174 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_13971226936099 : Nat.Prime 13971226936099 := by
  apply lucas_primality 13971226936099 (2 : ZMod 13971226936099)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13971226936099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_21617
      · exact prime_oneHundredEightDB_6336347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13971226936099) ^ 6985613468049 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 4657075645366 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 821836878594 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 646307394 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 2204934 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_14010211080413 : Nat.Prime 14010211080413 := by
  apply lucas_primality 14010211080413 (3 : ZMod 14010211080413)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (184344882637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (184344882637, 1)] : List FactorBlock).map factorBlockValue).prod) = 14010211080413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_184344882637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14010211080413) ^ 7005105540206 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 14010211080413) ^ 737379530548 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 14010211080413) ^ 76 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_14305552217941 : Nat.Prime 14305552217941 := by
  apply lucas_primality 14305552217941 (2 : ZMod 14305552217941)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) = 14305552217941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_6427
      · exact prime_oneHundredEightDB_37097537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14305552217941) ^ 7152776108970 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 4768517405980 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2861110443588 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2225852220 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 385620 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_20902081382297 : Nat.Prime 20902081382297 := by
  apply lucas_primality 20902081382297 (3 : ZMod 20902081382297)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1579, 1), (4423, 1), (374111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1579, 1), (4423, 1), (374111, 1)] : List FactorBlock).map factorBlockValue).prod) = 20902081382297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_1579
      · exact prime_oneHundredEightDB_4423
      · exact prime_oneHundredEightDB_374111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20902081382297) ^ 10451040691148 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20902081382297) ^ 13237543624 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20902081382297) ^ 4725770152 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20902081382297) ^ 55871336 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_23580678731417 : Nat.Prime 23580678731417 := by
  apply lucas_primality 23580678731417 (3 : ZMod 23580678731417)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (288689, 1), (10210243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (288689, 1), (10210243, 1)] : List FactorBlock).map factorBlockValue).prod) = 23580678731417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_288689
      · exact prime_oneHundredEightDB_10210243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 23580678731417) ^ 11790339365708 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23580678731417) ^ 81681944 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23580678731417) ^ 2309512 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_26851715585323 : Nat.Prime 26851715585323 := by
  apply lucas_primality 26851715585323 (2 : ZMod 26851715585323)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (89, 1), (24337, 1), (89833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (89, 1), (24337, 1), (89833, 1)] : List FactorBlock).map factorBlockValue).prod) = 26851715585323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_89
      · exact prime_oneHundredEightDB_24337
      · exact prime_oneHundredEightDB_89833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26851715585323) ^ 13425857792661 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 8950571861774 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 1167465895014 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 301704669498 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 1103328906 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 298907034 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_28020422160827 : Nat.Prime 28020422160827 := by
  apply lucas_primality 28020422160827 (2 : ZMod 28020422160827)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14010211080413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14010211080413, 1)] : List FactorBlock).map factorBlockValue).prod) = 28020422160827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_14010211080413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 28020422160827) ^ 14010211080413 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 28020422160827) ^ 2 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_46241910707801 : Nat.Prime 46241910707801 := by
  apply lucas_primality 46241910707801 (3 : ZMod 46241910707801)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (571, 1), (404920409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (571, 1), (404920409, 1)] : List FactorBlock).map factorBlockValue).prod) = 46241910707801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_571
      · exact prime_oneHundredEightDB_404920409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 46241910707801) ^ 23120955353900 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 46241910707801) ^ 9248382141560 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 46241910707801) ^ 80984081800 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 46241910707801) ^ 114200 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_55463448789821 : Nat.Prime 55463448789821 := by
  apply lucas_primality 55463448789821 (2 : ZMod 55463448789821)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (367, 1), (7556328173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (367, 1), (7556328173, 1)] : List FactorBlock).map factorBlockValue).prod) = 55463448789821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_367
      · exact prime_oneHundredEightDB_7556328173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55463448789821) ^ 27731724394910 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55463448789821) ^ 11092689757964 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55463448789821) ^ 151126563460 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55463448789821) ^ 7340 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_110926897579643 : Nat.Prime 110926897579643 := by
  apply lucas_primality 110926897579643 (2 : ZMod 110926897579643)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (55463448789821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (55463448789821, 1)] : List FactorBlock).map factorBlockValue).prod) = 110926897579643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_55463448789821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 110926897579643) ^ 55463448789821 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 110926897579643) ^ 2 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_113993486613649 : Nat.Prime 113993486613649 := by
  apply lucas_primality 113993486613649 (7 : ZMod 113993486613649)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) = 113993486613649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_317
      · exact prime_oneHundredEightDB_131433079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 113993486613649) ^ 56996743306824 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 37997828871216 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 5999657190192 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 359600904144 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 867312 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_123920774345411 : Nat.Prime 123920774345411 := by
  apply lucas_primality 123920774345411 (2 : ZMod 123920774345411)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (433, 1), (4088445211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (433, 1), (4088445211, 1)] : List FactorBlock).map factorBlockValue).prod) = 123920774345411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_433
      · exact prime_oneHundredEightDB_4088445211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 123920774345411) ^ 61960387172705 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 123920774345411) ^ 24784154869082 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 123920774345411) ^ 17702967763630 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 123920774345411) ^ 286191164770 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 123920774345411) ^ 30310 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_124975823753281 : Nat.Prime 124975823753281 := by
  apply lucas_primality 124975823753281 (11 : ZMod 124975823753281)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (287387, 1), (452989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (287387, 1), (452989, 1)] : List FactorBlock).map factorBlockValue).prod) = 124975823753281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_287387
      · exact prime_oneHundredEightDB_452989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 124975823753281) ^ 62487911876640 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 124975823753281) ^ 41658607917760 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 124975823753281) ^ 24995164750656 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 124975823753281) ^ 434869440 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 124975823753281) ^ 275891520 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_130417135331503 : Nat.Prime 130417135331503 := by
  apply lucas_primality 130417135331503 (3 : ZMod 130417135331503)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) = 130417135331503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_749523766273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 130417135331503) ^ 65208567665751 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 43472378443834 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 4497142597638 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 174 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_148631737990633 : Nat.Prime 148631737990633 := by
  apply lucas_primality 148631737990633 (10 : ZMod 148631737990633)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (47, 1), (691, 1), (14668343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (47, 1), (691, 1), (14668343, 1)] : List FactorBlock).map factorBlockValue).prod) = 148631737990633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_691
      · exact prime_oneHundredEightDB_14668343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 148631737990633) ^ 74315868995316 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 49543912663544 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 11433210614664 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 3162377404056 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 215096581752 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 10132824 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_177146449272173 : Nat.Prime 177146449272173 := by
  apply lucas_primality 177146449272173 (2 : ZMod 177146449272173)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (4421, 1), (189006211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (4421, 1), (189006211, 1)] : List FactorBlock).map factorBlockValue).prod) = 177146449272173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_53
      · exact prime_oneHundredEightDB_4421
      · exact prime_oneHundredEightDB_189006211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 177146449272173) ^ 88573224636086 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 177146449272173) ^ 3342385835324 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 177146449272173) ^ 40069316732 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 177146449272173) ^ 937252 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_240844691621461 : Nat.Prime 240844691621461 := by
  apply lucas_primality 240844691621461 (2 : ZMod 240844691621461)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) = 240844691621461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_4014078193691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240844691621461) ^ 120422345810730 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 80281563873820 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 48168938324292 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 60 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_247132914945517 : Nat.Prime 247132914945517 := by
  apply lucas_primality 247132914945517 (2 : ZMod 247132914945517)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (2861, 1), (799813957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (2861, 1), (799813957, 1)] : List FactorBlock).map factorBlockValue).prod) = 247132914945517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_2861
      · exact prime_oneHundredEightDB_799813957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 247132914945517) ^ 123566457472758 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 247132914945517) ^ 82377638315172 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 247132914945517) ^ 86379907356 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 247132914945517) ^ 308988 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_10789
      · exact prime_oneHundredEightDB_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_487995060087097 : Nat.Prime 487995060087097 := by
  apply lucas_primality 487995060087097 (5 : ZMod 487995060087097)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2591, 1), (7847598419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2591, 1), (7847598419, 1)] : List FactorBlock).map factorBlockValue).prod) = 487995060087097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_2591
      · exact prime_oneHundredEightDB_7847598419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 487995060087097) ^ 243997530043548 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 487995060087097) ^ 162665020029032 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 487995060087097) ^ 188342362056 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 487995060087097) ^ 62184 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_729992287516259 : Nat.Prime 729992287516259 := by
  apply lucas_primality 729992287516259 (2 : ZMod 729992287516259)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (19, 1), (2063, 1), (42135017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (19, 1), (2063, 1), (42135017, 1)] : List FactorBlock).map factorBlockValue).prod) = 729992287516259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_2063
      · exact prime_oneHundredEightDB_42135017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 729992287516259) ^ 364996143758129 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 729992287516259) ^ 56153252885866 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 729992287516259) ^ 42940722795074 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 729992287516259) ^ 38420646711382 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 729992287516259) ^ 353849872766 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 729992287516259) ^ 17325074 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_829722028640579 : Nat.Prime 829722028640579 := by
  apply lucas_primality 829722028640579 (2 : ZMod 829722028640579)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) = 829722028640579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_14305552217941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 829722028640579) ^ 414861014320289 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 28611104435882 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 58 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_991366194763289 : Nat.Prime 991366194763289 := by
  apply lucas_primality 991366194763289 (3 : ZMod 991366194763289)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (123920774345411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (123920774345411, 1)] : List FactorBlock).map factorBlockValue).prod) = 991366194763289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_123920774345411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 991366194763289) ^ 495683097381644 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 991366194763289) ^ 8 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1222420807213043 : Nat.Prime 1222420807213043 := by
  apply lucas_primality 1222420807213043 (5 : ZMod 1222420807213043)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (641, 1), (4092387857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (641, 1), (4092387857, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222420807213043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_233
      · exact prime_oneHundredEightDB_641
      · exact prime_oneHundredEightDB_4092387857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1222420807213043) ^ 611210403606521 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1222420807213043) ^ 5246441232674 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1222420807213043) ^ 1907052741362 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1222420807213043) ^ 298706 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1310054122227563 : Nat.Prime 1310054122227563 := by
  apply lucas_primality 1310054122227563 (2 : ZMod 1310054122227563)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5981, 1), (59011, 1), (1855891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5981, 1), (59011, 1), (1855891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1310054122227563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5981
      · exact prime_oneHundredEightDB_59011
      · exact prime_oneHundredEightDB_1855891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1310054122227563) ^ 655027061113781 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1310054122227563) ^ 219035967602 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1310054122227563) ^ 22200168142 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1310054122227563) ^ 705889582 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1353881570594633 : Nat.Prime 1353881570594633 := by
  apply lucas_primality 1353881570594633 (3 : ZMod 1353881570594633)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2381, 1), (2801, 1), (25375709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2381, 1), (2801, 1), (25375709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1353881570594633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_2381
      · exact prime_oneHundredEightDB_2801
      · exact prime_oneHundredEightDB_25375709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1353881570594633) ^ 676940785297316 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1353881570594633) ^ 568618887272 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1353881570594633) ^ 483356505032 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1353881570594633) ^ 53353448 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1452722104942727 : Nat.Prime 1452722104942727 := by
  apply lucas_primality 1452722104942727 (5 : ZMod 1452722104942727)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1452722104942727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_197
      · exact prime_oneHundredEightDB_3687111941479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1452722104942727) ^ 726361052471363 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 7374223882958 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 394 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1552976566115003 : Nat.Prime 1552976566115003 := by
  apply lucas_primality 1552976566115003 (2 : ZMod 1552976566115003)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (110926897579643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (110926897579643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1552976566115003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_110926897579643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1552976566115003) ^ 776488283057501 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1552976566115003) ^ 221853795159286 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1552976566115003) ^ 14 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1757371080014899 : Nat.Prime 1757371080014899 := by
  apply lucas_primality 1757371080014899 (3 : ZMod 1757371080014899)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (263, 1), (1113669885941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (263, 1), (1113669885941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1757371080014899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_263
      · exact prime_oneHundredEightDB_1113669885941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1757371080014899) ^ 878685540007449 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1757371080014899) ^ 585790360004966 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1757371080014899) ^ 6682019315646 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1757371080014899) ^ 1578 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1928207786983321 : Nat.Prime 1928207786983321 := by
  apply lucas_primality 1928207786983321 (11 : ZMod 1928207786983321)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (29, 1), (554082697409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (29, 1), (554082697409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1928207786983321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_554082697409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1928207786983321) ^ 964103893491660 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1928207786983321) ^ 642735928994440 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1928207786983321) ^ 385641557396664 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1928207786983321) ^ 66489923689080 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1928207786983321) ^ 3480 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2164499678281279 : Nat.Prime 2164499678281279 := by
  apply lucas_primality 2164499678281279 (11 : ZMod 2164499678281279)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (31, 1), (52656538663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (31, 1), (52656538663, 1)] : List FactorBlock).map factorBlockValue).prod) = 2164499678281279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_31
      · exact prime_oneHundredEightDB_52656538663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2164499678281279) ^ 1082249839140639 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2164499678281279) ^ 721499892760426 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2164499678281279) ^ 166499975252406 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2164499678281279) ^ 127323510487134 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2164499678281279) ^ 69822570267138 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2164499678281279) ^ 41106 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2471329149455171 : Nat.Prime 2471329149455171 := by
  apply lucas_primality 2471329149455171 (6 : ZMod 2471329149455171)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (247132914945517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (247132914945517, 1)] : List FactorBlock).map factorBlockValue).prod) = 2471329149455171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_247132914945517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 2471329149455171) ^ 1235664574727585 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 2471329149455171) ^ 494265829891034 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 2471329149455171) ^ 10 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2819741595528049 : Nat.Prime 2819741595528049 := by
  apply lucas_primality 2819741595528049 (14 : ZMod 2819741595528049)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (151, 1), (16139, 1), (831221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (151, 1), (16139, 1), (831221, 1)] : List FactorBlock).map factorBlockValue).prod) = 2819741595528049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_151
      · exact prime_oneHundredEightDB_16139
      · exact prime_oneHundredEightDB_831221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2819741595528049) ^ 1409870797764024 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 2819741595528049) ^ 939913865176016 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 2819741595528049) ^ 97232468811312 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 2819741595528049) ^ 18673785400848 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 2819741595528049) ^ 174716004432 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 2819741595528049) ^ 3392288688 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_4455926248468213 : Nat.Prime 4455926248468213 := by
  apply lucas_primality 4455926248468213 (2 : ZMod 4455926248468213)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (23, 1), (67, 1), (157, 1), (1373, 1), (53231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (23, 1), (67, 1), (157, 1), (1373, 1), (53231, 1)] : List FactorBlock).map factorBlockValue).prod) = 4455926248468213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_67
      · exact prime_oneHundredEightDB_157
      · exact prime_oneHundredEightDB_1373
      · exact prime_oneHundredEightDB_53231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4455926248468213) ^ 2227963124234106 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4455926248468213) ^ 1485308749489404 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4455926248468213) ^ 636560892638316 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4455926248468213) ^ 193735923846444 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4455926248468213) ^ 66506361917436 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4455926248468213) ^ 28381695850116 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4455926248468213) ^ 3245394208644 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4455926248468213) ^ 83709234252 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_4531707249364499 : Nat.Prime 4531707249364499 := by
  apply lucas_primality 4531707249364499 (2 : ZMod 4531707249364499)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (46241910707801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (46241910707801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4531707249364499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_46241910707801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4531707249364499) ^ 2265853624682249 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4531707249364499) ^ 647386749909214 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4531707249364499) ^ 98 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_4531774490983801 : Nat.Prime 4531774490983801 := by
  apply lucas_primality 4531774490983801 (7 : ZMod 4531774490983801)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (2517652494991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (2517652494991, 1)] : List FactorBlock).map factorBlockValue).prod) = 4531774490983801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_2517652494991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4531774490983801) ^ 2265887245491900 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 4531774490983801) ^ 1510591496994600 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 4531774490983801) ^ 906354898196760 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 4531774490983801) ^ 1800 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_6102026044398121 : Nat.Prime 6102026044398121 := by
  apply lucas_primality 6102026044398121 (7 : ZMod 6102026044398121)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (53791, 1), (945329461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (53791, 1), (945329461, 1)] : List FactorBlock).map factorBlockValue).prod) = 6102026044398121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_53791
      · exact prime_oneHundredEightDB_945329461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6102026044398121) ^ 3051013022199060 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 2034008681466040 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 1220405208879624 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 113439535320 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 6454920 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_10391732455352099 : Nat.Prime 10391732455352099 := by
  apply lucas_primality 10391732455352099 (2 : ZMod 10391732455352099)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (181, 1), (11789, 1), (6227671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (181, 1), (11789, 1), (6227671, 1)] : List FactorBlock).map factorBlockValue).prod) = 10391732455352099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_181
      · exact prime_oneHundredEightDB_11789
      · exact prime_oneHundredEightDB_6227671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10391732455352099) ^ 5195866227676049 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10391732455352099) ^ 611278379726594 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10391732455352099) ^ 451814454580526 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10391732455352099) ^ 57412886493658 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10391732455352099) ^ 881477008682 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10391732455352099) ^ 1668638638 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_10852315933041311 : Nat.Prime 10852315933041311 := by
  apply lucas_primality 10852315933041311 (7 : ZMod 10852315933041311)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (13, 1), (1703660272063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (13, 1), (1703660272063, 1)] : List FactorBlock).map factorBlockValue).prod) = 10852315933041311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_1703660272063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10852315933041311) ^ 5426157966520655 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 10852315933041311) ^ 2170463186608262 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 10852315933041311) ^ 1550330847577330 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 10852315933041311) ^ 834793533310870 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 10852315933041311) ^ 6370 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_17573710800148991 : Nat.Prime 17573710800148991 := by
  apply lucas_primality 17573710800148991 (11 : ZMod 17573710800148991)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1757371080014899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1757371080014899, 1)] : List FactorBlock).map factorBlockValue).prod) = 17573710800148991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_1757371080014899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 17573710800148991) ^ 8786855400074495 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 17573710800148991) ^ 3514742160029798 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 17573710800148991) ^ 10 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_27609957665089577 : Nat.Prime 27609957665089577 := by
  apply lucas_primality 27609957665089577 (3 : ZMod 27609957665089577)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (29, 1), (37, 1), (73, 1), (661, 1), (9522559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (29, 1), (37, 1), (73, 1), (661, 1), (9522559, 1)] : List FactorBlock).map factorBlockValue).prod) = 27609957665089577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_37
      · exact prime_oneHundredEightDB_73
      · exact prime_oneHundredEightDB_661
      · exact prime_oneHundredEightDB_9522559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27609957665089577) ^ 13804978832544788 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27609957665089577) ^ 3944279666441368 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27609957665089577) ^ 952067505692744 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27609957665089577) ^ 746215072029448 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27609957665089577) ^ 378218598151912 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27609957665089577) ^ 41769981339016 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27609957665089577) ^ 2899426264 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_38515360242221347 : Nat.Prime 38515360242221347 := by
  apply lucas_primality 38515360242221347 (2 : ZMod 38515360242221347)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (463, 1), (601, 1), (2097174487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (463, 1), (601, 1), (2097174487, 1)] : List FactorBlock).map factorBlockValue).prod) = 38515360242221347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_463
      · exact prime_oneHundredEightDB_601
      · exact prime_oneHundredEightDB_2097174487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38515360242221347) ^ 19257680121110673 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38515360242221347) ^ 12838453414073782 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38515360242221347) ^ 3501396385656486 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38515360242221347) ^ 83186523201342 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38515360242221347) ^ 64085457973746 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38515360242221347) ^ 18365358 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_40377390718990079 : Nat.Prime 40377390718990079 := by
  apply lucas_primality 40377390718990079 (17 : ZMod 40377390718990079)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1552976566115003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1552976566115003, 1)] : List FactorBlock).map factorBlockValue).prod) = 40377390718990079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_1552976566115003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 40377390718990079) ^ 20188695359495039 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 40377390718990079) ^ 3105953132230006 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 40377390718990079) ^ 26 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_222276424781035217 : Nat.Prime 222276424781035217 := by
  apply lucas_primality 222276424781035217 (3 : ZMod 222276424781035217)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (7129, 1), (19237, 1), (3267727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (7129, 1), (19237, 1), (3267727, 1)] : List FactorBlock).map factorBlockValue).prod) = 222276424781035217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_31
      · exact prime_oneHundredEightDB_7129
      · exact prime_oneHundredEightDB_19237
      · exact prime_oneHundredEightDB_3267727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 222276424781035217) ^ 111138212390517608 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 222276424781035217) ^ 7170207251001136 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 222276424781035217) ^ 31179187092304 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 222276424781035217) ^ 11554630388368 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 222276424781035217) ^ 68021724208 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_411776985049921223 : Nat.Prime 411776985049921223 := by
  apply lucas_primality 411776985049921223 (5 : ZMod 411776985049921223)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (402645769, 1), (511339019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (402645769, 1), (511339019, 1)] : List FactorBlock).map factorBlockValue).prod) = 411776985049921223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_402645769
      · exact prime_oneHundredEightDB_511339019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 411776985049921223) ^ 205888492524960611 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 411776985049921223) ^ 1022678038 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 411776985049921223) ^ 805291538 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_419996061740133023 : Nat.Prime 419996061740133023 := by
  apply lucas_primality 419996061740133023 (5 : ZMod 419996061740133023)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (882253, 1), (238024728587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (882253, 1), (238024728587, 1)] : List FactorBlock).map factorBlockValue).prod) = 419996061740133023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_882253
      · exact prime_oneHundredEightDB_238024728587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 419996061740133023) ^ 209998030870066511 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 419996061740133023) ^ 476049457174 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 419996061740133023) ^ 1764506 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_618877695587683109 : Nat.Prime 618877695587683109 := by
  apply lucas_primality 618877695587683109 (2 : ZMod 618877695587683109)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (367, 1), (19141, 1), (202063399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (367, 1), (19141, 1), (202063399, 1)] : List FactorBlock).map factorBlockValue).prod) = 618877695587683109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_109
      · exact prime_oneHundredEightDB_367
      · exact prime_oneHundredEightDB_19141
      · exact prime_oneHundredEightDB_202063399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 618877695587683109) ^ 309438847793841554 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 5677777023740212 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 1686315246832924 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 32332568600788 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 3062789692 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_872002404010526741 : Nat.Prime 872002404010526741 := by
  apply lucas_primality 872002404010526741 (11 : ZMod 872002404010526741)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 4), (18701, 1), (971025637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 4), (18701, 1), (971025637, 1)] : List FactorBlock).map factorBlockValue).prod) = 872002404010526741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_18701
      · exact prime_oneHundredEightDB_971025637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 872002404010526741) ^ 436001202005263370 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 872002404010526741) ^ 174400480802105348 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 872002404010526741) ^ 124571772001503820 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 872002404010526741) ^ 46628651088740 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 872002404010526741) ^ 898022020 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_969057377255761897 : Nat.Prime 969057377255761897 := by
  apply lucas_primality 969057377255761897 (7 : ZMod 969057377255761897)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (40377390718990079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (40377390718990079, 1)] : List FactorBlock).map factorBlockValue).prod) = 969057377255761897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_40377390718990079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 969057377255761897) ^ 484528688627880948 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 969057377255761897) ^ 323019125751920632 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 969057377255761897) ^ 24 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1110223939932987497 : Nat.Prime 1110223939932987497 := by
  apply lucas_primality 1110223939932987497 (3 : ZMod 1110223939932987497)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (739, 1), (4830151, 1), (38879033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (739, 1), (4830151, 1), (38879033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1110223939932987497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_739
      · exact prime_oneHundredEightDB_4830151
      · exact prime_oneHundredEightDB_38879033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1110223939932987497) ^ 555111969966493748 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110223939932987497) ^ 1502332800991864 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110223939932987497) ^ 229852843096 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110223939932987497) ^ 28555852712 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1492065108799822793 : Nat.Prime 1492065108799822793 := by
  apply lucas_primality 1492065108799822793 (3 : ZMod 1492065108799822793)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1492065108799822793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_47981
      · exact prime_oneHundredEightDB_88873
      · exact prime_oneHundredEightDB_1901651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1492065108799822793) ^ 746032554399911396 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 64872396034774904 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 31096998995432 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 16788733460104 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 784615635992 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1571357289259163123 : Nat.Prime 1571357289259163123 := by
  apply lucas_primality 1571357289259163123 (2 : ZMod 1571357289259163123)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (252309923, 1), (3113942707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (252309923, 1), (3113942707, 1)] : List FactorBlock).map factorBlockValue).prod) = 1571357289259163123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_252309923
      · exact prime_oneHundredEightDB_3113942707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1571357289259163123) ^ 785678644629581561 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1571357289259163123) ^ 6227885414 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1571357289259163123) ^ 504619846 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1608309624659490097 : Nat.Prime 1608309624659490097 := by
  apply lucas_primality 1608309624659490097 (5 : ZMod 1608309624659490097)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (40487, 1), (160907, 1), (5143253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (40487, 1), (160907, 1), (5143253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1608309624659490097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_40487
      · exact prime_oneHundredEightDB_160907
      · exact prime_oneHundredEightDB_5143253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1608309624659490097) ^ 804154812329745048 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 536103208219830032 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 39724099702608 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 9995274442128 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 312702802032 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1881806295833552119 : Nat.Prime 1881806295833552119 := by
  apply lucas_primality 1881806295833552119 (11 : ZMod 1881806295833552119)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (277, 1), (349, 1), (98507, 1), (32934523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (277, 1), (349, 1), (98507, 1), (32934523, 1)] : List FactorBlock).map factorBlockValue).prod) = 1881806295833552119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_277
      · exact prime_oneHundredEightDB_349
      · exact prime_oneHundredEightDB_98507
      · exact prime_oneHundredEightDB_32934523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1881806295833552119) ^ 940903147916776059 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1881806295833552119) ^ 627268765277850706 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1881806295833552119) ^ 6793524533695134 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1881806295833552119) ^ 5391995117001582 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1881806295833552119) ^ 19103274851874 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1881806295833552119) ^ 57137803266 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_101
      · exact prime_oneHundredEightDB_191
      · exact prime_oneHundredEightDB_48017
      · exact prime_oneHundredEightDB_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2224360176913807027 : Nat.Prime 2224360176913807027 := by
  apply lucas_primality 2224360176913807027 (2 : ZMod 2224360176913807027)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (1291, 1), (85159, 1), (34763647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (1291, 1), (85159, 1), (34763647, 1)] : List FactorBlock).map factorBlockValue).prod) = 2224360176913807027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_97
      · exact prime_oneHundredEightDB_1291
      · exact prime_oneHundredEightDB_85159
      · exact prime_oneHundredEightDB_34763647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2224360176913807027) ^ 1112180088456903513 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2224360176913807027) ^ 741453392304602342 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2224360176913807027) ^ 22931548215606258 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2224360176913807027) ^ 1722974575456086 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2224360176913807027) ^ 26120083337214 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2224360176913807027) ^ 63985236558 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2905562099488832683 : Nat.Prime 2905562099488832683 := by
  apply lucas_primality 2905562099488832683 (2 : ZMod 2905562099488832683)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (594163, 1), (815029461469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (594163, 1), (815029461469, 1)] : List FactorBlock).map factorBlockValue).prod) = 2905562099488832683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_594163
      · exact prime_oneHundredEightDB_815029461469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2905562099488832683) ^ 1452781049744416341 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2905562099488832683) ^ 968520699829610894 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2905562099488832683) ^ 4890176768814 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2905562099488832683) ^ 3564978 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2923321290853265399 : Nat.Prime 2923321290853265399 := by
  apply lucas_primality 2923321290853265399 (11 : ZMod 2923321290853265399)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (114617, 1), (112854550019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (114617, 1), (112854550019, 1)] : List FactorBlock).map factorBlockValue).prod) = 2923321290853265399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_113
      · exact prime_oneHundredEightDB_114617
      · exact prime_oneHundredEightDB_112854550019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2923321290853265399) ^ 1461660645426632699 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2923321290853265399) ^ 25870099919055446 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2923321290853265399) ^ 25505128304294 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2923321290853265399) ^ 25903442 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2938708440839972071 : Nat.Prime 2938708440839972071 := by
  apply lucas_primality 2938708440839972071 (12 : ZMod 2938708440839972071)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (103, 1), (1775887, 1), (59503181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (103, 1), (1775887, 1), (59503181, 1)] : List FactorBlock).map factorBlockValue).prod) = 2938708440839972071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_103
      · exact prime_oneHundredEightDB_1775887
      · exact prime_oneHundredEightDB_59503181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 2938708440839972071) ^ 1469354220419986035 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (12 : ZMod 2938708440839972071) ^ 979569480279990690 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (12 : ZMod 2938708440839972071) ^ 587741688167994414 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (12 : ZMod 2938708440839972071) ^ 28531149911067690 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (12 : ZMod 2938708440839972071) ^ 1654783463610 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (12 : ZMod 2938708440839972071) ^ 49387417470 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_3153414735646307359 : Nat.Prime 3153414735646307359 := by
  apply lucas_primality 3153414735646307359 (6 : ZMod 3153414735646307359)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (109, 1), (642877, 1), (159579683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (109, 1), (642877, 1), (159579683, 1)] : List FactorBlock).map factorBlockValue).prod) = 3153414735646307359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_109
      · exact prime_oneHundredEightDB_642877
      · exact prime_oneHundredEightDB_159579683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3153414735646307359) ^ 1576707367823153679 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3153414735646307359) ^ 1051138245215435786 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3153414735646307359) ^ 67093930545666114 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3153414735646307359) ^ 28930410418773462 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3153414735646307359) ^ 4905160296054 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3153414735646307359) ^ 19760753226 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_4055031395847446041 : Nat.Prime 4055031395847446041 := by
  apply lucas_primality 4055031395847446041 (17 : ZMod 4055031395847446041)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (13, 1), (313, 1), (12239, 1), (226182029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (13, 1), (313, 1), (12239, 1), (226182029, 1)] : List FactorBlock).map factorBlockValue).prod) = 4055031395847446041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_313
      · exact prime_oneHundredEightDB_12239
      · exact prime_oneHundredEightDB_226182029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 4055031395847446041) ^ 2027515697923723020 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 4055031395847446041) ^ 1351677131949148680 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 4055031395847446041) ^ 811006279169489208 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 4055031395847446041) ^ 311925491988265080 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 4055031395847446041) ^ 12955371871717080 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 4055031395847446041) ^ 331320483360360 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (17 : ZMod 4055031395847446041) ^ 17928176760 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_4694541528824955581 : Nat.Prime 4694541528824955581 := by
  apply lucas_primality 4694541528824955581 (2 : ZMod 4694541528824955581)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (8377, 1), (28020422160827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (8377, 1), (28020422160827, 1)] : List FactorBlock).map factorBlockValue).prod) = 4694541528824955581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_8377
      · exact prime_oneHundredEightDB_28020422160827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4694541528824955581) ^ 2347270764412477790 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4694541528824955581) ^ 938908305764991116 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4694541528824955581) ^ 560408443216540 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4694541528824955581) ^ 167540 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_5044842754105674733 : Nat.Prime 5044842754105674733 := by
  apply lucas_primality 5044842754105674733 (6 : ZMod 5044842754105674733)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (20113, 1), (20902081382297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (20113, 1), (20902081382297, 1)] : List FactorBlock).map factorBlockValue).prod) = 5044842754105674733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_20113
      · exact prime_oneHundredEightDB_20902081382297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5044842754105674733) ^ 2522421377052837366 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 5044842754105674733) ^ 1681614251368558244 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 5044842754105674733) ^ 250824976587564 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 5044842754105674733) ^ 241356 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_9129368555366506907 : Nat.Prime 9129368555366506907 := by
  apply lucas_primality 9129368555366506907 (2 : ZMod 9129368555366506907)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (307, 1), (284173, 1), (587894707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (307, 1), (284173, 1), (587894707, 1)] : List FactorBlock).map factorBlockValue).prod) = 9129368555366506907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_89
      · exact prime_oneHundredEightDB_307
      · exact prime_oneHundredEightDB_284173
      · exact prime_oneHundredEightDB_587894707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9129368555366506907) ^ 4564684277683253453 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9129368555366506907) ^ 102577174779398954 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9129368555366506907) ^ 29737356857871358 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9129368555366506907) ^ 32126094158722 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9129368555366506907) ^ 15528917758 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_13311937837557174217 : Nat.Prime 13311937837557174217 := by
  apply lucas_primality 13311937837557174217 (5 : ZMod 13311937837557174217)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) = 13311937837557174217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_4253
      · exact prime_oneHundredEightDB_130417135331503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13311937837557174217) ^ 6655968918778587108 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 4437312612519058072 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 3130011247956072 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 102072 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_20179371016422698933 : Nat.Prime 20179371016422698933 := by
  apply lucas_primality 20179371016422698933 (2 : ZMod 20179371016422698933)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5044842754105674733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5044842754105674733, 1)] : List FactorBlock).map factorBlockValue).prod) = 20179371016422698933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5044842754105674733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 20179371016422698933) ^ 10089685508211349466 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20179371016422698933) ^ 4 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_21705598351229560111 : Nat.Prime 21705598351229560111 := by
  apply lucas_primality 21705598351229560111 (6 : ZMod 21705598351229560111)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (17393, 1), (31573, 1), (62739473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (17393, 1), (31573, 1), (62739473, 1)] : List FactorBlock).map factorBlockValue).prod) = 21705598351229560111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_17393
      · exact prime_oneHundredEightDB_31573
      · exact prime_oneHundredEightDB_62739473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 21705598351229560111) ^ 10852799175614780055 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 7235199450409853370 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 4341119670245912022 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 3100799764461365730 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 1247950230048270 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 687473421950070 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 345963989070 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_29943190407334720097 : Nat.Prime 29943190407334720097 := by
  apply lucas_primality 29943190407334720097 (5 : ZMod 29943190407334720097)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (59, 1), (113, 1), (54101, 1), (52943941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (59, 1), (113, 1), (54101, 1), (52943941, 1)] : List FactorBlock).map factorBlockValue).prod) = 29943190407334720097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_59
      · exact prime_oneHundredEightDB_113
      · exact prime_oneHundredEightDB_54101
      · exact prime_oneHundredEightDB_52943941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 29943190407334720097) ^ 14971595203667360048 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 29943190407334720097) ^ 4277598629619245728 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 29943190407334720097) ^ 507511701819232544 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 29943190407334720097) ^ 264983985905616992 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 29943190407334720097) ^ 553468335286496 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 29943190407334720097) ^ 565564063456 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_35666719808417469181 : Nat.Prime 35666719808417469181 := by
  apply lucas_primality 35666719808417469181 (2 : ZMod 35666719808417469181)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (2801, 1), (23580678731417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (2801, 1), (23580678731417, 1)] : List FactorBlock).map factorBlockValue).prod) = 35666719808417469181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_2801
      · exact prime_oneHundredEightDB_23580678731417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35666719808417469181) ^ 17833359904208734590 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 11888906602805823060 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 7133343961683493836 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 12733566514965180 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 1512540 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_47019335053439553137 : Nat.Prime 47019335053439553137 := by
  apply lucas_primality 47019335053439553137 (3 : ZMod 47019335053439553137)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2938708440839972071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2938708440839972071, 1)] : List FactorBlock).map factorBlockValue).prod) = 47019335053439553137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_2938708440839972071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 47019335053439553137) ^ 23509667526719776568 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 47019335053439553137) ^ 16 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_56761465241633532463 : Nat.Prime 56761465241633532463 := by
  apply lucas_primality 56761465241633532463 (3 : ZMod 56761465241633532463)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3153414735646307359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3153414735646307359, 1)] : List FactorBlock).map factorBlockValue).prod) = 56761465241633532463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_3153414735646307359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 56761465241633532463) ^ 28380732620816766231 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 56761465241633532463) ^ 18920488413877844154 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 56761465241633532463) ^ 18 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_94281437355549787381 : Nat.Prime 94281437355549787381 := by
  apply lucas_primality 94281437355549787381 (6 : ZMod 94281437355549787381)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1571357289259163123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1571357289259163123, 1)] : List FactorBlock).map factorBlockValue).prod) = 94281437355549787381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_1571357289259163123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 94281437355549787381) ^ 47140718677774893690 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 94281437355549787381) ^ 31427145785183262460 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 94281437355549787381) ^ 18856287471109957476 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 94281437355549787381) ^ 60 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_120435602933347335617 : Nat.Prime 120435602933347335617 := by
  apply lucas_primality 120435602933347335617 (3 : ZMod 120435602933347335617)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (1881806295833552119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (1881806295833552119, 1)] : List FactorBlock).map factorBlockValue).prod) = 120435602933347335617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_1881806295833552119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 120435602933347335617) ^ 60217801466673667808 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 120435602933347335617) ^ 64 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_123442633682500070513 : Nat.Prime 123442633682500070513 := by
  apply lucas_primality 123442633682500070513 (5 : ZMod 123442633682500070513)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (47, 1), (101, 1), (383, 1), (419, 1), (20681, 1), (69959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (47, 1), (101, 1), (383, 1), (419, 1), (20681, 1), (69959, 1)] : List FactorBlock).map factorBlockValue).prod) = 123442633682500070513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_101
      · exact prime_oneHundredEightDB_383
      · exact prime_oneHundredEightDB_419
      · exact prime_oneHundredEightDB_20681
      · exact prime_oneHundredEightDB_69959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 123442633682500070513) ^ 61721316841250035256 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 17634661954642867216 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 2626439014521278096 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 1222204293886139312 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 322304526586162064 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 294612490889021648 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 5968890947367152 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 123442633682500070513) ^ 1764499688138768 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_133428789850506403081 : Nat.Prime 133428789850506403081 := by
  apply lucas_primality 133428789850506403081 (7 : ZMod 133428789850506403081)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (42379, 1), (48571, 1), (540182551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (42379, 1), (48571, 1), (540182551, 1)] : List FactorBlock).map factorBlockValue).prod) = 133428789850506403081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_42379
      · exact prime_oneHundredEightDB_48571
      · exact prime_oneHundredEightDB_540182551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 133428789850506403081) ^ 66714394925253201540 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 44476263283502134360 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 26685757970101280616 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 3148464802154520 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 2747087559459480 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 247006849080 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_141948996516209640817 : Nat.Prime 141948996516209640817 := by
  apply lucas_primality 141948996516209640817 (5 : ZMod 141948996516209640817)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (23, 1), (2011, 1), (7104093574121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (23, 1), (2011, 1), (7104093574121, 1)] : List FactorBlock).map factorBlockValue).prod) = 141948996516209640817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_2011
      · exact prime_oneHundredEightDB_7104093574121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 141948996516209640817) ^ 70974498258104820408 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 47316332172069880272 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 6171695500704766992 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 70586273752466256 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 19981296 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_6863
      · exact prime_oneHundredEightDB_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_277150409895147902543 : Nat.Prime 277150409895147902543 := by
  apply lucas_primality 277150409895147902543 (5 : ZMod 277150409895147902543)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (969057377255761897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (969057377255761897, 1)] : List FactorBlock).map factorBlockValue).prod) = 277150409895147902543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_969057377255761897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 277150409895147902543) ^ 138575204947573951271 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 277150409895147902543) ^ 25195491808649809322 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 277150409895147902543) ^ 21319262299626761734 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 277150409895147902543) ^ 286 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_431982838624831817233 : Nat.Prime 431982838624831817233 := by
  apply lucas_primality 431982838624831817233 (10 : ZMod 431982838624831817233)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (13, 1), (23, 1), (503, 1), (8548463135521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (13, 1), (23, 1), (503, 1), (8548463135521, 1)] : List FactorBlock).map factorBlockValue).prod) = 431982838624831817233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_503
      · exact prime_oneHundredEightDB_8548463135521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 431982838624831817233) ^ 215991419312415908616 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 431982838624831817233) ^ 143994279541610605744 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 431982838624831817233) ^ 61711834089261688176 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 431982838624831817233) ^ 33229449124987062864 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 431982838624831817233) ^ 18781862548905731184 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 431982838624831817233) ^ 858812800446981744 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (10 : ZMod 431982838624831817233) ^ 50533392 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_506987412674954663987 : Nat.Prime 506987412674954663987 := by
  apply lucas_primality 506987412674954663987 (2 : ZMod 506987412674954663987)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (563, 1), (4271, 1), (192103, 1), (8996327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (563, 1), (4271, 1), (192103, 1), (8996327, 1)] : List FactorBlock).map factorBlockValue).prod) = 506987412674954663987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_61
      · exact prime_oneHundredEightDB_563
      · exact prime_oneHundredEightDB_4271
      · exact prime_oneHundredEightDB_192103
      · exact prime_oneHundredEightDB_8996327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 506987412674954663987) ^ 253493706337477331993 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 506987412674954663987) ^ 8311269060245158426 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 506987412674954663987) ^ 900510502086953222 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 506987412674954663987) ^ 118704615470605166 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 506987412674954663987) ^ 2639143650411262 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 506987412674954663987) ^ 56354933816318 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1121278343585159108429 : Nat.Prime 1121278343585159108429 := by
  apply lucas_primality 1121278343585159108429 (2 : ZMod 1121278343585159108429)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (405373, 1), (2155273, 1), (320845783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (405373, 1), (2155273, 1), (320845783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1121278343585159108429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_405373
      · exact prime_oneHundredEightDB_2155273
      · exact prime_oneHundredEightDB_320845783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1121278343585159108429) ^ 560639171792579554214 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1121278343585159108429) ^ 2766041013055036 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1121278343585159108429) ^ 520248870368236 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1121278343585159108429) ^ 3494757927316 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1146250422224934728417 : Nat.Prime 1146250422224934728417 := by
  apply lucas_primality 1146250422224934728417 (3 : ZMod 1146250422224934728417)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (13, 1), (23, 1), (7573, 1), (1154401, 1), (1245779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (13, 1), (23, 1), (7573, 1), (1154401, 1), (1245779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1146250422224934728417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_7573
      · exact prime_oneHundredEightDB_1154401
      · exact prime_oneHundredEightDB_1245779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1146250422224934728417) ^ 573125211112467364208 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 104204583838630429856 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 88173109401918056032 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 49836974879344988192 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 151360150828592992 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 992939561058016 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 920107356300704 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_1549
      · exact prime_oneHundredEightDB_47713
      · exact prime_oneHundredEightDB_341461
      · exact prime_oneHundredEightDB_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1561950057225970932743 : Nat.Prime 1561950057225970932743 := by
  apply lucas_primality 1561950057225970932743 (5 : ZMod 1561950057225970932743)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (6074531, 1), (4147273733311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (6074531, 1), (4147273733311, 1)] : List FactorBlock).map factorBlockValue).prod) = 1561950057225970932743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_31
      · exact prime_oneHundredEightDB_6074531
      · exact prime_oneHundredEightDB_4147273733311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1561950057225970932743) ^ 780975028612985466371 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1561950057225970932743) ^ 50385485716966804282 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1561950057225970932743) ^ 257130971465282 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1561950057225970932743) ^ 376620922 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_2565337097194552275503 : Nat.Prime 2565337097194552275503 := by
  apply lucas_primality 2565337097194552275503 (5 : ZMod 2565337097194552275503)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (60133, 1), (1804687, 1), (11819515781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (60133, 1), (1804687, 1), (11819515781, 1)] : List FactorBlock).map factorBlockValue).prod) = 2565337097194552275503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_60133
      · exact prime_oneHundredEightDB_1804687
      · exact prime_oneHundredEightDB_11819515781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2565337097194552275503) ^ 1282668548597276137751 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2565337097194552275503) ^ 42661052952531094 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2565337097194552275503) ^ 1421485884917746 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2565337097194552275503) ^ 217042486742 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_8302232466023273733161 : Nat.Prime 8302232466023273733161 := by
  apply lucas_primality 8302232466023273733161 (3 : ZMod 8302232466023273733161)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (71, 1), (2923321290853265399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (71, 1), (2923321290853265399, 1)] : List FactorBlock).map factorBlockValue).prod) = 8302232466023273733161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_71
      · exact prime_oneHundredEightDB_2923321290853265399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8302232466023273733161) ^ 4151116233011636866580 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8302232466023273733161) ^ 1660446493204654746632 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8302232466023273733161) ^ 116932851634130615960 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8302232466023273733161) ^ 2840 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_22829483801584955382673 : Nat.Prime 22829483801584955382673 := by
  apply lucas_primality 22829483801584955382673 (5 : ZMod 22829483801584955382673)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (911, 1), (322319, 1), (1619759629171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (911, 1), (322319, 1), (1619759629171, 1)] : List FactorBlock).map factorBlockValue).prod) = 22829483801584955382673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_911
      · exact prime_oneHundredEightDB_322319
      · exact prime_oneHundredEightDB_1619759629171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22829483801584955382673) ^ 11414741900792477691336 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 22829483801584955382673) ^ 7609827933861651794224 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 22829483801584955382673) ^ 25059806587908842352 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 22829483801584955382673) ^ 70828849064389488 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 22829483801584955382673) ^ 14094365232 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_27696211172835316838549 : Nat.Prime 27696211172835316838549 := by
  apply lucas_primality 27696211172835316838549 (3 : ZMod 27696211172835316838549)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (67, 1), (197, 1), (27609957665089577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (67, 1), (197, 1), (27609957665089577, 1)] : List FactorBlock).map factorBlockValue).prod) = 27696211172835316838549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_67
      · exact prime_oneHundredEightDB_197
      · exact prime_oneHundredEightDB_27609957665089577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27696211172835316838549) ^ 13848105586417658419274 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27696211172835316838549) ^ 1457695324886069307292 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27696211172835316838549) ^ 413376286161721146844 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27696211172835316838549) ^ 140589904430636126084 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 27696211172835316838549) ^ 1003124 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_47886543588161587791203 : Nat.Prime 47886543588161587791203 := by
  apply lucas_primality 47886543588161587791203 (2 : ZMod 47886543588161587791203)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) = 47886543588161587791203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_14201963
      · exact prime_oneHundredEightDB_240844691621461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47886543588161587791203) ^ 23943271794080793895601 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 6840934798308798255886 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 3371825682700454 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 198827482 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_50435018577897128050349 : Nat.Prime 50435018577897128050349 := by
  apply lucas_primality 50435018577897128050349 (2 : ZMod 50435018577897128050349)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1146250422224934728417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1146250422224934728417, 1)] : List FactorBlock).map factorBlockValue).prod) = 50435018577897128050349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_1146250422224934728417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50435018577897128050349) ^ 25217509288948564025174 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 50435018577897128050349) ^ 4585001688899738913668 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 50435018577897128050349) ^ 44 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_102429416767293794920459 : Nat.Prime 102429416767293794920459 := by
  apply lucas_primality 102429416767293794920459 (3 : ZMod 102429416767293794920459)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2063, 1), (2115948589, 1), (3910831549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2063, 1), (2115948589, 1), (3910831549, 1)] : List FactorBlock).map factorBlockValue).prod) = 102429416767293794920459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_2063
      · exact prime_oneHundredEightDB_2115948589
      · exact prime_oneHundredEightDB_3910831549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 102429416767293794920459) ^ 51214708383646897460229 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 102429416767293794920459) ^ 34143138922431264973486 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 102429416767293794920459) ^ 49650710987539406166 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 102429416767293794920459) ^ 48408272913522 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 102429416767293794920459) ^ 26191211634642 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_105243360706265091623897 : Nat.Prime 105243360706265091623897 := by
  apply lucas_primality 105243360706265091623897 (3 : ZMod 105243360706265091623897)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (131, 1), (9129368555366506907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (131, 1), (9129368555366506907, 1)] : List FactorBlock).map factorBlockValue).prod) = 105243360706265091623897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_131
      · exact prime_oneHundredEightDB_9129368555366506907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 105243360706265091623897) ^ 52621680353132545811948 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 105243360706265091623897) ^ 9567578246024099238536 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 105243360706265091623897) ^ 803384432872252607816 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 105243360706265091623897) ^ 11528 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_119947828689167453892781 : Nat.Prime 119947828689167453892781 := by
  apply lucas_primality 119947828689167453892781 (6 : ZMod 119947828689167453892781)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (29, 1), (4055031395847446041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (29, 1), (4055031395847446041, 1)] : List FactorBlock).map factorBlockValue).prod) = 119947828689167453892781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_4055031395847446041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 119947828689167453892781) ^ 59973914344583726946390 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 119947828689167453892781) ^ 39982609563055817964260 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 119947828689167453892781) ^ 23989565737833490778556 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 119947828689167453892781) ^ 7055754628774556111340 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 119947828689167453892781) ^ 4136132023764394961820 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 119947828689167453892781) ^ 29580 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_135028625328865849106587 : Nat.Prime 135028625328865849106587 := by
  apply lucas_primality 135028625328865849106587 (2 : ZMod 135028625328865849106587)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (49169, 1), (4531707249364499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (49169, 1), (4531707249364499, 1)] : List FactorBlock).map factorBlockValue).prod) = 135028625328865849106587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_101
      · exact prime_oneHundredEightDB_49169
      · exact prime_oneHundredEightDB_4531707249364499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135028625328865849106587) ^ 67514312664432924553293 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 135028625328865849106587) ^ 45009541776288616368862 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 135028625328865849106587) ^ 1336917082464018307986 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 135028625328865849106587) ^ 2746214593114886394 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 135028625328865849106587) ^ 29796414 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_192414941557532911343323 : Nat.Prime 192414941557532911343323 := by
  apply lucas_primality 192414941557532911343323 (3 : ZMod 192414941557532911343323)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (17, 1), (29943190407334720097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (17, 1), (29943190407334720097, 1)] : List FactorBlock).map factorBlockValue).prod) = 192414941557532911343323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_29943190407334720097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 192414941557532911343323) ^ 96207470778766455671661 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 192414941557532911343323) ^ 64138313852510970447774 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 192414941557532911343323) ^ 27487848793933273049046 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 192414941557532911343323) ^ 11318525973972524196666 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 192414941557532911343323) ^ 6426 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_288520672202247931694107 : Nat.Prime 288520672202247931694107 := by
  apply lucas_primality 288520672202247931694107 (2 : ZMod 288520672202247931694107)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (79423, 1), (4735909, 1), (1800601883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (79423, 1), (4735909, 1), (1800601883, 1)] : List FactorBlock).map factorBlockValue).prod) = 288520672202247931694107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_71
      · exact prime_oneHundredEightDB_79423
      · exact prime_oneHundredEightDB_4735909
      · exact prime_oneHundredEightDB_1800601883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 288520672202247931694107) ^ 144260336101123965847053 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 288520672202247931694107) ^ 96173557400749310564702 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 288520672202247931694107) ^ 4063671439468280728086 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 288520672202247931694107) ^ 3632709318487691622 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 288520672202247931694107) ^ 60921920628594834 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 288520672202247931694107) ^ 160235682815982 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_368516849262748308491981 : Nat.Prime 368516849262748308491981 := by
  apply lucas_primality 368516849262748308491981 (3 : ZMod 368516849262748308491981)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (59, 1), (1367, 1), (17573710800148991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (59, 1), (1367, 1), (17573710800148991, 1)] : List FactorBlock).map factorBlockValue).prod) = 368516849262748308491981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_59
      · exact prime_oneHundredEightDB_1367
      · exact prime_oneHundredEightDB_17573710800148991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 368516849262748308491981) ^ 184258424631374154245990 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 368516849262748308491981) ^ 73703369852549661698396 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 368516849262748308491981) ^ 28347449943288331422460 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 368516849262748308491981) ^ 6246048292588954381220 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 368516849262748308491981) ^ 269580723674285521940 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 368516849262748308491981) ^ 20969780 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_421226894041107731343491 : Nat.Prime 421226894041107731343491 := by
  apply lucas_primality 421226894041107731343491 (2 : ZMod 421226894041107731343491)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (66373, 1), (85621, 1), (157705373099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (66373, 1), (85621, 1), (157705373099, 1)] : List FactorBlock).map factorBlockValue).prod) = 421226894041107731343491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_66373
      · exact prime_oneHundredEightDB_85621
      · exact prime_oneHundredEightDB_157705373099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 421226894041107731343491) ^ 210613447020553865671745 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 84245378808221546268698 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 8962274341300164496670 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 6346359122551455130 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 4919668002488965690 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 2670973637510 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_519263523941442000566203 : Nat.Prime 519263523941442000566203 := by
  apply lucas_primality 519263523941442000566203 (22 : ZMod 519263523941442000566203)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 2), (17, 1), (79, 1), (1783, 1), (97373, 1), (841651051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 2), (17, 1), (79, 1), (1783, 1), (97373, 1), (841651051, 1)] : List FactorBlock).map factorBlockValue).prod) = 519263523941442000566203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_79
      · exact prime_oneHundredEightDB_1783
      · exact prime_oneHundredEightDB_97373
      · exact prime_oneHundredEightDB_841651051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 519263523941442000566203) ^ 259631761970721000283101 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (22 : ZMod 519263523941442000566203) ^ 173087841313814000188734 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (22 : ZMod 519263523941442000566203) ^ 74180503420206000080886 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (22 : ZMod 519263523941442000566203) ^ 30544913173026000033306 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (22 : ZMod 519263523941442000566203) ^ 6572955999258759500838 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (22 : ZMod 519263523941442000566203) ^ 291230243377140774294 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (22 : ZMod 519263523941442000566203) ^ 5332725950124182274 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (22 : ZMod 519263523941442000566203) ^ 616958207709102 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_878899926231809511221431 : Nat.Prime 878899926231809511221431 := by
  apply lucas_primality 878899926231809511221431 (6 : ZMod 878899926231809511221431)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) = 878899926231809511221431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_797
      · exact prime_oneHundredEightDB_125287
      · exact prime_oneHundredEightDB_13971226936099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 878899926231809511221431) ^ 439449963115904755610715 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 292966642077269837073810 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 175779985246361902244286 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 125557132318829930174490 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 1102760258760112310190 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 7015092756884668890 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 62907855570 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1682809102787506222932509 : Nat.Prime 1682809102787506222932509 := by
  apply lucas_primality 1682809102787506222932509 (3 : ZMod 1682809102787506222932509)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (223, 1), (1523, 1), (6102026044398121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (223, 1), (1523, 1), (6102026044398121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1682809102787506222932509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_223
      · exact prime_oneHundredEightDB_1523
      · exact prime_oneHundredEightDB_6102026044398121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1682809102787506222932509) ^ 841404551393753111466254 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 240401300398215174704644 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 58027900096120904239052 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 7546229160482090685796 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 1104930468015434158196 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 275778748 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_4472636383743338313409943 : Nat.Prime 4472636383743338313409943 := by
  apply lucas_primality 4472636383743338313409943 (5 : ZMod 4472636383743338313409943)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (70496453, 1), (4531774490983801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (70496453, 1), (4531774490983801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4472636383743338313409943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_70496453
      · exact prime_oneHundredEightDB_4531774490983801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4472636383743338313409943) ^ 2236318191871669156704971 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4472636383743338313409943) ^ 638948054820476901915706 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4472636383743338313409943) ^ 63444842873773214 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4472636383743338313409943) ^ 986950342 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_7844975637939593399559293 : Nat.Prime 7844975637939593399559293 := by
  apply lucas_primality 7844975637939593399559293 (2 : ZMod 7844975637939593399559293)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (617, 1), (13267, 1), (41257, 1), (829617739043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (617, 1), (13267, 1), (41257, 1), (829617739043, 1)] : List FactorBlock).map factorBlockValue).prod) = 7844975637939593399559293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_617
      · exact prime_oneHundredEightDB_13267
      · exact prime_oneHundredEightDB_41257
      · exact prime_oneHundredEightDB_829617739043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7844975637939593399559293) ^ 3922487818969796699779646 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7844975637939593399559293) ^ 1120710805419941914222756 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7844975637939593399559293) ^ 12714709299740021717276 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7844975637939593399559293) ^ 591314964795326253076 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7844975637939593399559293) ^ 190148959884131017756 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7844975637939593399559293) ^ 9456132949844 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_8076717280226758313063891 : Nat.Prime 8076717280226758313063891 := by
  apply lucas_primality 8076717280226758313063891 (2 : ZMod 8076717280226758313063891)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 2), (56821, 1), (2819741595528049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 2), (56821, 1), (2819741595528049, 1)] : List FactorBlock).map factorBlockValue).prod) = 8076717280226758313063891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_71
      · exact prime_oneHundredEightDB_56821
      · exact prime_oneHundredEightDB_2819741595528049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8076717280226758313063891) ^ 4038358640113379156531945 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8076717280226758313063891) ^ 1615343456045351662612778 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8076717280226758313063891) ^ 113756581411644483282590 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8076717280226758313063891) ^ 142143173830568950090 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8076717280226758313063891) ^ 2864346610 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_15634238212698031366625083 : Nat.Prime 15634238212698031366625083 := by
  apply lucas_primality 15634238212698031366625083 (3 : ZMod 15634238212698031366625083)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (2027, 1), (354689, 1), (124975823753281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (2027, 1), (354689, 1), (124975823753281, 1)] : List FactorBlock).map factorBlockValue).prod) = 15634238212698031366625083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_2027
      · exact prime_oneHundredEightDB_354689
      · exact prime_oneHundredEightDB_124975823753281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15634238212698031366625083) ^ 7817119106349015683312541 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 15634238212698031366625083) ^ 5211412737566010455541694 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 15634238212698031366625083) ^ 539111662506828667814658 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 15634238212698031366625083) ^ 7712993691513582321966 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 15634238212698031366625083) ^ 44078723086134702138 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 15634238212698031366625083) ^ 125098100922 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_30300147955174376405132191 : Nat.Prime 30300147955174376405132191 := by
  apply lucas_primality 30300147955174376405132191 (11 : ZMod 30300147955174376405132191)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (43, 1), (47, 1), (7725973261, 1), (21561686411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (43, 1), (47, 1), (7725973261, 1), (21561686411, 1)] : List FactorBlock).map factorBlockValue).prod) = 30300147955174376405132191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_43
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_7725973261
      · exact prime_oneHundredEightDB_21561686411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 30300147955174376405132191) ^ 15150073977587188202566095 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 30300147955174376405132191) ^ 10100049318391458801710730 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 30300147955174376405132191) ^ 6060029591034875281026438 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 30300147955174376405132191) ^ 704654603608706428026330 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 30300147955174376405132191) ^ 644683999046263327768770 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 30300147955174376405132191) ^ 3921855141296790 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (11 : ZMod 30300147955174376405132191) ^ 1405277276443290 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_33877639555082202751718507 : Nat.Prime 33877639555082202751718507 := by
  apply lucas_primality 33877639555082202751718507 (2 : ZMod 33877639555082202751718507)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (529981, 1), (2905562099488832683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (529981, 1), (2905562099488832683, 1)] : List FactorBlock).map factorBlockValue).prod) = 33877639555082202751718507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_529981
      · exact prime_oneHundredEightDB_2905562099488832683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33877639555082202751718507) ^ 16938819777541101375859253 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33877639555082202751718507) ^ 3079785414098382068338046 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33877639555082202751718507) ^ 63922366188754319026 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33877639555082202751718507) ^ 11659582 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_61475601099231979860966323 : Nat.Prime 61475601099231979860966323 := by
  apply lucas_primality 61475601099231979860966323 (2 : ZMod 61475601099231979860966323)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12437760691, 1), (2471329149455171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12437760691, 1), (2471329149455171, 1)] : List FactorBlock).map factorBlockValue).prod) = 61475601099231979860966323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_12437760691
      · exact prime_oneHundredEightDB_2471329149455171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61475601099231979860966323) ^ 30737800549615989930483161 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 61475601099231979860966323) ^ 4942658298910342 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 61475601099231979860966323) ^ 24875521382 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_68062272645578263417498429 : Nat.Prime 68062272645578263417498429 := by
  apply lucas_primality 68062272645578263417498429 (2 : ZMod 68062272645578263417498429)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (701, 1), (141948996516209640817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (701, 1), (141948996516209640817, 1)] : List FactorBlock).map factorBlockValue).prod) = 68062272645578263417498429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_19
      · exact prime_oneHundredEightDB_701
      · exact prime_oneHundredEightDB_141948996516209640817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68062272645578263417498429) ^ 34031136322789131708749214 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 22687424215192754472499476 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 3582224876083066495657812 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 97093113617087394318828 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 479484 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_85694512404768337027669163 : Nat.Prime 85694512404768337027669163 := by
  apply lucas_primality 85694512404768337027669163 (2 : ZMod 85694512404768337027669163)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (409, 1), (9606671, 1), (991366194763289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (409, 1), (9606671, 1), (991366194763289, 1)] : List FactorBlock).map factorBlockValue).prod) = 85694512404768337027669163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_409
      · exact prime_oneHundredEightDB_9606671
      · exact prime_oneHundredEightDB_991366194763289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85694512404768337027669163) ^ 42847256202384168513834581 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 85694512404768337027669163) ^ 7790410218615303366151742 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 85694512404768337027669163) ^ 209522035219482486620218 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 85694512404768337027669163) ^ 8920313020480074422 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 85694512404768337027669163) ^ 86440825658 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_104147490606121388394149309 : Nat.Prime 104147490606121388394149309 := by
  apply lucas_primality 104147490606121388394149309 (2 : ZMod 104147490606121388394149309)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (640933, 1), (5828189, 1), (118138253869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (640933, 1), (5828189, 1), (118138253869, 1)] : List FactorBlock).map factorBlockValue).prod) = 104147490606121388394149309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_59
      · exact prime_oneHundredEightDB_640933
      · exact prime_oneHundredEightDB_5828189
      · exact prime_oneHundredEightDB_118138253869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104147490606121388394149309) ^ 52073745303060694197074654 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 104147490606121388394149309) ^ 1765211705188498108375412 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 104147490606121388394149309) ^ 162493568916129124876 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 104147490606121388394149309) ^ 17869614490216667372 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 104147490606121388394149309) ^ 881572963839532 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_116182732923662258572545089 : Nat.Prime 116182732923662258572545089 := by
  apply lucas_primality 116182732923662258572545089 (3 : ZMod 116182732923662258572545089)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (29, 1), (26849, 1), (462577, 1), (526681, 1), (9569821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (29, 1), (26849, 1), (462577, 1), (526681, 1), (9569821, 1)] : List FactorBlock).map factorBlockValue).prod) = 116182732923662258572545089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_29
      · exact prime_oneHundredEightDB_26849
      · exact prime_oneHundredEightDB_462577
      · exact prime_oneHundredEightDB_526681
      · exact prime_oneHundredEightDB_9569821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 116182732923662258572545089) ^ 58091366461831129286272544 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 116182732923662258572545089) ^ 4006301135298698571467072 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 116182732923662258572545089) ^ 4327264811488780162112 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 116182732923662258572545089) ^ 251164093596660142144 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 116182732923662258572545089) ^ 220594122293498832448 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 116182732923662258572545089) ^ 12140533550592248128 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_613869343668773183515514677 : Nat.Prime 613869343668773183515514677 := by
  apply lucas_primality 613869343668773183515514677 (6 : ZMod 613869343668773183515514677)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (47, 1), (14779, 1), (618877695587683109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (47, 1), (14779, 1), (618877695587683109, 1)] : List FactorBlock).map factorBlockValue).prod) = 613869343668773183515514677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_17
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_14779
      · exact prime_oneHundredEightDB_618877695587683109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 613869343668773183515514677) ^ 306934671834386591757757338 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 204623114556257727838504892 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 87695620524110454787930668 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 36109961392280775500912628 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 13061049865293046457776908 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 41536595417062939543644 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 991907364 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_1276848234831048221712270529 : Nat.Prime 1276848234831048221712270529 := by
  apply lucas_primality 1276848234831048221712270529 (7 : ZMod 1276848234831048221712270529)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1276848234831048221712270529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_171401
      · exact prime_oneHundredEightDB_714027719
      · exact prime_oneHundredEightDB_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1276848234831048221712270529) ^ 638424117415524110856135264 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1276848234831048221712270529) ^ 425616078277016073904090176 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1276848234831048221712270529) ^ 7449479494466474651328 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1276848234831048221712270529) ^ 1788233426874914112 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1276848234831048221712270529) ^ 211481392431143232 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_3273969832900123645416078277 : Nat.Prime 3273969832900123645416078277 := by
  apply lucas_primality 3273969832900123645416078277 (2 : ZMod 3273969832900123645416078277)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (4472636383743338313409943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (4472636383743338313409943, 1)] : List FactorBlock).map factorBlockValue).prod) = 3273969832900123645416078277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_61
      · exact prime_oneHundredEightDB_4472636383743338313409943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3273969832900123645416078277) ^ 1636984916450061822708039138 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273969832900123645416078277) ^ 1091323277633374548472026092 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273969832900123645416078277) ^ 53671636604920059760919316 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273969832900123645416078277) ^ 732 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_3869237075245600671855365239 : Nat.Prime 3869237075245600671855365239 := by
  apply lucas_primality 3869237075245600671855365239 (3 : ZMod 3869237075245600671855365239)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 3869237075245600671855365239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_461
      · exact prime_oneHundredEightDB_69997
      · exact prime_oneHundredEightDB_2220502305087140441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3869237075245600671855365239) ^ 1934618537622800335927682619 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3869237075245600671855365239) ^ 1289745691748533557285121746 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3869237075245600671855365239) ^ 8393138991855966750228558 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3869237075245600671855365239) ^ 55277184382839274138254 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3869237075245600671855365239) ^ 1742505318 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_6384241174155241108561352641 : Nat.Prime 6384241174155241108561352641 := by
  apply lucas_primality 6384241174155241108561352641 (7 : ZMod 6384241174155241108561352641)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 6384241174155241108561352641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_171401
      · exact prime_oneHundredEightDB_714027719
      · exact prime_oneHundredEightDB_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6384241174155241108561352641) ^ 3192120587077620554280676320 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 2128080391385080369520450880 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 1276848234831048221712270528 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 37247397472332373256640 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 8941167134374570560 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 1057406962155716160 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_14187202609233869130136339211 : Nat.Prime 14187202609233869130136339211 := by
  apply lucas_primality 14187202609233869130136339211 (6 : ZMod 14187202609233869130136339211)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (47, 1), (2609, 1), (1030817, 1), (487995060087097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (47, 1), (2609, 1), (1030817, 1), (487995060087097, 1)] : List FactorBlock).map factorBlockValue).prod) = 14187202609233869130136339211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_23
      · exact prime_oneHundredEightDB_47
      · exact prime_oneHundredEightDB_2609
      · exact prime_oneHundredEightDB_1030817
      · exact prime_oneHundredEightDB_487995060087097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14187202609233869130136339211) ^ 7093601304616934565068169605 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 14187202609233869130136339211) ^ 2837440521846773826027267842 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 14187202609233869130136339211) ^ 616834896053646483918971270 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 14187202609233869130136339211) ^ 301855374664550407024177430 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 14187202609233869130136339211) ^ 5437793257659589547771690 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 14187202609233869130136339211) ^ 13763066198203821949130 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (6 : ZMod 14187202609233869130136339211) ^ 29072430787930 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_15960602935388102771403381607 : Nat.Prime 15960602935388102771403381607 := by
  apply lucas_primality 15960602935388102771403381607 (3 : ZMod 15960602935388102771403381607)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) = 15960602935388102771403381607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_2411
      · exact prime_oneHundredEightDB_7039
      · exact prime_oneHundredEightDB_188911
      · exact prime_oneHundredEightDB_829722028640579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15960602935388102771403381607) ^ 7980301467694051385701690803 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 5320200978462700923801127202 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 6619909969053547395853746 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 2267453180194360388038554 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 84487419659988580714746 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 19236084356514 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_21280803913850803695204508801 : Nat.Prime 21280803913850803695204508801 := by
  apply lucas_primality 21280803913850803695204508801 (14 : ZMod 21280803913850803695204508801)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850803695204508801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_171401
      · exact prime_oneHundredEightDB_714027719
      · exact prime_oneHundredEightDB_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 21280803913850803695204508801) ^ 10640401956925401847602254400 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 7093601304616934565068169600 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 4256160782770160739040901760 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 124157991574441244188800 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 29803890447915235200 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 3524689873852387200 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_31921205870776205542806763223 : Nat.Prime 31921205870776205542806763223 := by
  apply lucas_primality 31921205870776205542806763223 (5 : ZMod 31921205870776205542806763223)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4391, 1), (519263523941442000566203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4391, 1), (519263523941442000566203, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921205870776205542806763223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_7
      · exact prime_oneHundredEightDB_4391
      · exact prime_oneHundredEightDB_519263523941442000566203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31921205870776205542806763223) ^ 15960602935388102771403381611 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 31921205870776205542806763223) ^ 4560172267253743648972394746 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 31921205870776205542806763223) ^ 7269689335180188007926842 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 31921205870776205542806763223) ^ 61474 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_63842411741552411085613526413 : Nat.Prime 63842411741552411085613526413 := by
  apply lucas_primality 63842411741552411085613526413 (5 : ZMod 63842411741552411085613526413)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3662228970263, 1), (1452722104942727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3662228970263, 1), (1452722104942727, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552411085613526413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_3
      · exact prime_oneHundredEightDB_3662228970263
      · exact prime_oneHundredEightDB_1452722104942727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 63842411741552411085613526413) ^ 31921205870776205542806763206 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 63842411741552411085613526413) ^ 21280803913850803695204508804 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 63842411741552411085613526413) ^ 17432665259312724 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (5 : ZMod 63842411741552411085613526413) ^ 43946747643156 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_127684823483104822171227052817 : Nat.Prime 127684823483104822171227052817 := by
  apply lucas_primality 127684823483104822171227052817 (3 : ZMod 127684823483104822171227052817)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (613869343668773183515514677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (613869343668773183515514677, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_13
      · exact prime_oneHundredEightDB_613869343668773183515514677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 127684823483104822171227052817) ^ 63842411741552411085613526408 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 127684823483104822171227052817) ^ 9821909498700370936248234832 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 127684823483104822171227052817) ^ 208 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_127684823483104822171227052841 : Nat.Prime 127684823483104822171227052841 := by
  apply lucas_primality 127684823483104822171227052841 (3 : ZMod 127684823483104822171227052841)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (31, 1), (79, 1), (4703, 1), (277150409895147902543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (31, 1), (79, 1), (4703, 1), (277150409895147902543, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_5
      · exact prime_oneHundredEightDB_31
      · exact prime_oneHundredEightDB_79
      · exact prime_oneHundredEightDB_4703
      · exact prime_oneHundredEightDB_277150409895147902543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 127684823483104822171227052841) ^ 63842411741552411085613526420 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 127684823483104822171227052841) ^ 25536964696620964434245410568 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 127684823483104822171227052841) ^ 4118865273648542650684743640 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 127684823483104822171227052841) ^ 1616263588393731926218063960 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 127684823483104822171227052841) ^ 27149654153328688533112280 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (3 : ZMod 127684823483104822171227052841) ^ 460705880 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem prime_oneHundredEightDB_127684823483104822171227052877 : Nat.Prime 127684823483104822171227052877 := by
  apply lucas_primality 127684823483104822171227052877 (2 : ZMod 127684823483104822171227052877)
  · rw [← oneHundredEightDBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (41, 1), (691, 1), (102429416767293794920459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (41, 1), (691, 1), (102429416767293794920459, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEightDB_2
      · exact prime_oneHundredEightDB_11
      · exact prime_oneHundredEightDB_41
      · exact prime_oneHundredEightDB_691
      · exact prime_oneHundredEightDB_102429416767293794920459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 127684823483104822171227052877) ^ 63842411741552411085613526438 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 127684823483104822171227052877) ^ 11607711225736802015566095716 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 127684823483104822171227052877) ^ 3114263987392800540761635436 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 127684823483104822171227052877) ^ 184782667848198006036508036 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide
    · change (2 : ZMod 127684823483104822171227052877) ^ 1246564 ≠ 1
      rw [← oneHundredEightDBFastPow_eq_pow]
      decide

private theorem phi_oneHundredEightDB_127684823483104822171227052800 : Nat.totient 127684823483104822171227052800 = 34049087556049349416194048000 := by
  rw [← show ((([(2, 8), (3, 3), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_5, prime_oneHundredEightDB_171401, prime_oneHundredEightDB_714027719, prime_oneHundredEightDB_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052801 : Nat.totient 127684823483104822171227052801 = 127061215628917157210431119360 := by
  rw [← show ((([(239, 1), (2273, 1), (4409, 1), (27647, 1), (1928207786983321, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_239, prime_oneHundredEightDB_2273, prime_oneHundredEightDB_4409, prime_oneHundredEightDB_27647, prime_oneHundredEightDB_1928207786983321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052802 : Nat.totient 127684823483104822171227052802 = 63744925765665176385058938960 := by
  rw [← show ((([(2, 1), (967, 1), (2027, 1), (44618071, 1), (729992287516259, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_967, prime_oneHundredEightDB_2027, prime_oneHundredEightDB_44618071, prime_oneHundredEightDB_729992287516259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052803 : Nat.totient 127684823483104822171227052803 = 78575275989602967489985878624 := by
  rw [← show ((([(3, 1), (13, 1), (3273969832900123645416078277, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_13, prime_oneHundredEightDB_3273969832900123645416078277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052804 : Nat.totient 127684823483104822171227052804 = 53905319935297984626658754976 := by
  rw [← show ((([(2, 2), (7, 1), (67, 1), (68062272645578263417498429, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_7, prime_oneHundredEightDB_67, prime_oneHundredEightDB_68062272645578263417498429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052805 : Nat.totient 127684823483104822171227052805 = 102147085927824689961385720320 := by
  rw [← show ((([(5, 1), (132169, 1), (156219162989, 1), (1236816770621, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_5, prime_oneHundredEightDB_132169, prime_oneHundredEightDB_156219162989, prime_oneHundredEightDB_1236816770621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052806 : Nat.totient 127684823483104822171227052806 = 42561607827701607390409017600 := by
  rw [← show ((([(2, 1), (3, 1), (21280803913850803695204508801, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_21280803913850803695204508801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052807 : Nat.totient 127684823483104822171227052807 = 127246367971372515416007300000 := by
  rw [← show ((([(293, 1), (47639, 1), (6197501251, 1), (1476020537791, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_293, prime_oneHundredEightDB_47639, prime_oneHundredEightDB_6197501251, prime_oneHundredEightDB_1476020537791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052808 : Nat.totient 127684823483104822171227052808 = 63140848857911274824701209600 := by
  rw [← show ((([(2, 3), (173, 1), (191, 1), (300331, 1), (1608309624659490097, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_173, prime_oneHundredEightDB_191, prime_oneHundredEightDB_300331, prime_oneHundredEightDB_1608309624659490097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052809 : Nat.totient 127684823483104822171227052809 = 77886505415273059310634228960 := by
  rw [← show ((([(3, 2), (19, 1), (31, 1), (503, 1), (47886543588161587791203, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_19, prime_oneHundredEightDB_31, prime_oneHundredEightDB_503, prime_oneHundredEightDB_47886543588161587791203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052810 : Nat.totient 127684823483104822171227052810 = 46219197838300443218515968000 := by
  rw [← show ((([(2, 1), (5, 1), (11, 2), (241, 1), (2441, 1), (1012597, 1), (177146449272173, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_5, prime_oneHundredEightDB_11, prime_oneHundredEightDB_241, prime_oneHundredEightDB_2441, prime_oneHundredEightDB_1012597, prime_oneHundredEightDB_177146449272173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052811 : Nat.totient 127684823483104822171227052811 = 108747038016547874023902202368 := by
  rw [← show ((([(7, 1), (157, 1), (116182732923662258572545089, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_7, prime_oneHundredEightDB_157, prime_oneHundredEightDB_116182732923662258572545089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052812 : Nat.totient 127684823483104822171227052812 = 39033229298169067841026031616 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (73, 1), (83, 1), (906208483, 1), (113993486613649, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_17, prime_oneHundredEightDB_73, prime_oneHundredEightDB_83, prime_oneHundredEightDB_906208483, prime_oneHundredEightDB_113993486613649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052813 : Nat.totient 127684823483104822171227052813 = 127681388365895387322361830400 := by
  rw [← show ((([(37361, 1), (11400581, 1), (20226677, 1), (14820718709, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_37361, prime_oneHundredEightDB_11400581, prime_oneHundredEightDB_20226677, prime_oneHundredEightDB_14820718709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052814 : Nat.totient 127684823483104822171227052814 = 61640945811312033110091047040 := by
  rw [← show ((([(2, 1), (29, 1), (17833891, 1), (123442633682500070513, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_29, prime_oneHundredEightDB_17833891, prime_oneHundredEightDB_123442633682500070513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052815 : Nat.totient 127684823483104822171227052815 = 68098546564904517849066781440 := by
  rw [← show ((([(3, 1), (5, 1), (2623979, 1), (10014130171, 1), (323947351769, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_5, prime_oneHundredEightDB_2623979, prime_oneHundredEightDB_10014130171, prime_oneHundredEightDB_323947351769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052816 : Nat.totient 127684823483104822171227052816 = 58931456992202225617489408896 := by
  rw [← show ((([(2, 4), (13, 1), (613869343668773183515514677, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_13, prime_oneHundredEightDB_613869343668773183515514677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052817 : Nat.totient 127684823483104822171227052817 = 127684823483104822171227052816 := by
  rw [← show ((([(127684823483104822171227052817, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_127684823483104822171227052817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052818 : Nat.totient 127684823483104822171227052818 = 36449737740685604049375144960 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_7, prime_oneHundredEightDB_1153, prime_oneHundredEightDB_878899926231809511221431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052819 : Nat.totient 127684823483104822171227052819 = 127676746765824595412913973120 := by
  rw [← show ((([(15809, 1), (8076717280226758313063891, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_15809, prime_oneHundredEightDB_8076717280226758313063891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052820 : Nat.totient 127684823483104822171227052820 = 51073929393241928868490821120 := by
  rw [← show ((([(2, 2), (5, 1), (6384241174155241108561352641, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_5, prime_oneHundredEightDB_6384241174155241108561352641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052821 : Nat.totient 127684823483104822171227052821 = 73436148045809571899527358400 := by
  rw [← show ((([(3, 1), (11, 1), (23, 1), (127, 1), (61027, 1), (21705598351229560111, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_11, prime_oneHundredEightDB_23, prime_oneHundredEightDB_127, prime_oneHundredEightDB_61027, prime_oneHundredEightDB_21705598351229560111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052822 : Nat.totient 127684823483104822171227052822 = 63842411721373040066027081112 := by
  rw [← show ((([(2, 1), (3163746367, 1), (20179371016422698933, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3163746367, prime_oneHundredEightDB_20179371016422698933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052823 : Nat.totient 127684823483104822171227052823 = 127226757039471226023771175200 := by
  rw [← show ((([(421, 1), (823, 1), (368516849262748308491981, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_421, prime_oneHundredEightDB_823, prime_oneHundredEightDB_368516849262748308491981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052824 : Nat.totient 127684823483104822171227052824 = 42561607827689956315737713696 := by
  rw [← show ((([(2, 3), (3, 1), (3662228970263, 1), (1452722104942727, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_3662228970263, prime_oneHundredEightDB_1452722104942727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052825 : Nat.totient 127684823483104822171227052825 = 86117604846436465392496896000 := by
  rw [← show ((([(5, 2), (7, 2), (61, 1), (36341, 1), (47019335053439553137, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_5, prime_oneHundredEightDB_7, prime_oneHundredEightDB_61, prime_oneHundredEightDB_36341, prime_oneHundredEightDB_47019335053439553137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052826 : Nat.totient 127684823483104822171227052826 = 63842411741552411085613526412 := by
  rw [← show ((([(2, 1), (63842411741552411085613526413, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_63842411741552411085613526413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052827 : Nat.totient 127684823483104822171227052827 = 85111957424745665939386854720 := by
  rw [← show ((([(3, 3), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_7561, prime_oneHundredEightDB_2416168199, prime_oneHundredEightDB_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052828 : Nat.totient 127684823483104822171227052828 = 60210778751255119943012068800 := by
  rw [← show ((([(2, 2), (19, 1), (223, 1), (211231, 1), (35666719808417469181, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_19, prime_oneHundredEightDB_223, prime_oneHundredEightDB_211231, prime_oneHundredEightDB_35666719808417469181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052829 : Nat.totient 127684823483104822171227052829 = 110929783295050570072067834880 := by
  rw [← show ((([(13, 1), (17, 1), (6128029, 1), (94281437355549787381, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_13, prime_oneHundredEightDB_17, prime_oneHundredEightDB_6128029, prime_oneHundredEightDB_94281437355549787381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052830 : Nat.totient 127684823483104822171227052830 = 34048882782012662735302136192 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (84389, 1), (50435018577897128050349, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_5, prime_oneHundredEightDB_84389, prime_oneHundredEightDB_50435018577897128050349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052831 : Nat.totient 127684823483104822171227052831 = 124709737781233920917860697880 := by
  rw [← show ((([(43, 1), (21991, 1), (135028625328865849106587, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_43, prime_oneHundredEightDB_21991, prime_oneHundredEightDB_135028625328865849106587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052832 : Nat.totient 127684823483104822171227052832 = 49747205732948037865906329600 := by
  rw [← show ((([(2, 5), (7, 1), (11, 1), (388373, 1), (133428789850506403081, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_7, prime_oneHundredEightDB_11, prime_oneHundredEightDB_388373, prime_oneHundredEightDB_133428789850506403081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052833 : Nat.totient 127684823483104822171227052833 = 85123207809988048627971901136 := by
  rw [← show ((([(3, 1), (10895267, 1), (2619477239, 1), (1491301720847, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_10895267, prime_oneHundredEightDB_2619477239, prime_oneHundredEightDB_1491301720847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052834 : Nat.totient 127684823483104822171227052834 = 63738264250946289697219376496 := by
  rw [← show ((([(2, 1), (613, 1), (104147490606121388394149309, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_613, prime_oneHundredEightDB_104147490606121388394149309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052835 : Nat.totient 127684823483104822171227052835 = 99656447561005388891062041600 := by
  rw [← show ((([(5, 1), (41, 1), (2802154111, 1), (222276424781035217, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_5, prime_oneHundredEightDB_41, prime_oneHundredEightDB_2802154111, prime_oneHundredEightDB_222276424781035217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052836 : Nat.totient 127684823483104822171227052836 = 41409965838392050300513076736 := by
  rw [← show ((([(2, 2), (3, 2), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_37, prime_oneHundredEightDB_31177, prime_oneHundredEightDB_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052837 : Nat.totient 127684823483104822171227052837 = 127684821921154764945174373036 := by
  rw [← show ((([(81747059, 1), (1561950057225970932743, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_81747059, prime_oneHundredEightDB_1561950057225970932743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052838 : Nat.totient 127684823483104822171227052838 = 63102384547650165367001439360 := by
  rw [← show ((([(2, 1), (139, 1), (229, 1), (19813, 1), (82811, 1), (1222420807213043, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_139, prime_oneHundredEightDB_229, prime_oneHundredEightDB_19813, prime_oneHundredEightDB_82811, prime_oneHundredEightDB_1222420807213043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052839 : Nat.totient 127684823483104822171227052839 = 72939717748522732251845087712 := by
  rw [← show ((([(3, 1), (7, 1), (3167, 1), (886981163, 1), (2164499678281279, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_7, prime_oneHundredEightDB_3167, prime_oneHundredEightDB_886981163, prime_oneHundredEightDB_2164499678281279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052840 : Nat.totient 127684823483104822171227052840 = 48790356351122334789453000960 := by
  rw [← show ((([(2, 3), (5, 1), (31, 1), (79, 1), (4703, 1), (277150409895147902543, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_5, prime_oneHundredEightDB_31, prime_oneHundredEightDB_79, prime_oneHundredEightDB_4703, prime_oneHundredEightDB_277150409895147902543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052841 : Nat.totient 127684823483104822171227052841 = 127684823483104822171227052840 := by
  rw [← show ((([(127684823483104822171227052841, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_127684823483104822171227052841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052842 : Nat.totient 127684823483104822171227052842 = 39287637994797652254554837376 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (11013696930283, 1), (148631737990633, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_13, prime_oneHundredEightDB_11013696930283, prime_oneHundredEightDB_148631737990633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052843 : Nat.totient 127684823483104822171227052843 = 108144962346153376429730448000 := by
  rw [← show ((([(11, 1), (29, 1), (47, 1), (71, 1), (119947828689167453892781, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_11, prime_oneHundredEightDB_29, prime_oneHundredEightDB_47, prime_oneHundredEightDB_71, prime_oneHundredEightDB_119947828689167453892781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052844 : Nat.totient 127684823483104822171227052844 = 61066614717215378736627771840 := by
  rw [← show ((([(2, 2), (23, 1), (1602869, 1), (32246411, 1), (26851715585323, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_23, prime_oneHundredEightDB_1602869, prime_oneHundredEightDB_32246411, prime_oneHundredEightDB_26851715585323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052845 : Nat.totient 127684823483104822171227052845 = 68098572204836063718166645248 := by
  rw [← show ((([(3, 2), (5, 1), (213150073, 1), (13311937837557174217, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_5, prime_oneHundredEightDB_213150073, prime_oneHundredEightDB_13311937837557174217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052846 : Nat.totient 127684823483104822171227052846 = 51296198363626252697688268800 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (349, 1), (907, 1), (19421, 1), (585911, 1), (148945151149, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_7, prime_oneHundredEightDB_17, prime_oneHundredEightDB_349, prime_oneHundredEightDB_907, prime_oneHundredEightDB_19421, prime_oneHundredEightDB_585911, prime_oneHundredEightDB_148945151149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052847 : Nat.totient 127684823483104822171227052847 = 118914263413966446828626513664 := by
  rw [← show ((([(19, 1), (59, 1), (2006689, 1), (56761465241633532463, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_19, prime_oneHundredEightDB_59, prime_oneHundredEightDB_2006689, prime_oneHundredEightDB_56761465241633532463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052848 : Nat.totient 127684823483104822171227052848 = 42537685526189720684367494400 := by
  rw [← show ((([(2, 4), (3, 1), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_2411, prime_oneHundredEightDB_7039, prime_oneHundredEightDB_188911, prime_oneHundredEightDB_829722028640579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052849 : Nat.totient 127684823483104822171227052849 = 126381263524273513103187604800 := by
  rw [← show ((([(107, 1), (1151, 1), (364747, 1), (438189827, 1), (6486735053, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_107, prime_oneHundredEightDB_1151, prime_oneHundredEightDB_364747, prime_oneHundredEightDB_438189827, prime_oneHundredEightDB_6486735053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052850 : Nat.totient 127684823483104822171227052850 = 49810208848996082927670459840 := by
  rw [← show ((([(2, 1), (5, 2), (53, 1), (167, 1), (288520672202247931694107, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_5, prime_oneHundredEightDB_53, prime_oneHundredEightDB_167, prime_oneHundredEightDB_288520672202247931694107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052851 : Nat.totient 127684823483104822171227052851 = 85123210524729020391680302152 := by
  rw [← show ((([(3, 1), (16591039, 1), (2565337097194552275503, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_16591039, prime_oneHundredEightDB_2565337097194552275503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052852 : Nat.totient 127684823483104822171227052852 = 63842406970996938295724364288 := by
  rw [← show ((([(2, 2), (13680577, 1), (614504323, 1), (3797081613103, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_13680577, prime_oneHundredEightDB_614504323, prime_oneHundredEightDB_3797081613103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052853 : Nat.totient 127684823483104822171227052853 = 109434768710739372092048921856 := by
  rw [← show ((([(7, 1), (11689, 1), (40516313, 1), (38515360242221347, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_7, prime_oneHundredEightDB_11689, prime_oneHundredEightDB_40516313, prime_oneHundredEightDB_38515360242221347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052854 : Nat.totient 127684823483104822171227052854 = 38607887789764863387978816000 := by
  rw [← show ((([(2, 1), (3, 4), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_11, prime_oneHundredEightDB_461, prime_oneHundredEightDB_69997, prime_oneHundredEightDB_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052855 : Nat.totient 127684823483104822171227052855 = 93568739386025097493058822400 := by
  rw [← show ((([(5, 1), (13, 1), (131, 2), (51461, 1), (2224360176913807027, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_5, prime_oneHundredEightDB_13, prime_oneHundredEightDB_131, prime_oneHundredEightDB_51461, prime_oneHundredEightDB_2224360176913807027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052856 : Nat.totient 127684823483104822171227052856 = 63842411741552411085613526424 := by
  rw [← show ((([(2, 3), (15960602935388102771403381607, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_15960602935388102771403381607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052857 : Nat.totient 127684823483104822171227052857 = 85123213412846527610423902160 := by
  rw [← show ((([(3, 1), (37958111, 1), (1121278343585159108429, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_37958111, prime_oneHundredEightDB_1121278343585159108429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052858 : Nat.totient 127684823483104822171227052858 = 63125070674213146084393363456 := by
  rw [← show ((([(2, 1), (89, 1), (5956133, 1), (120435602933347335617, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_89, prime_oneHundredEightDB_5956133, prime_oneHundredEightDB_120435602933347335617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052859 : Nat.totient 127684823483104822171227052859 = 127017926414274120577067045376 := by
  rw [← show ((([(193, 1), (23887, 1), (27696211172835316838549, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_193, prime_oneHundredEightDB_23887, prime_oneHundredEightDB_27696211172835316838549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052860 : Nat.totient 127684823483104822171227052860 = 29183704455931599544175901696 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (7, 1), (28403, 1), (79847, 1), (5816549, 1), (23046330287, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_5, prime_oneHundredEightDB_7, prime_oneHundredEightDB_28403, prime_oneHundredEightDB_79847, prime_oneHundredEightDB_5816549, prime_oneHundredEightDB_23046330287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052861 : Nat.totient 127684823483104822171227052861 = 127669189244892124139860419612 := by
  rw [← show ((([(8167, 1), (15634238212698031366625083, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_8167, prime_oneHundredEightDB_15634238212698031366625083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052862 : Nat.totient 127684823483104822171227052862 = 63054677833484454022626353920 := by
  rw [← show ((([(2, 1), (137, 1), (197, 1), (2712719, 1), (872002404010526741, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_137, prime_oneHundredEightDB_197, prime_oneHundredEightDB_2712719, prime_oneHundredEightDB_872002404010526741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052863 : Nat.totient 127684823483104822171227052863 = 80115967532435363412880476672 := by
  rw [← show ((([(3, 2), (17, 1), (559319647, 1), (1492065108799822793, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_17, prime_oneHundredEightDB_559319647, prime_oneHundredEightDB_1492065108799822793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052864 : Nat.totient 127684823483104822171227052864 = 63419612296819311859553241600 := by
  rw [← show ((([(2, 6), (151, 1), (31458437, 1), (419996061740133023, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_151, prime_oneHundredEightDB_31458437, prime_oneHundredEightDB_419996061740133023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052865 : Nat.totient 127684823483104822171227052865 = 92861689789423336497017395200 := by
  rw [← show ((([(5, 1), (11, 1), (5637863041, 1), (411776985049921223, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_5, prime_oneHundredEightDB_11, prime_oneHundredEightDB_5637863041, prime_oneHundredEightDB_411776985049921223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052866 : Nat.totient 127684823483104822171227052866 = 40306359037005516596795871120 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (2659, 1), (421226894041107731343491, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_19, prime_oneHundredEightDB_2659, prime_oneHundredEightDB_421226894041107731343491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052867 : Nat.totient 127684823483104822171227052867 = 104682680295528479770990311552 := by
  rw [← show ((([(7, 1), (23, 1), (34739, 1), (22829483801584955382673, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_7, prime_oneHundredEightDB_23, prime_oneHundredEightDB_34739, prime_oneHundredEightDB_22829483801584955382673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052868 : Nat.totient 127684823483104822171227052868 = 58743177576891675375899978496 := by
  rw [← show ((([(2, 2), (13, 1), (313, 1), (7844975637939593399559293, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_13, prime_oneHundredEightDB_313, prime_oneHundredEightDB_7844975637939593399559293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052869 : Nat.totient 127684823483104822171227052869 = 84651055912368304115089305600 := by
  rw [← show ((([(3, 1), (181, 1), (45377, 1), (452722021, 1), (11446482564799, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_181, prime_oneHundredEightDB_45377, prime_oneHundredEightDB_452722021, prime_oneHundredEightDB_11446482564799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052870 : Nat.totient 127684823483104822171227052870 = 50731151343622855520380143904 := by
  rw [← show ((([(2, 1), (5, 1), (149, 1), (85694512404768337027669163, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_5, prime_oneHundredEightDB_149, prime_oneHundredEightDB_85694512404768337027669163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052871 : Nat.totient 127684823483104822171227052871 = 121721690176479320124713317560 := by
  rw [← show ((([(31, 1), (67, 1), (61475601099231979860966323, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_31, prime_oneHundredEightDB_67, prime_oneHundredEightDB_61475601099231979860966323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052872 : Nat.totient 127684823483104822171227052872 = 40639589391783839901740040192 := by
  rw [← show ((([(2, 3), (3, 2), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_29, prime_oneHundredEightDB_113, prime_oneHundredEightDB_449, prime_oneHundredEightDB_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052873 : Nat.totient 127684823483104822171227052873 = 124233792264605988184046319360 := by
  rw [← show ((([(37, 1), (1379813, 1), (23093355541, 1), (108300455213, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_37, prime_oneHundredEightDB_1379813, prime_oneHundredEightDB_23093355541, prime_oneHundredEightDB_108300455213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052874 : Nat.totient 127684823483104822171227052874 = 53449460992927599978653183160 := by
  rw [← show ((([(2, 1), (7, 2), (43, 1), (30300147955174376405132191, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_7, prime_oneHundredEightDB_43, prime_oneHundredEightDB_30300147955174376405132191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052875 : Nat.totient 127684823483104822171227052875 = 68089689622579167930361241600 := by
  rw [← show ((([(3, 1), (5, 3), (10337, 1), (29669, 1), (1110223939932987497, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_5, prime_oneHundredEightDB_10337, prime_oneHundredEightDB_29669, prime_oneHundredEightDB_1110223939932987497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052876 : Nat.totient 127684823483104822171227052876 = 56541038055546174796092816000 := by
  rw [← show ((([(2, 2), (11, 1), (41, 1), (691, 1), (102429416767293794920459, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_11, prime_oneHundredEightDB_41, prime_oneHundredEightDB_691, prime_oneHundredEightDB_102429416767293794920459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052877 : Nat.totient 127684823483104822171227052877 = 127684823483104822171227052876 := by
  rw [← show ((([(127684823483104822171227052877, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_127684823483104822171227052877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052878 : Nat.totient 127684823483104822171227052878 = 42323833478595992332235234976 := by
  rw [← show ((([(2, 1), (3, 1), (179, 1), (11440553653, 1), (10391732455352099, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_179, prime_oneHundredEightDB_11440553653, prime_oneHundredEightDB_10391732455352099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052879 : Nat.totient 127684823483104822171227052879 = 127684823051121983546099657184 := by
  rw [← show ((([(295578463, 1), (431982838624831817233, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_295578463, prime_oneHundredEightDB_431982838624831817233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052880 : Nat.totient 127684823483104822171227052880 = 48069178287083044407693099008 := by
  rw [← show ((([(2, 4), (5, 1), (17, 1), (168263, 1), (412127, 1), (1353881570594633, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_5, prime_oneHundredEightDB_17, prime_oneHundredEightDB_168263, prime_oneHundredEightDB_412127, prime_oneHundredEightDB_1353881570594633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052881 : Nat.totient 127684823483104822171227052881 = 65954194384678590014502912000 := by
  rw [← show ((([(3, 3), (7, 1), (13, 1), (101, 1), (103, 1), (1163, 1), (3221, 1), (20357, 1), (53279, 1), (1229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_7, prime_oneHundredEightDB_13, prime_oneHundredEightDB_101, prime_oneHundredEightDB_103, prime_oneHundredEightDB_1163, prime_oneHundredEightDB_3221, prime_oneHundredEightDB_20357, prime_oneHundredEightDB_53279, prime_oneHundredEightDB_1229519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052882 : Nat.totient 127684823483104822171227052882 = 63842411234564998410532937412 := by
  rw [← show ((([(2, 1), (125925043, 1), (506987412674954663987, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_125925043, prime_oneHundredEightDB_506987412674954663987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052883 : Nat.totient 127684823483104822171227052883 = 127650945843549739968475330608 := by
  rw [← show ((([(3769, 1), (33877639555082202751718507, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3769, prime_oneHundredEightDB_33877639555082202751718507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052884 : Nat.totient 127684823483104822171227052884 = 42554876591290457365517262304 := by
  rw [← show ((([(2, 2), (3, 1), (6323, 1), (1682809102787506222932509, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_6323, prime_oneHundredEightDB_1682809102787506222932509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052885 : Nat.totient 127684823483104822171227052885 = 95406565498548985427281920000 := by
  rw [← show ((([(5, 1), (19, 1), (73, 1), (2617, 1), (32077, 1), (18572501, 1), (11809321819, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_5, prime_oneHundredEightDB_19, prime_oneHundredEightDB_73, prime_oneHundredEightDB_2617, prime_oneHundredEightDB_32077, prime_oneHundredEightDB_18572501, prime_oneHundredEightDB_11809321819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052886 : Nat.totient 127684823483104822171227052886 = 62785960911734478129312330240 := by
  rw [← show ((([(2, 1), (61, 1), (6373, 1), (125356337, 1), (1310054122227563, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_61, prime_oneHundredEightDB_6373, prime_oneHundredEightDB_125356337, prime_oneHundredEightDB_1310054122227563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052887 : Nat.totient 127684823483104822171227052887 = 77384741504912013437107304760 := by
  rw [← show ((([(3, 1), (11, 1), (3869237075245600671855365239, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_11, prime_oneHundredEightDB_3869237075245600671855365239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052888 : Nat.totient 127684823483104822171227052888 = 54709604882470329179655042720 := by
  rw [← show ((([(2, 3), (7, 1), (4391, 1), (519263523941442000566203, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_7, prime_oneHundredEightDB_4391, prime_oneHundredEightDB_519263523941442000566203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052889 : Nat.totient 127684823483104822171227052889 = 127684823483093958089618899380 := by
  rw [← show ((([(11765675112199, 1), (10852315933041311, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_11765675112199, prime_oneHundredEightDB_10852315933041311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052890 : Nat.totient 127684823483104822171227052890 = 31863678973284213983088082944 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (23, 1), (47, 1), (2609, 1), (1030817, 1), (487995060087097, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_5, prime_oneHundredEightDB_23, prime_oneHundredEightDB_47, prime_oneHundredEightDB_2609, prime_oneHundredEightDB_1030817, prime_oneHundredEightDB_487995060087097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052891 : Nat.totient 127684823483104822171227052891 = 126370323204246884162924576640 := by
  rw [← show ((([(109, 1), (887, 1), (281317, 1), (4694541528824955581, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_109, prime_oneHundredEightDB_887, prime_oneHundredEightDB_281317, prime_oneHundredEightDB_4694541528824955581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052892 : Nat.totient 127684823483104822171227052892 = 63842411741552411085613526444 := by
  rw [← show ((([(2, 2), (31921205870776205542806763223, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_31921205870776205542806763223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052893 : Nat.totient 127684823483104822171227052893 = 85122830825520099714994906224 := by
  rw [← show ((([(3, 1), (221197, 1), (192414941557532911343323, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_221197, prime_oneHundredEightDB_192414941557532911343323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052894 : Nat.totient 127684823483104822171227052894 = 58001243857570675161547407360 := by
  rw [← show ((([(2, 1), (13, 2), (97, 1), (227, 1), (1013, 1), (6977, 1), (565517, 1), (4292409581, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_13, prime_oneHundredEightDB_97, prime_oneHundredEightDB_227, prime_oneHundredEightDB_1013, prime_oneHundredEightDB_6977, prime_oneHundredEightDB_565517, prime_oneHundredEightDB_4292409581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052895 : Nat.totient 127684823483104822171227052895 = 86500424307971948092373047680 := by
  rw [← show ((([(5, 1), (7, 1), (83, 1), (3501634450421, 1), (12552271877179, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_5, prime_oneHundredEightDB_7, prime_oneHundredEightDB_83, prime_oneHundredEightDB_3501634450421, prime_oneHundredEightDB_12552271877179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052896 : Nat.totient 127684823483104822171227052896 = 42561240354199523985777709056 := by
  rw [← show ((([(2, 5), (3, 1), (120157, 1), (3649993, 1), (42676379, 1), (71062319, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_3, prime_oneHundredEightDB_120157, prime_oneHundredEightDB_3649993, prime_oneHundredEightDB_42676379, prime_oneHundredEightDB_71062319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052897 : Nat.totient 127684823483104822171227052897 = 120173818677790964494643020800 := by
  rw [← show ((([(17, 1), (904681, 1), (8302232466023273733161, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_17, prime_oneHundredEightDB_904681, prime_oneHundredEightDB_8302232466023273733161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052898 : Nat.totient 127684823483104822171227052898 = 58037503695076947426913688160 := by
  rw [← show ((([(2, 1), (11, 1), (55147, 1), (105243360706265091623897, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_11, prime_oneHundredEightDB_55147, prime_oneHundredEightDB_105243360706265091623897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052899 : Nat.totient 127684823483104822171227052899 = 85123215655403214780818035260 := by
  rw [← show ((([(3, 2), (14187202609233869130136339211, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_3, prime_oneHundredEightDB_14187202609233869130136339211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052900 : Nat.totient 127684823483104822171227052900 = 51073929393241928868490821120 := by
  rw [← show ((([(2, 2), (5, 2), (1276848234831048221712270529, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_2, prime_oneHundredEightDB_5, prime_oneHundredEightDB_1276848234831048221712270529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEightDB_127684823483104822171227052901 : Nat.totient 127684823483104822171227052901 = 123201585887983780033630126080 := by
  rw [← show ((([(29, 1), (2161, 1), (5669, 1), (80657, 1), (4455926248468213, 1)] : List FactorBlock).map factorBlockValue).prod) = 127684823483104822171227052901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEightDB_29, prime_oneHundredEightDB_2161, prime_oneHundredEightDB_5669, prime_oneHundredEightDB_80657, prime_oneHundredEightDB_4455926248468213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredEightDB : certifiedKill 1 127684823483104822171227052799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredEightDB_127684823483104822171227052800, phi_oneHundredEightDB_127684823483104822171227052801, phi_oneHundredEightDB_127684823483104822171227052802,
    phi_oneHundredEightDB_127684823483104822171227052803, phi_oneHundredEightDB_127684823483104822171227052804, phi_oneHundredEightDB_127684823483104822171227052805,
    phi_oneHundredEightDB_127684823483104822171227052806, phi_oneHundredEightDB_127684823483104822171227052807, phi_oneHundredEightDB_127684823483104822171227052808,
    phi_oneHundredEightDB_127684823483104822171227052809, phi_oneHundredEightDB_127684823483104822171227052810, phi_oneHundredEightDB_127684823483104822171227052811,
    phi_oneHundredEightDB_127684823483104822171227052812, phi_oneHundredEightDB_127684823483104822171227052813, phi_oneHundredEightDB_127684823483104822171227052814,
    phi_oneHundredEightDB_127684823483104822171227052815, phi_oneHundredEightDB_127684823483104822171227052816, phi_oneHundredEightDB_127684823483104822171227052817,
    phi_oneHundredEightDB_127684823483104822171227052818, phi_oneHundredEightDB_127684823483104822171227052819, phi_oneHundredEightDB_127684823483104822171227052820,
    phi_oneHundredEightDB_127684823483104822171227052821, phi_oneHundredEightDB_127684823483104822171227052822, phi_oneHundredEightDB_127684823483104822171227052823,
    phi_oneHundredEightDB_127684823483104822171227052824, phi_oneHundredEightDB_127684823483104822171227052825, phi_oneHundredEightDB_127684823483104822171227052826,
    phi_oneHundredEightDB_127684823483104822171227052827, phi_oneHundredEightDB_127684823483104822171227052828, phi_oneHundredEightDB_127684823483104822171227052829,
    phi_oneHundredEightDB_127684823483104822171227052830, phi_oneHundredEightDB_127684823483104822171227052831, phi_oneHundredEightDB_127684823483104822171227052832,
    phi_oneHundredEightDB_127684823483104822171227052833, phi_oneHundredEightDB_127684823483104822171227052834, phi_oneHundredEightDB_127684823483104822171227052835,
    phi_oneHundredEightDB_127684823483104822171227052836, phi_oneHundredEightDB_127684823483104822171227052837, phi_oneHundredEightDB_127684823483104822171227052838,
    phi_oneHundredEightDB_127684823483104822171227052839, phi_oneHundredEightDB_127684823483104822171227052840, phi_oneHundredEightDB_127684823483104822171227052841,
    phi_oneHundredEightDB_127684823483104822171227052842, phi_oneHundredEightDB_127684823483104822171227052843, phi_oneHundredEightDB_127684823483104822171227052844,
    phi_oneHundredEightDB_127684823483104822171227052845, phi_oneHundredEightDB_127684823483104822171227052846, phi_oneHundredEightDB_127684823483104822171227052847,
    phi_oneHundredEightDB_127684823483104822171227052848, phi_oneHundredEightDB_127684823483104822171227052849, phi_oneHundredEightDB_127684823483104822171227052850,
    phi_oneHundredEightDB_127684823483104822171227052851, phi_oneHundredEightDB_127684823483104822171227052852, phi_oneHundredEightDB_127684823483104822171227052853,
    phi_oneHundredEightDB_127684823483104822171227052854, phi_oneHundredEightDB_127684823483104822171227052855, phi_oneHundredEightDB_127684823483104822171227052856,
    phi_oneHundredEightDB_127684823483104822171227052857, phi_oneHundredEightDB_127684823483104822171227052858, phi_oneHundredEightDB_127684823483104822171227052859,
    phi_oneHundredEightDB_127684823483104822171227052860, phi_oneHundredEightDB_127684823483104822171227052861, phi_oneHundredEightDB_127684823483104822171227052862,
    phi_oneHundredEightDB_127684823483104822171227052863, phi_oneHundredEightDB_127684823483104822171227052864, phi_oneHundredEightDB_127684823483104822171227052865,
    phi_oneHundredEightDB_127684823483104822171227052866, phi_oneHundredEightDB_127684823483104822171227052867, phi_oneHundredEightDB_127684823483104822171227052868,
    phi_oneHundredEightDB_127684823483104822171227052869, phi_oneHundredEightDB_127684823483104822171227052870, phi_oneHundredEightDB_127684823483104822171227052871,
    phi_oneHundredEightDB_127684823483104822171227052872, phi_oneHundredEightDB_127684823483104822171227052873, phi_oneHundredEightDB_127684823483104822171227052874,
    phi_oneHundredEightDB_127684823483104822171227052875, phi_oneHundredEightDB_127684823483104822171227052876, phi_oneHundredEightDB_127684823483104822171227052877,
    phi_oneHundredEightDB_127684823483104822171227052878, phi_oneHundredEightDB_127684823483104822171227052879, phi_oneHundredEightDB_127684823483104822171227052880,
    phi_oneHundredEightDB_127684823483104822171227052881, phi_oneHundredEightDB_127684823483104822171227052882, phi_oneHundredEightDB_127684823483104822171227052883,
    phi_oneHundredEightDB_127684823483104822171227052884, phi_oneHundredEightDB_127684823483104822171227052885, phi_oneHundredEightDB_127684823483104822171227052886,
    phi_oneHundredEightDB_127684823483104822171227052887, phi_oneHundredEightDB_127684823483104822171227052888, phi_oneHundredEightDB_127684823483104822171227052889,
    phi_oneHundredEightDB_127684823483104822171227052890, phi_oneHundredEightDB_127684823483104822171227052891, phi_oneHundredEightDB_127684823483104822171227052892,
    phi_oneHundredEightDB_127684823483104822171227052893, phi_oneHundredEightDB_127684823483104822171227052894, phi_oneHundredEightDB_127684823483104822171227052895,
    phi_oneHundredEightDB_127684823483104822171227052896, phi_oneHundredEightDB_127684823483104822171227052897, phi_oneHundredEightDB_127684823483104822171227052898,
    phi_oneHundredEightDB_127684823483104822171227052899, phi_oneHundredEightDB_127684823483104822171227052900, phi_oneHundredEightDB_127684823483104822171227052901
    ]

end TotientTailPeriodKiller
end Erdos249257
