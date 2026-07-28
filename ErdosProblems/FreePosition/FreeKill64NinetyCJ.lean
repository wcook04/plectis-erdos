import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def ninetyCJFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem ninetyCJFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : ninetyCJFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [ninetyCJFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [ninetyCJFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then ninetyCJFastPow a n * ninetyCJFastPow a n * a else ninetyCJFastPow a n * ninetyCJFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_ninetyCJ_2 : Nat.Prime 2 := by norm_num

private theorem prime_ninetyCJ_3 : Nat.Prime 3 := by norm_num

private theorem prime_ninetyCJ_5 : Nat.Prime 5 := by norm_num

private theorem prime_ninetyCJ_7 : Nat.Prime 7 := by norm_num

private theorem prime_ninetyCJ_11 : Nat.Prime 11 := by norm_num

private theorem prime_ninetyCJ_13 : Nat.Prime 13 := by norm_num

private theorem prime_ninetyCJ_17 : Nat.Prime 17 := by norm_num

private theorem prime_ninetyCJ_19 : Nat.Prime 19 := by norm_num

private theorem prime_ninetyCJ_23 : Nat.Prime 23 := by norm_num

private theorem prime_ninetyCJ_29 : Nat.Prime 29 := by norm_num

private theorem prime_ninetyCJ_31 : Nat.Prime 31 := by norm_num

private theorem prime_ninetyCJ_37 : Nat.Prime 37 := by norm_num

private theorem prime_ninetyCJ_41 : Nat.Prime 41 := by norm_num

private theorem prime_ninetyCJ_43 : Nat.Prime 43 := by norm_num

private theorem prime_ninetyCJ_47 : Nat.Prime 47 := by norm_num

private theorem prime_ninetyCJ_53 : Nat.Prime 53 := by norm_num

private theorem prime_ninetyCJ_59 : Nat.Prime 59 := by norm_num

private theorem prime_ninetyCJ_61 : Nat.Prime 61 := by norm_num

private theorem prime_ninetyCJ_67 : Nat.Prime 67 := by norm_num

private theorem prime_ninetyCJ_71 : Nat.Prime 71 := by norm_num

private theorem prime_ninetyCJ_73 : Nat.Prime 73 := by norm_num

private theorem prime_ninetyCJ_79 : Nat.Prime 79 := by norm_num

private theorem prime_ninetyCJ_83 : Nat.Prime 83 := by norm_num

private theorem prime_ninetyCJ_89 : Nat.Prime 89 := by norm_num

private theorem prime_ninetyCJ_97 : Nat.Prime 97 := by norm_num

private theorem prime_ninetyCJ_101 : Nat.Prime 101 := by norm_num

private theorem prime_ninetyCJ_103 : Nat.Prime 103 := by norm_num

private theorem prime_ninetyCJ_107 : Nat.Prime 107 := by norm_num

private theorem prime_ninetyCJ_109 : Nat.Prime 109 := by norm_num

private theorem prime_ninetyCJ_113 : Nat.Prime 113 := by norm_num

private theorem prime_ninetyCJ_127 : Nat.Prime 127 := by norm_num

private theorem prime_ninetyCJ_131 : Nat.Prime 131 := by norm_num

private theorem prime_ninetyCJ_137 : Nat.Prime 137 := by norm_num

private theorem prime_ninetyCJ_139 : Nat.Prime 139 := by norm_num

private theorem prime_ninetyCJ_149 : Nat.Prime 149 := by norm_num

private theorem prime_ninetyCJ_151 : Nat.Prime 151 := by norm_num

private theorem prime_ninetyCJ_157 : Nat.Prime 157 := by norm_num

private theorem prime_ninetyCJ_163 : Nat.Prime 163 := by norm_num

private theorem prime_ninetyCJ_167 : Nat.Prime 167 := by norm_num

private theorem prime_ninetyCJ_179 : Nat.Prime 179 := by norm_num

private theorem prime_ninetyCJ_181 : Nat.Prime 181 := by norm_num

private theorem prime_ninetyCJ_193 : Nat.Prime 193 := by norm_num

private theorem prime_ninetyCJ_197 : Nat.Prime 197 := by norm_num

private theorem prime_ninetyCJ_223 : Nat.Prime 223 := by norm_num

private theorem prime_ninetyCJ_227 : Nat.Prime 227 := by norm_num

private theorem prime_ninetyCJ_229 : Nat.Prime 229 := by norm_num

private theorem prime_ninetyCJ_239 : Nat.Prime 239 := by norm_num

private theorem prime_ninetyCJ_241 : Nat.Prime 241 := by norm_num

private theorem prime_ninetyCJ_257 : Nat.Prime 257 := by norm_num

private theorem prime_ninetyCJ_263 : Nat.Prime 263 := by norm_num

private theorem prime_ninetyCJ_269 : Nat.Prime 269 := by norm_num

private theorem prime_ninetyCJ_271 : Nat.Prime 271 := by norm_num

private theorem prime_ninetyCJ_281 : Nat.Prime 281 := by norm_num

private theorem prime_ninetyCJ_283 : Nat.Prime 283 := by norm_num

private theorem prime_ninetyCJ_311 : Nat.Prime 311 := by norm_num

private theorem prime_ninetyCJ_313 : Nat.Prime 313 := by norm_num

private theorem prime_ninetyCJ_331 : Nat.Prime 331 := by norm_num

private theorem prime_ninetyCJ_337 : Nat.Prime 337 := by norm_num

private theorem prime_ninetyCJ_347 : Nat.Prime 347 := by norm_num

private theorem prime_ninetyCJ_349 : Nat.Prime 349 := by norm_num

private theorem prime_ninetyCJ_359 : Nat.Prime 359 := by norm_num

private theorem prime_ninetyCJ_373 : Nat.Prime 373 := by norm_num

private theorem prime_ninetyCJ_379 : Nat.Prime 379 := by norm_num

private theorem prime_ninetyCJ_383 : Nat.Prime 383 := by norm_num

private theorem prime_ninetyCJ_401 : Nat.Prime 401 := by norm_num

private theorem prime_ninetyCJ_409 : Nat.Prime 409 := by norm_num

private theorem prime_ninetyCJ_419 : Nat.Prime 419 := by norm_num

private theorem prime_ninetyCJ_421 : Nat.Prime 421 := by norm_num

private theorem prime_ninetyCJ_443 : Nat.Prime 443 := by norm_num

private theorem prime_ninetyCJ_449 : Nat.Prime 449 := by norm_num

private theorem prime_ninetyCJ_461 : Nat.Prime 461 := by norm_num

private theorem prime_ninetyCJ_467 : Nat.Prime 467 := by norm_num

private theorem prime_ninetyCJ_499 : Nat.Prime 499 := by norm_num

private theorem prime_ninetyCJ_503 : Nat.Prime 503 := by norm_num

private theorem prime_ninetyCJ_509 : Nat.Prime 509 := by norm_num

private theorem prime_ninetyCJ_521 : Nat.Prime 521 := by norm_num

private theorem prime_ninetyCJ_523 : Nat.Prime 523 := by norm_num

private theorem prime_ninetyCJ_541 : Nat.Prime 541 := by norm_num

private theorem prime_ninetyCJ_557 : Nat.Prime 557 := by norm_num

private theorem prime_ninetyCJ_563 : Nat.Prime 563 := by norm_num

private theorem prime_ninetyCJ_571 : Nat.Prime 571 := by norm_num

private theorem prime_ninetyCJ_601 : Nat.Prime 601 := by norm_num

private theorem prime_ninetyCJ_617 : Nat.Prime 617 := by norm_num

private theorem prime_ninetyCJ_619 : Nat.Prime 619 := by norm_num

private theorem prime_ninetyCJ_643 : Nat.Prime 643 := by norm_num

private theorem prime_ninetyCJ_653 : Nat.Prime 653 := by norm_num

private theorem prime_ninetyCJ_661 : Nat.Prime 661 := by norm_num

private theorem prime_ninetyCJ_677 : Nat.Prime 677 := by norm_num

private theorem prime_ninetyCJ_701 : Nat.Prime 701 := by norm_num

private theorem prime_ninetyCJ_727 : Nat.Prime 727 := by norm_num

private theorem prime_ninetyCJ_733 : Nat.Prime 733 := by norm_num

private theorem prime_ninetyCJ_743 : Nat.Prime 743 := by norm_num

private theorem prime_ninetyCJ_797 : Nat.Prime 797 := by norm_num

private theorem prime_ninetyCJ_823 : Nat.Prime 823 := by norm_num

private theorem prime_ninetyCJ_859 : Nat.Prime 859 := by norm_num

private theorem prime_ninetyCJ_883 : Nat.Prime 883 := by norm_num

private theorem prime_ninetyCJ_887 : Nat.Prime 887 := by norm_num

private theorem prime_ninetyCJ_929 : Nat.Prime 929 := by norm_num

private theorem prime_ninetyCJ_971 : Nat.Prime 971 := by norm_num

private theorem prime_ninetyCJ_977 : Nat.Prime 977 := by norm_num

private theorem prime_ninetyCJ_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_ninetyCJ_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_ninetyCJ_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_ninetyCJ_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_ninetyCJ_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_ninetyCJ_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_ninetyCJ_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_ninetyCJ_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_ninetyCJ_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_ninetyCJ_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_ninetyCJ_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_ninetyCJ_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_ninetyCJ_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_ninetyCJ_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_ninetyCJ_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_ninetyCJ_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_ninetyCJ_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_ninetyCJ_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_ninetyCJ_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_ninetyCJ_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_ninetyCJ_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_ninetyCJ_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_ninetyCJ_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_ninetyCJ_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_ninetyCJ_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_ninetyCJ_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_ninetyCJ_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_ninetyCJ_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_ninetyCJ_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_ninetyCJ_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_ninetyCJ_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_ninetyCJ_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_ninetyCJ_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_ninetyCJ_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_ninetyCJ_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_ninetyCJ_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_ninetyCJ_2089 : Nat.Prime 2089 := by norm_num

private theorem prime_ninetyCJ_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_ninetyCJ_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_ninetyCJ_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_ninetyCJ_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_ninetyCJ_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_ninetyCJ_2341 : Nat.Prime 2341 := by norm_num

private theorem prime_ninetyCJ_2371 : Nat.Prime 2371 := by norm_num

private theorem prime_ninetyCJ_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_ninetyCJ_2437 : Nat.Prime 2437 := by norm_num

private theorem prime_ninetyCJ_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_ninetyCJ_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_ninetyCJ_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_ninetyCJ_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_ninetyCJ_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_ninetyCJ_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_ninetyCJ_3167 : Nat.Prime 3167 := by norm_num

private theorem prime_ninetyCJ_3181 : Nat.Prime 3181 := by norm_num

private theorem prime_ninetyCJ_3209 : Nat.Prime 3209 := by norm_num

private theorem prime_ninetyCJ_3251 : Nat.Prime 3251 := by norm_num

private theorem prime_ninetyCJ_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_ninetyCJ_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_ninetyCJ_3571 : Nat.Prime 3571 := by norm_num

private theorem prime_ninetyCJ_3643 : Nat.Prime 3643 := by norm_num

private theorem prime_ninetyCJ_3767 : Nat.Prime 3767 := by norm_num

private theorem prime_ninetyCJ_3833 : Nat.Prime 3833 := by norm_num

private theorem prime_ninetyCJ_3851 : Nat.Prime 3851 := by norm_num

private theorem prime_ninetyCJ_4049 : Nat.Prime 4049 := by norm_num

private theorem prime_ninetyCJ_4133 : Nat.Prime 4133 := by norm_num

private theorem prime_ninetyCJ_4157 : Nat.Prime 4157 := by norm_num

private theorem prime_ninetyCJ_4219 : Nat.Prime 4219 := by norm_num

private theorem prime_ninetyCJ_4241 : Nat.Prime 4241 := by norm_num

private theorem prime_ninetyCJ_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_ninetyCJ_4649 : Nat.Prime 4649 := by norm_num

private theorem prime_ninetyCJ_4663 : Nat.Prime 4663 := by norm_num

private theorem prime_ninetyCJ_4679 : Nat.Prime 4679 := by norm_num

private theorem prime_ninetyCJ_4967 : Nat.Prime 4967 := by norm_num

private theorem prime_ninetyCJ_5107 : Nat.Prime 5107 := by norm_num

private theorem prime_ninetyCJ_5653 : Nat.Prime 5653 := by norm_num

private theorem prime_ninetyCJ_5801 : Nat.Prime 5801 := by norm_num

private theorem prime_ninetyCJ_6143 : Nat.Prime 6143 := by norm_num

private theorem prime_ninetyCJ_6221 : Nat.Prime 6221 := by norm_num

private theorem prime_ninetyCJ_6389 : Nat.Prime 6389 := by norm_num

private theorem prime_ninetyCJ_6691 : Nat.Prime 6691 := by norm_num

private theorem prime_ninetyCJ_6701 : Nat.Prime 6701 := by norm_num

private theorem prime_ninetyCJ_6833 : Nat.Prime 6833 := by norm_num

private theorem prime_ninetyCJ_6997 : Nat.Prime 6997 := by norm_num

private theorem prime_ninetyCJ_7253 : Nat.Prime 7253 := by norm_num

private theorem prime_ninetyCJ_7283 : Nat.Prime 7283 := by norm_num

private theorem prime_ninetyCJ_7333 : Nat.Prime 7333 := by norm_num

private theorem prime_ninetyCJ_7393 : Nat.Prime 7393 := by norm_num

private theorem prime_ninetyCJ_7639 : Nat.Prime 7639 := by norm_num

private theorem prime_ninetyCJ_7927 : Nat.Prime 7927 := by norm_num

private theorem prime_ninetyCJ_8017 : Nat.Prime 8017 := by norm_num

private theorem prime_ninetyCJ_8111 : Nat.Prime 8111 := by norm_num

private theorem prime_ninetyCJ_8179 : Nat.Prime 8179 := by norm_num

private theorem prime_ninetyCJ_8609 : Nat.Prime 8609 := by norm_num

private theorem prime_ninetyCJ_8663 : Nat.Prime 8663 := by norm_num

private theorem prime_ninetyCJ_9341 : Nat.Prime 9341 := by norm_num

private theorem prime_ninetyCJ_9413 : Nat.Prime 9413 := by norm_num

private theorem prime_ninetyCJ_9629 : Nat.Prime 9629 := by norm_num

private theorem prime_ninetyCJ_9649 : Nat.Prime 9649 := by norm_num

private theorem prime_ninetyCJ_10091 : Nat.Prime 10091 := by norm_num

private theorem prime_ninetyCJ_10133 : Nat.Prime 10133 := by norm_num

private theorem prime_ninetyCJ_10663 : Nat.Prime 10663 := by norm_num

private theorem prime_ninetyCJ_12289 : Nat.Prime 12289 := by norm_num

private theorem prime_ninetyCJ_12401 : Nat.Prime 12401 := by norm_num

private theorem prime_ninetyCJ_12451 : Nat.Prime 12451 := by norm_num

private theorem prime_ninetyCJ_12647 : Nat.Prime 12647 := by norm_num

private theorem prime_ninetyCJ_12823 : Nat.Prime 12823 := by norm_num

private theorem prime_ninetyCJ_13001 : Nat.Prime 13001 := by norm_num

private theorem prime_ninetyCJ_13033 : Nat.Prime 13033 := by norm_num

private theorem prime_ninetyCJ_13043 : Nat.Prime 13043 := by norm_num

private theorem prime_ninetyCJ_13759 : Nat.Prime 13759 := by norm_num

private theorem prime_ninetyCJ_14843 : Nat.Prime 14843 := by norm_num

private theorem prime_ninetyCJ_14983 : Nat.Prime 14983 := by norm_num

private theorem prime_ninetyCJ_15551 : Nat.Prime 15551 := by norm_num

private theorem prime_ninetyCJ_16253 : Nat.Prime 16253 := by norm_num

private theorem prime_ninetyCJ_17077 : Nat.Prime 17077 := by norm_num

private theorem prime_ninetyCJ_18289 : Nat.Prime 18289 := by norm_num

private theorem prime_ninetyCJ_18899 : Nat.Prime 18899 := by norm_num

private theorem prime_ninetyCJ_19309 : Nat.Prime 19309 := by norm_num

private theorem prime_ninetyCJ_21529 : Nat.Prime 21529 := by norm_num

private theorem prime_ninetyCJ_22153 : Nat.Prime 22153 := by norm_num

private theorem prime_ninetyCJ_22433 : Nat.Prime 22433 := by norm_num

private theorem prime_ninetyCJ_23459 : Nat.Prime 23459 := by norm_num

private theorem prime_ninetyCJ_23767 : Nat.Prime 23767 := by norm_num

private theorem prime_ninetyCJ_23879 : Nat.Prime 23879 := by norm_num

private theorem prime_ninetyCJ_24691 : Nat.Prime 24691 := by norm_num

private theorem prime_ninetyCJ_25357 : Nat.Prime 25357 := by norm_num

private theorem prime_ninetyCJ_26591 : Nat.Prime 26591 := by norm_num

private theorem prime_ninetyCJ_28069 : Nat.Prime 28069 := by norm_num

private theorem prime_ninetyCJ_28087 : Nat.Prime 28087 := by norm_num

private theorem prime_ninetyCJ_29917 : Nat.Prime 29917 := by norm_num

private theorem prime_ninetyCJ_34127 : Nat.Prime 34127 := by norm_num

private theorem prime_ninetyCJ_34297 : Nat.Prime 34297 := by norm_num

private theorem prime_ninetyCJ_35129 : Nat.Prime 35129 := by norm_num

private theorem prime_ninetyCJ_37087 : Nat.Prime 37087 := by norm_num

private theorem prime_ninetyCJ_40471 : Nat.Prime 40471 := by norm_num

private theorem prime_ninetyCJ_43321 : Nat.Prime 43321 := by norm_num

private theorem prime_ninetyCJ_45841 : Nat.Prime 45841 := by norm_num

private theorem prime_ninetyCJ_46141 : Nat.Prime 46141 := by norm_num

private theorem prime_ninetyCJ_48131 : Nat.Prime 48131 := by norm_num

private theorem prime_ninetyCJ_51487 : Nat.Prime 51487 := by norm_num

private theorem prime_ninetyCJ_53597 : Nat.Prime 53597 := by norm_num

private theorem prime_ninetyCJ_55207 : Nat.Prime 55207 := by norm_num

private theorem prime_ninetyCJ_57037 : Nat.Prime 57037 := by norm_num

private theorem prime_ninetyCJ_57269 : Nat.Prime 57269 := by norm_num

private theorem prime_ninetyCJ_59669 : Nat.Prime 59669 := by norm_num

private theorem prime_ninetyCJ_62497 : Nat.Prime 62497 := by norm_num

private theorem prime_ninetyCJ_64381 : Nat.Prime 64381 := by norm_num

private theorem prime_ninetyCJ_65599 : Nat.Prime 65599 := by norm_num

private theorem prime_ninetyCJ_66629 : Nat.Prime 66629 := by norm_num

private theorem prime_ninetyCJ_68087 : Nat.Prime 68087 := by norm_num

private theorem prime_ninetyCJ_70393 : Nat.Prime 70393 := by norm_num

private theorem prime_ninetyCJ_71419 : Nat.Prime 71419 := by norm_num

private theorem prime_ninetyCJ_75707 : Nat.Prime 75707 := by norm_num

private theorem prime_ninetyCJ_80251 : Nat.Prime 80251 := by norm_num

private theorem prime_ninetyCJ_80537 : Nat.Prime 80537 := by norm_num

private theorem prime_ninetyCJ_85691 : Nat.Prime 85691 := by norm_num

private theorem prime_ninetyCJ_85703 : Nat.Prime 85703 := by norm_num

private theorem prime_ninetyCJ_86399 : Nat.Prime 86399 := by norm_num

private theorem prime_ninetyCJ_88661 : Nat.Prime 88661 := by norm_num

private theorem prime_ninetyCJ_90007 : Nat.Prime 90007 := by norm_num

private theorem prime_ninetyCJ_91703 : Nat.Prime 91703 := by norm_num

private theorem prime_ninetyCJ_99349 : Nat.Prime 99349 := by norm_num

private theorem prime_ninetyCJ_104281 : Nat.Prime 104281 := by norm_num

private theorem prime_ninetyCJ_105899 : Nat.Prime 105899 := by norm_num

private theorem prime_ninetyCJ_111301 : Nat.Prime 111301 := by norm_num

private theorem prime_ninetyCJ_113933 : Nat.Prime 113933 := by norm_num

private theorem prime_ninetyCJ_124337 : Nat.Prime 124337 := by norm_num

private theorem prime_ninetyCJ_138319 : Nat.Prime 138319 := by norm_num

private theorem prime_ninetyCJ_144427 : Nat.Prime 144427 := by norm_num

private theorem prime_ninetyCJ_146837 : Nat.Prime 146837 := by norm_num

private theorem prime_ninetyCJ_150797 : Nat.Prime 150797 := by norm_num

private theorem prime_ninetyCJ_152833 : Nat.Prime 152833 := by norm_num

private theorem prime_ninetyCJ_156577 : Nat.Prime 156577 := by norm_num

private theorem prime_ninetyCJ_156631 : Nat.Prime 156631 := by norm_num

private theorem prime_ninetyCJ_157253 : Nat.Prime 157253 := by norm_num

private theorem prime_ninetyCJ_167899 : Nat.Prime 167899 := by norm_num

private theorem prime_ninetyCJ_168599 : Nat.Prime 168599 := by norm_num

private theorem prime_ninetyCJ_175081 : Nat.Prime 175081 := by norm_num

private theorem prime_ninetyCJ_176521 : Nat.Prime 176521 := by norm_num

private theorem prime_ninetyCJ_185621 : Nat.Prime 185621 := by norm_num

private theorem prime_ninetyCJ_188711 : Nat.Prime 188711 := by norm_num

private theorem prime_ninetyCJ_189877 : Nat.Prime 189877 := by norm_num

private theorem prime_ninetyCJ_204301 : Nat.Prime 204301 := by norm_num

private theorem prime_ninetyCJ_208141 : Nat.Prime 208141 := by norm_num

private theorem prime_ninetyCJ_224197 : Nat.Prime 224197 := by norm_num

private theorem prime_ninetyCJ_227393 : Nat.Prime 227393 := by norm_num

private theorem prime_ninetyCJ_240797 : Nat.Prime 240797 := by norm_num

private theorem prime_ninetyCJ_243431 : Nat.Prime 243431 := by norm_num

private theorem prime_ninetyCJ_246781 : Nat.Prime 246781 := by norm_num

private theorem prime_ninetyCJ_253103 : Nat.Prime 253103 := by norm_num

private theorem prime_ninetyCJ_274853 : Nat.Prime 274853 := by norm_num

private theorem prime_ninetyCJ_277213 : Nat.Prime 277213 := by norm_num

private theorem prime_ninetyCJ_297457 : Nat.Prime 297457 := by norm_num

private theorem prime_ninetyCJ_309823 : Nat.Prime 309823 := by norm_num

private theorem prime_ninetyCJ_324997 : Nat.Prime 324997 := by norm_num

private theorem prime_ninetyCJ_333769 : Nat.Prime 333769 := by norm_num

private theorem prime_ninetyCJ_348367 : Nat.Prime 348367 := by norm_num

private theorem prime_ninetyCJ_386173 : Nat.Prime 386173 := by norm_num

private theorem prime_ninetyCJ_388937 : Nat.Prime 388937 := by norm_num

private theorem prime_ninetyCJ_407153 : Nat.Prime 407153 := by norm_num

private theorem prime_ninetyCJ_407369 : Nat.Prime 407369 := by norm_num

private theorem prime_ninetyCJ_419687 : Nat.Prime 419687 := by norm_num

private theorem prime_ninetyCJ_424597 : Nat.Prime 424597 := by norm_num

private theorem prime_ninetyCJ_427717 : Nat.Prime 427717 := by norm_num

private theorem prime_ninetyCJ_430691 : Nat.Prime 430691 := by norm_num

private theorem prime_ninetyCJ_442469 : Nat.Prime 442469 := by norm_num

private theorem prime_ninetyCJ_465011 : Nat.Prime 465011 := by norm_num

private theorem prime_ninetyCJ_474433 : Nat.Prime 474433 := by norm_num

private theorem prime_ninetyCJ_498053 : Nat.Prime 498053 := by norm_num

private theorem prime_ninetyCJ_507029 : Nat.Prime 507029 := by norm_num

private theorem prime_ninetyCJ_510067 : Nat.Prime 510067 := by norm_num

private theorem prime_ninetyCJ_517169 : Nat.Prime 517169 := by norm_num

private theorem prime_ninetyCJ_537403 : Nat.Prime 537403 := by norm_num

private theorem prime_ninetyCJ_578959 : Nat.Prime 578959 := by norm_num

private theorem prime_ninetyCJ_584677 : Nat.Prime 584677 := by norm_num

private theorem prime_ninetyCJ_607307 : Nat.Prime 607307 := by norm_num

private theorem prime_ninetyCJ_619669 : Nat.Prime 619669 := by norm_num

private theorem prime_ninetyCJ_639007 : Nat.Prime 639007 := by norm_num

private theorem prime_ninetyCJ_651863 : Nat.Prime 651863 := by norm_num

private theorem prime_ninetyCJ_688447 : Nat.Prime 688447 := by norm_num

private theorem prime_ninetyCJ_691843 : Nat.Prime 691843 := by norm_num

private theorem prime_ninetyCJ_725639 : Nat.Prime 725639 := by norm_num

private theorem prime_ninetyCJ_736367 : Nat.Prime 736367 := by norm_num

private theorem prime_ninetyCJ_774853 : Nat.Prime 774853 := by norm_num

private theorem prime_ninetyCJ_795323 : Nat.Prime 795323 := by norm_num

private theorem prime_ninetyCJ_833429 : Nat.Prime 833429 := by norm_num

private theorem prime_ninetyCJ_834107 : Nat.Prime 834107 := by norm_num

private theorem prime_ninetyCJ_838367 : Nat.Prime 838367 := by norm_num

private theorem prime_ninetyCJ_841411 : Nat.Prime 841411 := by norm_num

private theorem prime_ninetyCJ_854263 : Nat.Prime 854263 := by norm_num

private theorem prime_ninetyCJ_878597 : Nat.Prime 878597 := by norm_num

private theorem prime_ninetyCJ_885371 : Nat.Prime 885371 := by norm_num

private theorem prime_ninetyCJ_917041 : Nat.Prime 917041 := by norm_num

private theorem prime_ninetyCJ_926179 : Nat.Prime 926179 := by norm_num

private theorem prime_ninetyCJ_961777 : Nat.Prime 961777 := by norm_num

private theorem prime_ninetyCJ_996049 : Nat.Prime 996049 := by norm_num

private theorem prime_ninetyCJ_1038449 : Nat.Prime 1038449 := by norm_num

private theorem prime_ninetyCJ_1063541 : Nat.Prime 1063541 := by norm_num

private theorem prime_ninetyCJ_1074389 : Nat.Prime 1074389 := by norm_num

private theorem prime_ninetyCJ_1100947 : Nat.Prime 1100947 := by norm_num

private theorem prime_ninetyCJ_1121831 : Nat.Prime 1121831 := by norm_num

private theorem prime_ninetyCJ_1126693 : Nat.Prime 1126693 := by norm_num

private theorem prime_ninetyCJ_1142159 : Nat.Prime 1142159 := by norm_num

private theorem prime_ninetyCJ_1161239 : Nat.Prime 1161239 := by norm_num

private theorem prime_ninetyCJ_1270579 : Nat.Prime 1270579 := by norm_num

private theorem prime_ninetyCJ_1422541 : Nat.Prime 1422541 := by norm_num

private theorem prime_ninetyCJ_1513661 : Nat.Prime 1513661 := by norm_num

private theorem prime_ninetyCJ_1636711 : Nat.Prime 1636711 := by norm_num

private theorem prime_ninetyCJ_1651477 : Nat.Prime 1651477 := by norm_num

private theorem prime_ninetyCJ_1757999 : Nat.Prime 1757999 := by norm_num

private theorem prime_ninetyCJ_1803667 : Nat.Prime 1803667 := by norm_num

private theorem prime_ninetyCJ_1810747 : Nat.Prime 1810747 := by norm_num

private theorem prime_ninetyCJ_2074481 : Nat.Prime 2074481 := by norm_num

private theorem prime_ninetyCJ_2153471 : Nat.Prime 2153471 := by norm_num

private theorem prime_ninetyCJ_2188583 : Nat.Prime 2188583 := by norm_num

private theorem prime_ninetyCJ_2267483 : Nat.Prime 2267483 := by norm_num

private theorem prime_ninetyCJ_2300611 : Nat.Prime 2300611 := by norm_num

private theorem prime_ninetyCJ_2331151 : Nat.Prime 2331151 := by norm_num

private theorem prime_ninetyCJ_2581573 : Nat.Prime 2581573 := by norm_num

private theorem prime_ninetyCJ_2646107 : Nat.Prime 2646107 := by norm_num

private theorem prime_ninetyCJ_2930303 : Nat.Prime 2930303 := by norm_num

private theorem prime_ninetyCJ_3237653 : Nat.Prime 3237653 := by norm_num

private theorem prime_ninetyCJ_3278701 : Nat.Prime 3278701 := by norm_num

private theorem prime_ninetyCJ_3460543 : Nat.Prime 3460543 := by norm_num

private theorem prime_ninetyCJ_3620501 : Nat.Prime 3620501 := by norm_num

private theorem prime_ninetyCJ_3692701 : Nat.Prime 3692701 := by norm_num

private theorem prime_ninetyCJ_3737563 : Nat.Prime 3737563 := by norm_num

private theorem prime_ninetyCJ_3751003 : Nat.Prime 3751003 := by norm_num

private theorem prime_ninetyCJ_3826723 : Nat.Prime 3826723 := by norm_num

private theorem prime_ninetyCJ_3843551 : Nat.Prime 3843551 := by norm_num

private theorem prime_ninetyCJ_4093247 : Nat.Prime 4093247 := by norm_num

private theorem prime_ninetyCJ_4209259 : Nat.Prime 4209259 := by norm_num

private theorem prime_ninetyCJ_4437259 : Nat.Prime 4437259 := by norm_num

private theorem prime_ninetyCJ_4453321 : Nat.Prime 4453321 := by norm_num

private theorem prime_ninetyCJ_4765759 : Nat.Prime 4765759 := by norm_num

private theorem prime_ninetyCJ_4893197 : Nat.Prime 4893197 := by norm_num

private theorem prime_ninetyCJ_4959701 : Nat.Prime 4959701 := by norm_num

private theorem prime_ninetyCJ_5030639 : Nat.Prime 5030639 := by norm_num

private theorem prime_ninetyCJ_5181983 : Nat.Prime 5181983 := by norm_num

private theorem prime_ninetyCJ_5344553 : Nat.Prime 5344553 := by norm_num

private theorem prime_ninetyCJ_5379403 : Nat.Prime 5379403 := by norm_num

private theorem prime_ninetyCJ_5454223 : Nat.Prime 5454223 := by norm_num

private theorem prime_ninetyCJ_5520967 : Nat.Prime 5520967 := by norm_num

private theorem prime_ninetyCJ_5871301 : Nat.Prime 5871301 := by norm_num

private theorem prime_ninetyCJ_5988271 : Nat.Prime 5988271 := by norm_num

private theorem prime_ninetyCJ_6157199 : Nat.Prime 6157199 := by norm_num

private theorem prime_ninetyCJ_6166129 : Nat.Prime 6166129 := by norm_num

private theorem prime_ninetyCJ_6312379 : Nat.Prime 6312379 := by norm_num

private theorem prime_ninetyCJ_6381581 : Nat.Prime 6381581 := by norm_num

private theorem prime_ninetyCJ_6882593 : Nat.Prime 6882593 := by norm_num

private theorem prime_ninetyCJ_7064927 : Nat.Prime 7064927 := by norm_num

private theorem prime_ninetyCJ_7978889 : Nat.Prime 7978889 := by norm_num

private theorem prime_ninetyCJ_9513017 : Nat.Prime 9513017 := by norm_num

private theorem prime_ninetyCJ_9818873 : Nat.Prime 9818873 := by norm_num

private theorem prime_ninetyCJ_10102733 : Nat.Prime 10102733 := by norm_num

private theorem prime_ninetyCJ_11032883 : Nat.Prime 11032883 := by norm_num

private theorem prime_ninetyCJ_11415697 : Nat.Prime 11415697 := by norm_num

private theorem prime_ninetyCJ_11453899 : Nat.Prime 11453899 := by norm_num

private theorem prime_ninetyCJ_11712863 : Nat.Prime 11712863 := by norm_num

private theorem prime_ninetyCJ_12028531 : Nat.Prime 12028531 := by norm_num

private theorem prime_ninetyCJ_12118103 : Nat.Prime 12118103 := by norm_num

private theorem prime_ninetyCJ_12768089 : Nat.Prime 12768089 := by norm_num

private theorem prime_ninetyCJ_14028673 : Nat.Prime 14028673 := by norm_num

private theorem prime_ninetyCJ_15024749 : Nat.Prime 15024749 := by norm_num

private theorem prime_ninetyCJ_16001729 : Nat.Prime 16001729 := by norm_num

private theorem prime_ninetyCJ_16482539 : Nat.Prime 16482539 := by norm_num

private theorem prime_ninetyCJ_17230201 : Nat.Prime 17230201 := by norm_num

private theorem prime_ninetyCJ_17453897 : Nat.Prime 17453897 := by norm_num

private theorem prime_ninetyCJ_17882957 : Nat.Prime 17882957 := by norm_num

private theorem prime_ninetyCJ_18478217 : Nat.Prime 18478217 := by norm_num

private theorem prime_ninetyCJ_18594001 : Nat.Prime 18594001 := by norm_num

private theorem prime_ninetyCJ_18884653 : Nat.Prime 18884653 := by norm_num

private theorem prime_ninetyCJ_19479701 : Nat.Prime 19479701 := by norm_num

private theorem prime_ninetyCJ_20649851 : Nat.Prime 20649851 := by norm_num

private theorem prime_ninetyCJ_20662897 : Nat.Prime 20662897 := by norm_num

private theorem prime_ninetyCJ_23286269 : Nat.Prime 23286269 := by norm_num

private theorem prime_ninetyCJ_23842051 : Nat.Prime 23842051 := by norm_num

private theorem prime_ninetyCJ_24435863 : Nat.Prime 24435863 := by norm_num

private theorem prime_ninetyCJ_26411711 : Nat.Prime 26411711 := by norm_num

private theorem prime_ninetyCJ_27185311 : Nat.Prime 27185311 := by norm_num

private theorem prime_ninetyCJ_27682313 : Nat.Prime 27682313 := by norm_num

private theorem prime_ninetyCJ_29110747 : Nat.Prime 29110747 := by norm_num

private theorem prime_ninetyCJ_30748409 : Nat.Prime 30748409 := by
  apply lucas_primality 30748409 (3 : ZMod 30748409)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3843551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3843551, 1)] : List FactorBlock).map factorBlockValue).prod) = 30748409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3843551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 30748409) ^ 15374204 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30748409) ^ 8 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_31555571 : Nat.Prime 31555571 := by
  apply lucas_primality 31555571 (2 : ZMod 31555571)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (185621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (185621, 1)] : List FactorBlock).map factorBlockValue).prod) = 31555571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_17
      · exact prime_ninetyCJ_185621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31555571) ^ 15777785 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 31555571) ^ 6311114 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 31555571) ^ 1856210 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 31555571) ^ 170 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_31635049 : Nat.Prime 31635049 := by
  apply lucas_primality 31635049 (7 : ZMod 31635049)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (197, 1), (6691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (197, 1), (6691, 1)] : List FactorBlock).map factorBlockValue).prod) = 31635049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_197
      · exact prime_ninetyCJ_6691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 31635049) ^ 15817524 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 31635049) ^ 10545016 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 31635049) ^ 160584 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 31635049) ^ 4728 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_33654931 : Nat.Prime 33654931 := by
  apply lucas_primality 33654931 (3 : ZMod 33654931)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1121831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1121831, 1)] : List FactorBlock).map factorBlockValue).prod) = 33654931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_1121831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33654931) ^ 16827465 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33654931) ^ 11218310 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33654931) ^ 6730986 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33654931) ^ 30 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_35975837 : Nat.Prime 35975837 := by
  apply lucas_primality 35975837 (2 : ZMod 35975837)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (691843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (691843, 1)] : List FactorBlock).map factorBlockValue).prod) = 35975837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_691843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35975837) ^ 17987918 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 35975837) ^ 2767372 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 35975837) ^ 52 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_36046847 : Nat.Prime 36046847 := by
  apply lucas_primality 36046847 (5 : ZMod 36046847)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (619, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (619, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) = 36046847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_619
      · exact prime_ninetyCJ_2647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 36046847) ^ 18023423 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 36046847) ^ 3276986 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 36046847) ^ 58234 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 36046847) ^ 13618 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_36281951 : Nat.Prime 36281951 := by
  apply lucas_primality 36281951 (17 : ZMod 36281951)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (725639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (725639, 1)] : List FactorBlock).map factorBlockValue).prod) = 36281951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_725639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 36281951) ^ 18140975 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 36281951) ^ 7256390 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 36281951) ^ 50 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_38703011 : Nat.Prime 38703011 := by
  apply lucas_primality 38703011 (2 : ZMod 38703011)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (90007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (90007, 1)] : List FactorBlock).map factorBlockValue).prod) = 38703011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_43
      · exact prime_ninetyCJ_90007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38703011) ^ 19351505 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 38703011) ^ 7740602 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 38703011) ^ 900070 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 38703011) ^ 430 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_40018213 : Nat.Prime 40018213 := by
  apply lucas_primality 40018213 (2 : ZMod 40018213)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (13, 1), (3167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (13, 1), (3167, 1)] : List FactorBlock).map factorBlockValue).prod) = 40018213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_3167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40018213) ^ 20009106 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40018213) ^ 13339404 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40018213) ^ 3078324 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40018213) ^ 12636 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_40828927 : Nat.Prime 40828927 := by
  apply lucas_primality 40828927 (3 : ZMod 40828927)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (461, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (461, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) = 40828927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_461
      · exact prime_ninetyCJ_509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40828927) ^ 20414463 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40828927) ^ 13609642 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40828927) ^ 1407894 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40828927) ^ 88566 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40828927) ^ 80214 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_43039247 : Nat.Prime 43039247 := by
  apply lucas_primality 43039247 (5 : ZMod 43039247)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (144427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (144427, 1)] : List FactorBlock).map factorBlockValue).prod) = 43039247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_149
      · exact prime_ninetyCJ_144427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 43039247) ^ 21519623 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 43039247) ^ 288854 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 43039247) ^ 298 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_48871727 : Nat.Prime 48871727 := by
  apply lucas_primality 48871727 (5 : ZMod 48871727)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (24435863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (24435863, 1)] : List FactorBlock).map factorBlockValue).prod) = 48871727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_24435863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 48871727) ^ 24435863 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 48871727) ^ 2 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_50056471 : Nat.Prime 50056471 := by
  apply lucas_primality 50056471 (3 : ZMod 50056471)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (83, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (83, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod) = 50056471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_83
      · exact prime_ninetyCJ_6701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 50056471) ^ 25028235 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 50056471) ^ 16685490 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 50056471) ^ 10011294 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 50056471) ^ 603090 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 50056471) ^ 7470 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_56319349 : Nat.Prime 56319349 := by
  apply lucas_primality 56319349 (2 : ZMod 56319349)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (61, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (61, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) = 56319349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_47
      · exact prime_ninetyCJ_61
      · exact prime_ninetyCJ_1637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56319349) ^ 28159674 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 56319349) ^ 18773116 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 56319349) ^ 1198284 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 56319349) ^ 923268 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 56319349) ^ 34404 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_56794607 : Nat.Prime 56794607 := by
  apply lucas_primality 56794607 (5 : ZMod 56794607)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2581573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2581573, 1)] : List FactorBlock).map factorBlockValue).prod) = 56794607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_2581573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 56794607) ^ 28397303 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 56794607) ^ 5163146 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 56794607) ^ 22 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_57040801 : Nat.Prime 57040801 := by
  apply lucas_primality 57040801 (7 : ZMod 57040801)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (23767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (23767, 1)] : List FactorBlock).map factorBlockValue).prod) = 57040801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_23767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 57040801) ^ 28520400 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 57040801) ^ 19013600 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 57040801) ^ 11408160 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 57040801) ^ 2400 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_59166553 : Nat.Prime 59166553 := by
  apply lucas_primality 59166553 (5 : ZMod 59166553)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (66629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (66629, 1)] : List FactorBlock).map factorBlockValue).prod) = 59166553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_37
      · exact prime_ninetyCJ_66629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 59166553) ^ 29583276 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 59166553) ^ 19722184 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 59166553) ^ 1599096 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 59166553) ^ 888 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_59834051 : Nat.Prime 59834051 := by
  apply lucas_primality 59834051 (2 : ZMod 59834051)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (70393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (70393, 1)] : List FactorBlock).map factorBlockValue).prod) = 59834051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_17
      · exact prime_ninetyCJ_70393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 59834051) ^ 29917025 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 59834051) ^ 11966810 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 59834051) ^ 3519650 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 59834051) ^ 850 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_71055833 : Nat.Prime 71055833 := by
  apply lucas_primality 71055833 (3 : ZMod 71055833)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (386173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (386173, 1)] : List FactorBlock).map factorBlockValue).prod) = 71055833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_23
      · exact prime_ninetyCJ_386173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71055833) ^ 35527916 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 71055833) ^ 3089384 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 71055833) ^ 184 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_72563903 : Nat.Prime 72563903 := by
  apply lucas_primality 72563903 (5 : ZMod 72563903)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (36281951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (36281951, 1)] : List FactorBlock).map factorBlockValue).prod) = 72563903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_36281951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 72563903) ^ 36281951 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 72563903) ^ 2 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_73835959 : Nat.Prime 73835959 := by
  apply lucas_primality 73835959 (3 : ZMod 73835959)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1757999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1757999, 1)] : List FactorBlock).map factorBlockValue).prod) = 73835959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_1757999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 73835959) ^ 36917979 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 73835959) ^ 24611986 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 73835959) ^ 10547994 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 73835959) ^ 42 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_75538613 : Nat.Prime 75538613 := by
  apply lucas_primality 75538613 (2 : ZMod 75538613)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18884653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18884653, 1)] : List FactorBlock).map factorBlockValue).prod) = 75538613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_18884653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 75538613) ^ 37769306 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 75538613) ^ 4 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_78217151 : Nat.Prime 78217151 := by
  apply lucas_primality 78217151 (11 : ZMod 78217151)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (71, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (71, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) = 78217151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_71
      · exact prime_ninetyCJ_2003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 78217151) ^ 39108575 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 78217151) ^ 15643430 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 78217151) ^ 7110650 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 78217151) ^ 1101650 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 78217151) ^ 39050 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_84216413 : Nat.Prime 84216413 := by
  apply lucas_primality 84216413 (3 : ZMod 84216413)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1087, 1), (2767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1087, 1), (2767, 1)] : List FactorBlock).map factorBlockValue).prod) = 84216413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_1087
      · exact prime_ninetyCJ_2767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 84216413) ^ 42108206 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 84216413) ^ 12030916 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 84216413) ^ 77476 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 84216413) ^ 30436 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_90659137 : Nat.Prime 90659137 := by
  apply lucas_primality 90659137 (11 : ZMod 90659137)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (43, 1), (79, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (43, 1), (79, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) = 90659137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_43
      · exact prime_ninetyCJ_79
      · exact prime_ninetyCJ_139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 90659137) ^ 45329568 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 90659137) ^ 30219712 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 90659137) ^ 2108352 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 90659137) ^ 1147584 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 90659137) ^ 652224 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_91715497 : Nat.Prime 91715497 := by
  apply lucas_primality 91715497 (7 : ZMod 91715497)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (57037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (57037, 1)] : List FactorBlock).map factorBlockValue).prod) = 91715497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_67
      · exact prime_ninetyCJ_57037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 91715497) ^ 45857748 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 91715497) ^ 30571832 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 91715497) ^ 1368888 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 91715497) ^ 1608 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_92090969 : Nat.Prime 92090969 := by
  apply lucas_primality 92090969 (3 : ZMod 92090969)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (188711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (188711, 1)] : List FactorBlock).map factorBlockValue).prod) = 92090969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_61
      · exact prime_ninetyCJ_188711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 92090969) ^ 46045484 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 92090969) ^ 1509688 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 92090969) ^ 488 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_97699907 : Nat.Prime 97699907 := by
  apply lucas_primality 97699907 (2 : ZMod 97699907)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (37, 1), (137, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (37, 1), (137, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 97699907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_23
      · exact prime_ninetyCJ_37
      · exact prime_ninetyCJ_137
      · exact prime_ninetyCJ_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 97699907) ^ 48849953 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 97699907) ^ 4247822 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 97699907) ^ 2640538 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 97699907) ^ 713138 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 97699907) ^ 233174 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_102221831 : Nat.Prime 102221831 := by
  apply lucas_primality 102221831 (19 : ZMod 102221831)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1013, 1), (10091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1013, 1), (10091, 1)] : List FactorBlock).map factorBlockValue).prod) = 102221831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_1013
      · exact prime_ninetyCJ_10091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 102221831) ^ 51110915 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 102221831) ^ 20444366 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 102221831) ^ 100910 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 102221831) ^ 10130 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_102322639 : Nat.Prime 102322639 := by
  apply lucas_primality 102322639 (3 : ZMod 102322639)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (19, 1), (59, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (19, 1), (59, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) = 102322639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_59
      · exact prime_ninetyCJ_461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 102322639) ^ 51161319 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 102322639) ^ 34107546 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 102322639) ^ 9302058 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 102322639) ^ 5385402 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 102322639) ^ 1734282 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 102322639) ^ 221958 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_104489563 : Nat.Prime 104489563 := by
  apply lucas_primality 104489563 (2 : ZMod 104489563)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (104281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (104281, 1)] : List FactorBlock).map factorBlockValue).prod) = 104489563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_167
      · exact prime_ninetyCJ_104281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 104489563) ^ 52244781 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 104489563) ^ 34829854 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 104489563) ^ 625686 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 104489563) ^ 1002 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_111557489 : Nat.Prime 111557489 := by
  apply lucas_primality 111557489 (3 : ZMod 111557489)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (996049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (996049, 1)] : List FactorBlock).map factorBlockValue).prod) = 111557489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_996049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 111557489) ^ 55778744 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 111557489) ^ 15936784 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 111557489) ^ 112 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_128096911 : Nat.Prime 128096911 := by
  apply lucas_primality 128096911 (3 : ZMod 128096911)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (474433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (474433, 1)] : List FactorBlock).map factorBlockValue).prod) = 128096911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_474433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 128096911) ^ 64048455 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 128096911) ^ 42698970 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 128096911) ^ 25619382 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 128096911) ^ 270 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_130178273 : Nat.Prime 130178273 := by
  apply lucas_primality 130178273 (3 : ZMod 130178273)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (19, 1), (73, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (19, 1), (73, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 130178273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_73
      · exact prime_ninetyCJ_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 130178273) ^ 65089136 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 130178273) ^ 18596896 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 130178273) ^ 6851488 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 130178273) ^ 1783264 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 130178273) ^ 310688 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_130747007 : Nat.Prime 130747007 := by
  apply lucas_primality 130747007 (5 : ZMod 130747007)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (227, 1), (22153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (227, 1), (22153, 1)] : List FactorBlock).map factorBlockValue).prod) = 130747007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_227
      · exact prime_ninetyCJ_22153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 130747007) ^ 65373503 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 130747007) ^ 10057462 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 130747007) ^ 575978 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 130747007) ^ 5902 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_134042011 : Nat.Prime 134042011 := by
  apply lucas_primality 134042011 (2 : ZMod 134042011)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (89, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (89, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) = 134042011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_61
      · exact prime_ninetyCJ_89
      · exact prime_ninetyCJ_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 134042011) ^ 67021005 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 134042011) ^ 44680670 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 134042011) ^ 26808402 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 134042011) ^ 2197410 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 134042011) ^ 1506090 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 134042011) ^ 162870 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_136964263 : Nat.Prime 136964263 := by
  apply lucas_primality 136964263 (3 : ZMod 136964263)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (736367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (736367, 1)] : List FactorBlock).map factorBlockValue).prod) = 136964263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_31
      · exact prime_ninetyCJ_736367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 136964263) ^ 68482131 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 136964263) ^ 45654754 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 136964263) ^ 4418202 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 136964263) ^ 186 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_137446789 : Nat.Prime 137446789 := by
  apply lucas_primality 137446789 (2 : ZMod 137446789)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11453899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11453899, 1)] : List FactorBlock).map factorBlockValue).prod) = 137446789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11453899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 137446789) ^ 68723394 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 137446789) ^ 45815596 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 137446789) ^ 12 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_140079089 : Nat.Prime 140079089 := by
  apply lucas_primality 140079089 (3 : ZMod 140079089)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2693, 1), (3251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2693, 1), (3251, 1)] : List FactorBlock).map factorBlockValue).prod) = 140079089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_2693
      · exact prime_ninetyCJ_3251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 140079089) ^ 70039544 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 140079089) ^ 52016 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 140079089) ^ 43088 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_140144509 : Nat.Prime 140144509 := by
  apply lucas_primality 140144509 (6 : ZMod 140144509)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (53, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (53, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) = 140144509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_53
      · exact prime_ninetyCJ_1499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 140144509) ^ 70072254 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 140144509) ^ 46714836 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 140144509) ^ 20020644 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 140144509) ^ 2644236 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 140144509) ^ 93492 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_143847059 : Nat.Prime 143847059 := by
  apply lucas_primality 143847059 (2 : ZMod 143847059)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (521, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (521, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) = 143847059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_127
      · exact prime_ninetyCJ_521
      · exact prime_ninetyCJ_1087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 143847059) ^ 71923529 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 143847059) ^ 1132654 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 143847059) ^ 276098 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 143847059) ^ 132334 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_147538673 : Nat.Prime 147538673 := by
  apply lucas_primality 147538673 (3 : ZMod 147538673)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (297457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (297457, 1)] : List FactorBlock).map factorBlockValue).prod) = 147538673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_31
      · exact prime_ninetyCJ_297457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 147538673) ^ 73769336 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 147538673) ^ 4759312 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 147538673) ^ 496 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_153217069 : Nat.Prime 153217069 := by
  apply lucas_primality 153217069 (2 : ZMod 153217069)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (12768089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (12768089, 1)] : List FactorBlock).map factorBlockValue).prod) = 153217069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_12768089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 153217069) ^ 76608534 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 153217069) ^ 51072356 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 153217069) ^ 12 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_156434303 : Nat.Prime 156434303 := by
  apply lucas_primality 156434303 (5 : ZMod 156434303)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (78217151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (78217151, 1)] : List FactorBlock).map factorBlockValue).prod) = 156434303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_78217151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 156434303) ^ 78217151 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 156434303) ^ 2 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_174824659 : Nat.Prime 174824659 := by
  apply lucas_primality 174824659 (2 : ZMod 174824659)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (89, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (89, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) = 174824659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_61
      · exact prime_ninetyCJ_89
      · exact prime_ninetyCJ_1789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 174824659) ^ 87412329 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 174824659) ^ 58274886 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 174824659) ^ 2865978 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 174824659) ^ 1964322 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 174824659) ^ 97722 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_185940011 : Nat.Prime 185940011 := by
  apply lucas_primality 185940011 (2 : ZMod 185940011)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (18594001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (18594001, 1)] : List FactorBlock).map factorBlockValue).prod) = 185940011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_18594001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 185940011) ^ 92970005 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 185940011) ^ 37188002 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 185940011) ^ 10 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_192456497 : Nat.Prime 192456497 := by
  apply lucas_primality 192456497 (3 : ZMod 192456497)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (12028531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (12028531, 1)] : List FactorBlock).map factorBlockValue).prod) = 192456497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_12028531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 192456497) ^ 96228248 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 192456497) ^ 16 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_192651929 : Nat.Prime 192651929 := by
  apply lucas_primality 192651929 (6 : ZMod 192651929)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (79, 1), (6221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (79, 1), (6221, 1)] : List FactorBlock).map factorBlockValue).prod) = 192651929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_79
      · exact prime_ninetyCJ_6221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 192651929) ^ 96325964 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 192651929) ^ 27521704 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 192651929) ^ 2438632 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 192651929) ^ 30968 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_209252401 : Nat.Prime 209252401 := by
  apply lucas_primality 209252401 (23 : ZMod 209252401)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (7, 1), (29, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (7, 1), (29, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) = 209252401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 209252401) ^ 104626200 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (23 : ZMod 209252401) ^ 69750800 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (23 : ZMod 209252401) ^ 41850480 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (23 : ZMod 209252401) ^ 29893200 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (23 : ZMod 209252401) ^ 7215600 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (23 : ZMod 209252401) ^ 243600 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_235712387 : Nat.Prime 235712387 := by
  apply lucas_primality 235712387 (2 : ZMod 235712387)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (101, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (101, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) = 235712387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_101
      · exact prime_ninetyCJ_12823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 235712387) ^ 117856193 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 235712387) ^ 33673198 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 235712387) ^ 18131722 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 235712387) ^ 2333786 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 235712387) ^ 18382 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_258441151 : Nat.Prime 258441151 := by
  apply lucas_primality 258441151 (13 : ZMod 258441151)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (156631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (156631, 1)] : List FactorBlock).map factorBlockValue).prod) = 258441151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_156631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 258441151) ^ 129220575 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 258441151) ^ 86147050 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 258441151) ^ 51688230 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 258441151) ^ 23494650 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 258441151) ^ 1650 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_264790529 : Nat.Prime 264790529 := by
  apply lucas_primality 264790529 (3 : ZMod 264790529)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (517169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (517169, 1)] : List FactorBlock).map factorBlockValue).prod) = 264790529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_517169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 264790529) ^ 132395264 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 264790529) ^ 512 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_315870367 : Nat.Prime 315870367 := by
  apply lucas_primality 315870367 (5 : ZMod 315870367)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (1074389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (1074389, 1)] : List FactorBlock).map factorBlockValue).prod) = 315870367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_1074389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 315870367) ^ 157935183 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 315870367) ^ 105290122 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 315870367) ^ 45124338 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 315870367) ^ 294 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_356900633 : Nat.Prime 356900633 := by
  apply lucas_primality 356900633 (3 : ZMod 356900633)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (503, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (503, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) = 356900633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_503
      · exact prime_ninetyCJ_733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 356900633) ^ 178450316 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 356900633) ^ 32445512 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 356900633) ^ 709544 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 356900633) ^ 486904 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_371880023 : Nat.Prime 371880023 := by
  apply lucas_primality 371880023 (5 : ZMod 371880023)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (185940011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (185940011, 1)] : List FactorBlock).map factorBlockValue).prod) = 371880023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_185940011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 371880023) ^ 185940011 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 371880023) ^ 2 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_404383613 : Nat.Prime 404383613 := by
  apply lucas_primality 404383613 (2 : ZMod 404383613)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (499, 1), (10663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (499, 1), (10663, 1)] : List FactorBlock).map factorBlockValue).prod) = 404383613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_499
      · exact prime_ninetyCJ_10663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 404383613) ^ 202191806 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 404383613) ^ 21283348 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 404383613) ^ 810388 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 404383613) ^ 37924 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_457633661 : Nat.Prime 457633661 := by
  apply lucas_primality 457633661 (10 : ZMod 457633661)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (571, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (571, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) = 457633661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_571
      · exact prime_ninetyCJ_3643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 457633661) ^ 228816830 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 457633661) ^ 91526732 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 457633661) ^ 41603060 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 457633661) ^ 801460 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 457633661) ^ 125620 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_466794217 : Nat.Prime 466794217 := by
  apply lucas_primality 466794217 (5 : ZMod 466794217)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (926179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (926179, 1)] : List FactorBlock).map factorBlockValue).prod) = 466794217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_926179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 466794217) ^ 233397108 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 466794217) ^ 155598072 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 466794217) ^ 66684888 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 466794217) ^ 504 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_523616911 : Nat.Prime 523616911 := by
  apply lucas_primality 523616911 (3 : ZMod 523616911)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17453897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17453897, 1)] : List FactorBlock).map factorBlockValue).prod) = 523616911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_17453897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 523616911) ^ 261808455 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 523616911) ^ 174538970 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 523616911) ^ 104723382 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 523616911) ^ 30 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_550292983 : Nat.Prime 550292983 := by
  apply lucas_primality 550292983 (3 : ZMod 550292983)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (91715497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (91715497, 1)] : List FactorBlock).map factorBlockValue).prod) = 550292983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_91715497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 550292983) ^ 275146491 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 550292983) ^ 183430994 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 550292983) ^ 6 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_579740593 : Nat.Prime 579740593 := by
  apply lucas_primality 579740593 (5 : ZMod 579740593)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (929, 1), (13001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (929, 1), (13001, 1)] : List FactorBlock).map factorBlockValue).prod) = 579740593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_929
      · exact prime_ninetyCJ_13001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 579740593) ^ 289870296 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 579740593) ^ 193246864 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 579740593) ^ 624048 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 579740593) ^ 44592 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_682775959 : Nat.Prime 682775959 := by
  apply lucas_primality 682775959 (3 : ZMod 682775959)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (1126693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (1126693, 1)] : List FactorBlock).map factorBlockValue).prod) = 682775959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_101
      · exact prime_ninetyCJ_1126693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 682775959) ^ 341387979 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 682775959) ^ 227591986 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 682775959) ^ 6760158 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 682775959) ^ 606 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_684489613 : Nat.Prime 684489613 := by
  apply lucas_primality 684489613 (2 : ZMod 684489613)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (57040801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (57040801, 1)] : List FactorBlock).map factorBlockValue).prod) = 684489613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_57040801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 684489613) ^ 342244806 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 684489613) ^ 228163204 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 684489613) ^ 12 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_711548987 : Nat.Prime 711548987 := by
  apply lucas_primality 711548987 (2 : ZMod 711548987)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (1163, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (1163, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) = 711548987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_179
      · exact prime_ninetyCJ_1163
      · exact prime_ninetyCJ_1709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 711548987) ^ 355774493 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 711548987) ^ 3975134 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 711548987) ^ 611822 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 711548987) ^ 416354 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_715261531 : Nat.Prime 715261531 := by
  apply lucas_primality 715261531 (2 : ZMod 715261531)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23842051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23842051, 1)] : List FactorBlock).map factorBlockValue).prod) = 715261531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_23842051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 715261531) ^ 357630765 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 715261531) ^ 238420510 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 715261531) ^ 143052306 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 715261531) ^ 30 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_953385283 : Nat.Prime 953385283 := by
  apply lucas_primality 953385283 (2 : ZMod 953385283)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (23, 1), (181, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (23, 1), (181, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) = 953385283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_23
      · exact prime_ninetyCJ_181
      · exact prime_ninetyCJ_4241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 953385283) ^ 476692641 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 953385283) ^ 317795094 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 953385283) ^ 41451534 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 953385283) ^ 5267322 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 953385283) ^ 224802 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_983445889 : Nat.Prime 983445889 := by
  apply lucas_primality 983445889 (11 : ZMod 983445889)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (101, 1), (25357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (101, 1), (25357, 1)] : List FactorBlock).map factorBlockValue).prod) = 983445889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_101
      · exact prime_ninetyCJ_25357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 983445889) ^ 491722944 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 983445889) ^ 327815296 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 983445889) ^ 9737088 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 983445889) ^ 38784 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1015894643 : Nat.Prime 1015894643 := by
  apply lucas_primality 1015894643 (2 : ZMod 1015894643)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (72563903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (72563903, 1)] : List FactorBlock).map factorBlockValue).prod) = 1015894643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_72563903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1015894643) ^ 507947321 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1015894643) ^ 145127806 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1015894643) ^ 14 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1148960017 : Nat.Prime 1148960017 := by
  apply lucas_primality 1148960017 (5 : ZMod 1148960017)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7978889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7978889, 1)] : List FactorBlock).map factorBlockValue).prod) = 1148960017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7978889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1148960017) ^ 574480008 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1148960017) ^ 382986672 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1148960017) ^ 144 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1154738983 : Nat.Prime 1154738983 := by
  apply lucas_primality 1154738983 (3 : ZMod 1154738983)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (192456497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (192456497, 1)] : List FactorBlock).map factorBlockValue).prod) = 1154738983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_192456497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1154738983) ^ 577369491 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1154738983) ^ 384912994 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1154738983) ^ 6 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1325599591 : Nat.Prime 1325599591 := by
  apply lucas_primality 1325599591 (14 : ZMod 1325599591)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (6312379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (6312379, 1)] : List FactorBlock).map factorBlockValue).prod) = 1325599591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_6312379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1325599591) ^ 662799795 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 1325599591) ^ 441866530 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 1325599591) ^ 265119918 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 1325599591) ^ 189371370 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 1325599591) ^ 210 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1454172361 : Nat.Prime 1454172361 := by
  apply lucas_primality 1454172361 (14 : ZMod 1454172361)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (12118103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (12118103, 1)] : List FactorBlock).map factorBlockValue).prod) = 1454172361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_12118103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 1454172361) ^ 727086180 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 1454172361) ^ 484724120 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 1454172361) ^ 290834472 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 1454172361) ^ 120 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1616582321 : Nat.Prime 1616582321 := by
  apply lucas_primality 1616582321 (3 : ZMod 1616582321)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (19, 1), (1063541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (19, 1), (1063541, 1)] : List FactorBlock).map factorBlockValue).prod) = 1616582321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_1063541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1616582321) ^ 808291160 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616582321) ^ 323316464 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616582321) ^ 85083280 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616582321) ^ 1520 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1729488407 : Nat.Prime 1729488407 := by
  apply lucas_primality 1729488407 (5 : ZMod 1729488407)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (89, 1), (167, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (89, 1), (167, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) = 1729488407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_73
      · exact prime_ninetyCJ_89
      · exact prime_ninetyCJ_167
      · exact prime_ninetyCJ_797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1729488407) ^ 864744203 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1729488407) ^ 23691622 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1729488407) ^ 19432454 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1729488407) ^ 10356218 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1729488407) ^ 2169998 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1834421983 : Nat.Prime 1834421983 := by
  apply lucas_primality 1834421983 (23 : ZMod 1834421983)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (5181983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (5181983, 1)] : List FactorBlock).map factorBlockValue).prod) = 1834421983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_59
      · exact prime_ninetyCJ_5181983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 1834421983) ^ 917210991 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (23 : ZMod 1834421983) ^ 611473994 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (23 : ZMod 1834421983) ^ 31091898 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (23 : ZMod 1834421983) ^ 354 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1899786293 : Nat.Prime 1899786293 := by
  apply lucas_primality 1899786293 (2 : ZMod 1899786293)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (20649851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (20649851, 1)] : List FactorBlock).map factorBlockValue).prod) = 1899786293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_23
      · exact prime_ninetyCJ_20649851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1899786293) ^ 949893146 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1899786293) ^ 82599404 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1899786293) ^ 92 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_2234906981 : Nat.Prime 2234906981 := by
  apply lucas_primality 2234906981 (2 : ZMod 2234906981)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3181, 1), (35129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3181, 1), (35129, 1)] : List FactorBlock).map factorBlockValue).prod) = 2234906981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_3181
      · exact prime_ninetyCJ_35129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2234906981) ^ 1117453490 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2234906981) ^ 446981396 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2234906981) ^ 702580 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2234906981) ^ 63620 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_2325314293 : Nat.Prime 2325314293 := by
  apply lucas_primality 2325314293 (2 : ZMod 2325314293)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (27682313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (27682313, 1)] : List FactorBlock).map factorBlockValue).prod) = 2325314293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_27682313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2325314293) ^ 1162657146 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2325314293) ^ 775104764 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2325314293) ^ 332187756 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2325314293) ^ 84 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_2379091903 : Nat.Prime 2379091903 := by
  apply lucas_primality 2379091903 (3 : ZMod 2379091903)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (36046847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (36046847, 1)] : List FactorBlock).map factorBlockValue).prod) = 2379091903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_36046847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2379091903) ^ 1189545951 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2379091903) ^ 793030634 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2379091903) ^ 216281082 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2379091903) ^ 66 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_2737990001 : Nat.Prime 2737990001 := by
  apply lucas_primality 2737990001 (6 : ZMod 2737990001)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 4), (113, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 4), (113, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) = 2737990001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_113
      · exact prime_ninetyCJ_2423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2737990001) ^ 1368995000 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2737990001) ^ 547598000 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2737990001) ^ 24230000 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 2737990001) ^ 1130000 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_2876941181 : Nat.Prime 2876941181 := by
  apply lucas_primality 2876941181 (2 : ZMod 2876941181)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (143847059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (143847059, 1)] : List FactorBlock).map factorBlockValue).prod) = 2876941181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_143847059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2876941181) ^ 1438470590 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2876941181) ^ 575388236 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2876941181) ^ 20 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_2939528491 : Nat.Prime 2939528491 := by
  apply lucas_primality 2939528491 (2 : ZMod 2939528491)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (89, 1), (1100947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (89, 1), (1100947, 1)] : List FactorBlock).map factorBlockValue).prod) = 2939528491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_89
      · exact prime_ninetyCJ_1100947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2939528491) ^ 1469764245 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2939528491) ^ 979842830 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2939528491) ^ 587905698 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2939528491) ^ 33028410 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2939528491) ^ 2670 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_3202753819 : Nat.Prime 3202753819 := by
  apply lucas_primality 3202753819 (2 : ZMod 3202753819)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (23, 1), (37, 1), (127, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (23, 1), (37, 1), (127, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 3202753819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_23
      · exact prime_ninetyCJ_37
      · exact prime_ninetyCJ_127
      · exact prime_ninetyCJ_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3202753819) ^ 1601376909 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3202753819) ^ 1067584606 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3202753819) ^ 291159438 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3202753819) ^ 139250166 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3202753819) ^ 86560914 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3202753819) ^ 25218534 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3202753819) ^ 7133082 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_3229254433 : Nat.Prime 3229254433 := by
  apply lucas_primality 3229254433 (5 : ZMod 3229254433)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (3737563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (3737563, 1)] : List FactorBlock).map factorBlockValue).prod) = 3229254433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_3737563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3229254433) ^ 1614627216 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3229254433) ^ 1076418144 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3229254433) ^ 864 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_3362437957 : Nat.Prime 3362437957 := by
  apply lucas_primality 3362437957 (5 : ZMod 3362437957)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (16482539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (16482539, 1)] : List FactorBlock).map factorBlockValue).prod) = 3362437957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_17
      · exact prime_ninetyCJ_16482539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3362437957) ^ 1681218978 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3362437957) ^ 1120812652 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3362437957) ^ 197790468 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3362437957) ^ 204 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_3848510093 : Nat.Prime 3848510093 := by
  apply lucas_primality 3848510093 (3 : ZMod 3848510093)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (137446789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (137446789, 1)] : List FactorBlock).map factorBlockValue).prod) = 3848510093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_137446789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3848510093) ^ 1924255046 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3848510093) ^ 549787156 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3848510093) ^ 28 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_3855717031 : Nat.Prime 3855717031 := by
  apply lucas_primality 3855717031 (3 : ZMod 3855717031)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 2), (257, 1), (4133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 2), (257, 1), (4133, 1)] : List FactorBlock).map factorBlockValue).prod) = 3855717031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_257
      · exact prime_ninetyCJ_4133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3855717031) ^ 1927858515 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3855717031) ^ 1285239010 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3855717031) ^ 771143406 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3855717031) ^ 350519730 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3855717031) ^ 15002790 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3855717031) ^ 932910 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_4019502061 : Nat.Prime 4019502061 := by
  apply lucas_primality 4019502061 (2 : ZMod 4019502061)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (19, 1), (167899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (19, 1), (167899, 1)] : List FactorBlock).map factorBlockValue).prod) = 4019502061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_167899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4019502061) ^ 2009751030 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4019502061) ^ 1339834020 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4019502061) ^ 803900412 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4019502061) ^ 574214580 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4019502061) ^ 211552740 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4019502061) ^ 23940 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_4996608863 : Nat.Prime 4996608863 := by
  apply lucas_primality 4996608863 (5 : ZMod 4996608863)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (356900633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (356900633, 1)] : List FactorBlock).map factorBlockValue).prod) = 4996608863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_356900633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4996608863) ^ 2498304431 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4996608863) ^ 713801266 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4996608863) ^ 14 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_5004875131 : Nat.Prime 5004875131 := by
  apply lucas_primality 5004875131 (3 : ZMod 5004875131)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3851, 1), (43321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3851, 1), (43321, 1)] : List FactorBlock).map factorBlockValue).prod) = 5004875131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_3851
      · exact prime_ninetyCJ_43321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5004875131) ^ 2502437565 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5004875131) ^ 1668291710 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5004875131) ^ 1000975026 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5004875131) ^ 1299630 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5004875131) ^ 115530 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_5269992269 : Nat.Prime 5269992269 := by
  apply lucas_primality 5269992269 (2 : ZMod 5269992269)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (313, 1), (4209259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (313, 1), (4209259, 1)] : List FactorBlock).map factorBlockValue).prod) = 5269992269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_313
      · exact prime_ninetyCJ_4209259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5269992269) ^ 2634996134 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5269992269) ^ 16837036 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5269992269) ^ 1252 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_5797539721 : Nat.Prime 5797539721 := by
  apply lucas_primality 5797539721 (17 : ZMod 5797539721)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (2300611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (2300611, 1)] : List FactorBlock).map factorBlockValue).prod) = 5797539721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_2300611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 5797539721) ^ 2898769860 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 5797539721) ^ 1932513240 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 5797539721) ^ 1159507944 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 5797539721) ^ 828219960 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 5797539721) ^ 2520 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_6842041781 : Nat.Prime 6842041781 := by
  apply lucas_primality 6842041781 (2 : ZMod 6842041781)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (48871727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (48871727, 1)] : List FactorBlock).map factorBlockValue).prod) = 6842041781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_48871727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6842041781) ^ 3421020890 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6842041781) ^ 1368408356 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6842041781) ^ 977434540 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6842041781) ^ 140 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_6893760103 : Nat.Prime 6893760103 := by
  apply lucas_primality 6893760103 (5 : ZMod 6893760103)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1148960017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1148960017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6893760103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_1148960017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6893760103) ^ 3446880051 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6893760103) ^ 2297920034 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6893760103) ^ 6 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_7277011717 : Nat.Prime 7277011717 := by
  apply lucas_primality 7277011717 (6 : ZMod 7277011717)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (73, 1), (639007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (73, 1), (639007, 1)] : List FactorBlock).map factorBlockValue).prod) = 7277011717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_73
      · exact prime_ninetyCJ_639007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7277011717) ^ 3638505858 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 7277011717) ^ 2425670572 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 7277011717) ^ 559770132 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 7277011717) ^ 99685092 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 7277011717) ^ 11388 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_7337687933 : Nat.Prime 7337687933 := by
  apply lucas_primality 7337687933 (2 : ZMod 7337687933)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1834421983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1834421983, 1)] : List FactorBlock).map factorBlockValue).prod) = 7337687933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_1834421983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7337687933) ^ 3668843966 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7337687933) ^ 4 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_7615115047 : Nat.Prime 7615115047 := by
  apply lucas_primality 7615115047 (3 : ZMod 7615115047)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (7, 1), (11, 1), (29, 1), (2339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (7, 1), (11, 1), (29, 1), (2339, 1)] : List FactorBlock).map factorBlockValue).prod) = 7615115047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_2339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7615115047) ^ 3807557523 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7615115047) ^ 2538371682 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7615115047) ^ 1087873578 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7615115047) ^ 692283186 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7615115047) ^ 262590174 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7615115047) ^ 3255714 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_7697020187 : Nat.Prime 7697020187 := by
  apply lucas_primality 7697020187 (2 : ZMod 7697020187)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3848510093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3848510093, 1)] : List FactorBlock).map factorBlockValue).prod) = 7697020187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3848510093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7697020187) ^ 3848510093 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7697020187) ^ 2 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_9313006279 : Nat.Prime 9313006279 := by
  apply lucas_primality 9313006279 (3 : ZMod 9313006279)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (16001729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (16001729, 1)] : List FactorBlock).map factorBlockValue).prod) = 9313006279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_97
      · exact prime_ninetyCJ_16001729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9313006279) ^ 4656503139 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9313006279) ^ 3104335426 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9313006279) ^ 96010374 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9313006279) ^ 582 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_10051216723 : Nat.Prime 10051216723 := by
  apply lucas_primality 10051216723 (2 : ZMod 10051216723)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (5030639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (5030639, 1)] : List FactorBlock).map factorBlockValue).prod) = 10051216723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_37
      · exact prime_ninetyCJ_5030639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10051216723) ^ 5025608361 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10051216723) ^ 3350405574 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10051216723) ^ 271654506 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10051216723) ^ 1998 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_11330791951 : Nat.Prime 11330791951 := by
  apply lucas_primality 11330791951 (6 : ZMod 11330791951)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (75538613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (75538613, 1)] : List FactorBlock).map factorBlockValue).prod) = 11330791951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_75538613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 11330791951) ^ 5665395975 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 11330791951) ^ 3776930650 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 11330791951) ^ 2266158390 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 11330791951) ^ 150 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_12652990601 : Nat.Prime 12652990601 := by
  apply lucas_primality 12652990601 (3 : ZMod 12652990601)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (149, 1), (424597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (149, 1), (424597, 1)] : List FactorBlock).map factorBlockValue).prod) = 12652990601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_149
      · exact prime_ninetyCJ_424597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12652990601) ^ 6326495300 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 12652990601) ^ 2530598120 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 12652990601) ^ 84919400 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 12652990601) ^ 29800 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_13786913143 : Nat.Prime 13786913143 := by
  apply lucas_primality 13786913143 (3 : ZMod 13786913143)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (26411711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (26411711, 1)] : List FactorBlock).map factorBlockValue).prod) = 13786913143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_26411711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13786913143) ^ 6893456571 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 13786913143) ^ 4595637714 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 13786913143) ^ 475410798 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 13786913143) ^ 522 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_14222525003 : Nat.Prime 14222525003 := by
  apply lucas_primality 14222525003 (2 : ZMod 14222525003)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1015894643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1015894643, 1)] : List FactorBlock).map factorBlockValue).prod) = 14222525003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_1015894643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14222525003) ^ 7111262501 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 14222525003) ^ 2031789286 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 14222525003) ^ 14 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_15120654371 : Nat.Prime 15120654371 := by
  apply lucas_primality 15120654371 (6 : ZMod 15120654371)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1721, 1), (878597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1721, 1), (878597, 1)] : List FactorBlock).map factorBlockValue).prod) = 15120654371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_1721
      · exact prime_ninetyCJ_878597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 15120654371) ^ 7560327185 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 15120654371) ^ 3024130874 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 15120654371) ^ 8785970 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 15120654371) ^ 17210 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_17974206721 : Nat.Prime 17974206721 := by
  apply lucas_primality 17974206721 (17 : ZMod 17974206721)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 1), (19, 1), (31, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 1), (19, 1), (31, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 17974206721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_31
      · exact prime_ninetyCJ_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 17974206721) ^ 8987103360 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 17974206721) ^ 5991402240 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 17974206721) ^ 3594841344 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 17974206721) ^ 946010880 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 17974206721) ^ 579813120 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 17974206721) ^ 20355840 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_18057209543 : Nat.Prime 18057209543 := by
  apply lucas_primality 18057209543 (5 : ZMod 18057209543)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (103, 1), (239, 1), (12647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (103, 1), (239, 1), (12647, 1)] : List FactorBlock).map factorBlockValue).prod) = 18057209543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_103
      · exact prime_ninetyCJ_239
      · exact prime_ninetyCJ_12647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18057209543) ^ 9028604771 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 18057209543) ^ 622662398 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 18057209543) ^ 175312714 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 18057209543) ^ 75553178 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 18057209543) ^ 1427786 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_21903920009 : Nat.Prime 21903920009 := by
  apply lucas_primality 21903920009 (3 : ZMod 21903920009)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2737990001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2737990001, 1)] : List FactorBlock).map factorBlockValue).prod) = 21903920009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_2737990001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 21903920009) ^ 10951960004 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 21903920009) ^ 8 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_22853596301 : Nat.Prime 22853596301 := by
  apply lucas_primality 22853596301 (2 : ZMod 22853596301)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7639, 1), (29917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7639, 1), (29917, 1)] : List FactorBlock).map factorBlockValue).prod) = 22853596301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7639
      · exact prime_ninetyCJ_29917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22853596301) ^ 11426798150 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 22853596301) ^ 4570719260 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 22853596301) ^ 2991700 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 22853596301) ^ 763900 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_25305981203 : Nat.Prime 25305981203 := by
  apply lucas_primality 25305981203 (2 : ZMod 25305981203)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12652990601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12652990601, 1)] : List FactorBlock).map factorBlockValue).prod) = 25305981203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_12652990601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 25305981203) ^ 12652990601 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25305981203) ^ 2 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_27256488367 : Nat.Prime 27256488367 := by
  apply lucas_primality 27256488367 (3 : ZMod 27256488367)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (643, 1), (7064927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (643, 1), (7064927, 1)] : List FactorBlock).map factorBlockValue).prod) = 27256488367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_643
      · exact prime_ninetyCJ_7064927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 27256488367) ^ 13628244183 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 27256488367) ^ 9085496122 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 27256488367) ^ 42389562 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 27256488367) ^ 3858 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_31237921933 : Nat.Prime 31237921933 := by
  apply lucas_primality 31237921933 (5 : ZMod 31237921933)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (371880023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (371880023, 1)] : List FactorBlock).map factorBlockValue).prod) = 31237921933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_371880023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31237921933) ^ 15618960966 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 31237921933) ^ 10412640644 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 31237921933) ^ 4462560276 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 31237921933) ^ 84 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_31693282799 : Nat.Prime 31693282799 := by
  apply lucas_primality 31693282799 (23 : ZMod 31693282799)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2699, 1), (5871301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2699, 1), (5871301, 1)] : List FactorBlock).map factorBlockValue).prod) = 31693282799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_2699
      · exact prime_ninetyCJ_5871301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 31693282799) ^ 15846641399 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (23 : ZMod 31693282799) ^ 11742602 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (23 : ZMod 31693282799) ^ 5398 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_35765914001 : Nat.Prime 35765914001 := by
  apply lucas_primality 35765914001 (6 : ZMod 35765914001)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (17882957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (17882957, 1)] : List FactorBlock).map factorBlockValue).prod) = 35765914001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_17882957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 35765914001) ^ 17882957000 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 35765914001) ^ 7153182800 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 35765914001) ^ 2000 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_40358306297 : Nat.Prime 40358306297 := by
  apply lucas_primality 40358306297 (3 : ZMod 40358306297)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (11, 1), (19, 1), (47, 2), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (11, 1), (19, 1), (47, 2), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 40358306297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_47
      · exact prime_ninetyCJ_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40358306297) ^ 20179153148 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40358306297) ^ 5765472328 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40358306297) ^ 3668936936 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40358306297) ^ 2124121384 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40358306297) ^ 858687368 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 40358306297) ^ 180978952 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_42102296813 : Nat.Prime 42102296813 := by
  apply lucas_primality 42102296813 (2 : ZMod 42102296813)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (457633661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (457633661, 1)] : List FactorBlock).map factorBlockValue).prod) = 42102296813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_23
      · exact prime_ninetyCJ_457633661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42102296813) ^ 21051148406 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 42102296813) ^ 1830534644 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 42102296813) ^ 92 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_45158112773 : Nat.Prime 45158112773 := by
  apply lucas_primality 45158112773 (2 : ZMod 45158112773)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19309, 1), (584677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19309, 1), (584677, 1)] : List FactorBlock).map factorBlockValue).prod) = 45158112773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_19309
      · exact prime_ninetyCJ_584677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45158112773) ^ 22579056386 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 45158112773) ^ 2338708 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 45158112773) ^ 77236 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_53093028787 : Nat.Prime 53093028787 := by
  apply lucas_primality 53093028787 (13 : ZMod 53093028787)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (8609, 1), (146837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (8609, 1), (146837, 1)] : List FactorBlock).map factorBlockValue).prod) = 53093028787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_8609
      · exact prime_ninetyCJ_146837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 53093028787) ^ 26546514393 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 53093028787) ^ 17697676262 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 53093028787) ^ 7584718398 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 53093028787) ^ 6167154 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 53093028787) ^ 361578 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_59831827441 : Nat.Prime 59831827441 := by
  apply lucas_primality 59831827441 (19 : ZMod 59831827441)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (11, 1), (3237653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (11, 1), (3237653, 1)] : List FactorBlock).map factorBlockValue).prod) = 59831827441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_3237653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 59831827441) ^ 29915913720 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 59831827441) ^ 19943942480 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 59831827441) ^ 11966365488 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 59831827441) ^ 8547403920 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 59831827441) ^ 5439257040 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 59831827441) ^ 18480 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_66456831821 : Nat.Prime 66456831821 := by
  apply lucas_primality 66456831821 (3 : ZMod 66456831821)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (59, 1), (56319349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (59, 1), (56319349, 1)] : List FactorBlock).map factorBlockValue).prod) = 66456831821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_59
      · exact prime_ninetyCJ_56319349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66456831821) ^ 33228415910 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 66456831821) ^ 13291366364 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 66456831821) ^ 1126386980 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 66456831821) ^ 1180 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_76368940909 : Nat.Prime 76368940909 := by
  apply lucas_primality 76368940909 (2 : ZMod 76368940909)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (509, 1), (961777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (509, 1), (961777, 1)] : List FactorBlock).map factorBlockValue).prod) = 76368940909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_509
      · exact prime_ninetyCJ_961777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76368940909) ^ 38184470454 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76368940909) ^ 25456313636 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76368940909) ^ 5874533916 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76368940909) ^ 150037212 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76368940909) ^ 79404 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_77656990819 : Nat.Prime 77656990819 := by
  apply lucas_primality 77656990819 (2 : ZMod 77656990819)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (5653, 1), (208141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (5653, 1), (208141, 1)] : List FactorBlock).map factorBlockValue).prod) = 77656990819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_5653
      · exact prime_ninetyCJ_208141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 77656990819) ^ 38828495409 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 77656990819) ^ 25885663606 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 77656990819) ^ 7059726438 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 77656990819) ^ 13737306 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 77656990819) ^ 373098 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_85113580939 : Nat.Prime 85113580939 := by
  apply lucas_primality 85113580939 (3 : ZMod 85113580939)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (103, 1), (2930303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (103, 1), (2930303, 1)] : List FactorBlock).map factorBlockValue).prod) = 85113580939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_47
      · exact prime_ninetyCJ_103
      · exact prime_ninetyCJ_2930303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 85113580939) ^ 42556790469 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 85113580939) ^ 28371193646 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 85113580939) ^ 1810927254 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 85113580939) ^ 826345446 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 85113580939) ^ 29046 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_87570130463 : Nat.Prime 87570130463 := by
  apply lucas_primality 87570130463 (5 : ZMod 87570130463)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1301, 1), (33654931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1301, 1), (33654931, 1)] : List FactorBlock).map factorBlockValue).prod) = 87570130463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_1301
      · exact prime_ninetyCJ_33654931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 87570130463) ^ 43785065231 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 87570130463) ^ 67309862 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 87570130463) ^ 2602 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_94697184697 : Nat.Prime 94697184697 := by
  apply lucas_primality 94697184697 (7 : ZMod 94697184697)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (229, 1), (17230201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (229, 1), (17230201, 1)] : List FactorBlock).map factorBlockValue).prod) = 94697184697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_229
      · exact prime_ninetyCJ_17230201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 94697184697) ^ 47348592348 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 94697184697) ^ 31565728232 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 94697184697) ^ 413524824 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 94697184697) ^ 5496 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_98982267859 : Nat.Prime 98982267859 := by
  apply lucas_primality 98982267859 (2 : ZMod 98982267859)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (2657, 1), (48131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (2657, 1), (48131, 1)] : List FactorBlock).map factorBlockValue).prod) = 98982267859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_43
      · exact prime_ninetyCJ_2657
      · exact prime_ninetyCJ_48131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 98982267859) ^ 49491133929 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 98982267859) ^ 32994089286 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 98982267859) ^ 2301913206 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 98982267859) ^ 37253394 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 98982267859) ^ 2056518 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_108343257259 : Nat.Prime 108343257259 := by
  apply lucas_primality 108343257259 (2 : ZMod 108343257259)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (18057209543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (18057209543, 1)] : List FactorBlock).map factorBlockValue).prod) = 108343257259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_18057209543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 108343257259) ^ 54171628629 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 108343257259) ^ 36114419086 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 108343257259) ^ 6 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_147725226629 : Nat.Prime 147725226629 := by
  apply lucas_primality 147725226629 (2 : ZMod 147725226629)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (41, 1), (4437259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (41, 1), (4437259, 1)] : List FactorBlock).map factorBlockValue).prod) = 147725226629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_41
      · exact prime_ninetyCJ_4437259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 147725226629) ^ 73862613314 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 147725226629) ^ 21103603804 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 147725226629) ^ 5093973332 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 147725226629) ^ 3603054308 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 147725226629) ^ 33292 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_172857306653 : Nat.Prime 172857306653 := by
  apply lucas_primality 172857306653 (2 : ZMod 172857306653)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (1297, 1), (774853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (1297, 1), (774853, 1)] : List FactorBlock).map factorBlockValue).prod) = 172857306653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_43
      · exact prime_ninetyCJ_1297
      · exact prime_ninetyCJ_774853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 172857306653) ^ 86428653326 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 172857306653) ^ 4019937364 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 172857306653) ^ 133274716 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 172857306653) ^ 223084 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_178335622963 : Nat.Prime 178335622963 := by
  apply lucas_primality 178335622963 (2 : ZMod 178335622963)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (409, 1), (3460543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (409, 1), (3460543, 1)] : List FactorBlock).map factorBlockValue).prod) = 178335622963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_409
      · exact prime_ninetyCJ_3460543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178335622963) ^ 89167811481 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 178335622963) ^ 59445207654 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 178335622963) ^ 25476517566 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 178335622963) ^ 436028418 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 178335622963) ^ 51534 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_233394757109 : Nat.Prime 233394757109 := by
  apply lucas_primality 233394757109 (2 : ZMod 233394757109)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (1031, 1), (407153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (1031, 1), (407153, 1)] : List FactorBlock).map factorBlockValue).prod) = 233394757109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_139
      · exact prime_ninetyCJ_1031
      · exact prime_ninetyCJ_407153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 233394757109) ^ 116697378554 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 233394757109) ^ 1679098972 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 233394757109) ^ 226377068 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 233394757109) ^ 573236 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_233890202717 : Nat.Prime 233890202717 := by
  apply lucas_primality 233890202717 (2 : ZMod 233890202717)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (59, 1), (67, 1), (510067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (59, 1), (67, 1), (510067, 1)] : List FactorBlock).map factorBlockValue).prod) = 233890202717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_59
      · exact prime_ninetyCJ_67
      · exact prime_ninetyCJ_510067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 233890202717) ^ 116945101358 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 233890202717) ^ 8065179404 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 233890202717) ^ 3964240724 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 233890202717) ^ 3490898548 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 233890202717) ^ 458548 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_262462494953 : Nat.Prime 262462494953 := by
  apply lucas_primality 262462494953 (3 : ZMod 262462494953)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (23, 1), (29110747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (23, 1), (29110747, 1)] : List FactorBlock).map factorBlockValue).prod) = 262462494953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_23
      · exact prime_ninetyCJ_29110747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 262462494953) ^ 131231247476 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 262462494953) ^ 37494642136 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 262462494953) ^ 11411412824 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 262462494953) ^ 9016 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_279979712539 : Nat.Prime 279979712539 := by
  apply lucas_primality 279979712539 (2 : ZMod 279979712539)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (223, 1), (209252401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (223, 1), (209252401, 1)] : List FactorBlock).map factorBlockValue).prod) = 279979712539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_223
      · exact prime_ninetyCJ_209252401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 279979712539) ^ 139989856269 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 279979712539) ^ 93326570846 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 279979712539) ^ 1255514406 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 279979712539) ^ 1338 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_295305253703 : Nat.Prime 295305253703 := by
  apply lucas_primality 295305253703 (5 : ZMod 295305253703)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383, 1), (1601, 1), (240797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383, 1), (1601, 1), (240797, 1)] : List FactorBlock).map factorBlockValue).prod) = 295305253703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_383
      · exact prime_ninetyCJ_1601
      · exact prime_ninetyCJ_240797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 295305253703) ^ 147652626851 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 295305253703) ^ 771031994 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 295305253703) ^ 184450502 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 295305253703) ^ 1226366 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_315766880347 : Nat.Prime 315766880347 := by
  apply lucas_primality 315766880347 (2 : ZMod 315766880347)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (229, 1), (5344553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (229, 1), (5344553, 1)] : List FactorBlock).map factorBlockValue).prod) = 315766880347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_43
      · exact prime_ninetyCJ_229
      · exact prime_ninetyCJ_5344553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 315766880347) ^ 157883440173 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 315766880347) ^ 105255626782 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 315766880347) ^ 7343415822 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 315766880347) ^ 1378894674 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 315766880347) ^ 59082 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_316056205609 : Nat.Prime 316056205609 := by
  apply lucas_primality 316056205609 (17 : ZMod 316056205609)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 1), (92090969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 1), (92090969, 1)] : List FactorBlock).map factorBlockValue).prod) = 316056205609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_92090969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 316056205609) ^ 158028102804 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 316056205609) ^ 105352068536 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 316056205609) ^ 28732382328 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 316056205609) ^ 24312015816 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 316056205609) ^ 3432 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_347852383261 : Nat.Prime 347852383261 := by
  apply lucas_primality 347852383261 (13 : ZMod 347852383261)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (5797539721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (5797539721, 1)] : List FactorBlock).map factorBlockValue).prod) = 347852383261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_5797539721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 347852383261) ^ 173926191630 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 347852383261) ^ 115950794420 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 347852383261) ^ 69570476652 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 347852383261) ^ 60 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_381510033769 : Nat.Prime 381510033769 := by
  apply lucas_primality 381510033769 (11 : ZMod 381510033769)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (557, 1), (9513017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (557, 1), (9513017, 1)] : List FactorBlock).map factorBlockValue).prod) = 381510033769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_557
      · exact prime_ninetyCJ_9513017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 381510033769) ^ 190755016884 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 381510033769) ^ 127170011256 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 381510033769) ^ 684937224 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 381510033769) ^ 40104 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_447225412903 : Nat.Prime 447225412903 := by
  apply lucas_primality 447225412903 (3 : ZMod 447225412903)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1049, 1), (71055833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1049, 1), (71055833, 1)] : List FactorBlock).map factorBlockValue).prod) = 447225412903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_1049
      · exact prime_ninetyCJ_71055833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 447225412903) ^ 223612706451 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 447225412903) ^ 149075137634 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 447225412903) ^ 426334998 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 447225412903) ^ 6294 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_462040960393 : Nat.Prime 462040960393 := by
  apply lucas_primality 462040960393 (5 : ZMod 462040960393)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (131, 1), (4453321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (131, 1), (4453321, 1)] : List FactorBlock).map factorBlockValue).prod) = 462040960393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_131
      · exact prime_ninetyCJ_4453321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 462040960393) ^ 231020480196 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 462040960393) ^ 154013653464 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 462040960393) ^ 42003723672 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 462040960393) ^ 3527030232 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 462040960393) ^ 103752 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_487105996733 : Nat.Prime 487105996733 := by
  apply lucas_primality 487105996733 (2 : ZMod 487105996733)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (7253, 1), (578959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (7253, 1), (578959, 1)] : List FactorBlock).map factorBlockValue).prod) = 487105996733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_7253
      · exact prime_ninetyCJ_578959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 487105996733) ^ 243552998366 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 487105996733) ^ 16796758508 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 487105996733) ^ 67159244 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 487105996733) ^ 841348 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_488387893967 : Nat.Prime 488387893967 := by
  apply lucas_primality 488387893967 (5 : ZMod 488387893967)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (223, 1), (156434303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (223, 1), (156434303, 1)] : List FactorBlock).map factorBlockValue).prod) = 488387893967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_223
      · exact prime_ninetyCJ_156434303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 488387893967) ^ 244193946983 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 488387893967) ^ 69769699138 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 488387893967) ^ 2190080242 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 488387893967) ^ 3122 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_540286620527 : Nat.Prime 540286620527 := by
  apply lucas_primality 540286620527 (5 : ZMod 540286620527)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1831, 1), (147538673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1831, 1), (147538673, 1)] : List FactorBlock).map factorBlockValue).prod) = 540286620527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_1831
      · exact prime_ninetyCJ_147538673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 540286620527) ^ 270143310263 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 540286620527) ^ 295077346 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 540286620527) ^ 3662 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_682834270241 : Nat.Prime 682834270241 := by
  apply lucas_primality 682834270241 (3 : ZMod 682834270241)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (373, 1), (1571, 1), (7283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (373, 1), (1571, 1), (7283, 1)] : List FactorBlock).map factorBlockValue).prod) = 682834270241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_373
      · exact prime_ninetyCJ_1571
      · exact prime_ninetyCJ_7283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 682834270241) ^ 341417135120 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 682834270241) ^ 136566854048 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 682834270241) ^ 1830654880 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 682834270241) ^ 434649440 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 682834270241) ^ 93757280 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_826735377437 : Nat.Prime 826735377437 := by
  apply lucas_primality 826735377437 (2 : ZMod 826735377437)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (227, 1), (2341, 1), (388937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (227, 1), (2341, 1), (388937, 1)] : List FactorBlock).map factorBlockValue).prod) = 826735377437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_227
      · exact prime_ninetyCJ_2341
      · exact prime_ninetyCJ_388937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 826735377437) ^ 413367688718 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 826735377437) ^ 3642006068 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 826735377437) ^ 353154796 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 826735377437) ^ 2125628 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_962186389259 : Nat.Prime 962186389259 := by
  apply lucas_primality 962186389259 (2 : ZMod 962186389259)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (1523, 1), (1636711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (1523, 1), (1636711, 1)] : List FactorBlock).map factorBlockValue).prod) = 962186389259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_193
      · exact prime_ninetyCJ_1523
      · exact prime_ninetyCJ_1636711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 962186389259) ^ 481093194629 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 962186389259) ^ 4985421706 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 962186389259) ^ 631770446 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 962186389259) ^ 587878 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1046121149317 : Nat.Prime 1046121149317 := by
  apply lucas_primality 1046121149317 (5 : ZMod 1046121149317)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4219, 1), (20662897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4219, 1), (20662897, 1)] : List FactorBlock).map factorBlockValue).prod) = 1046121149317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_4219
      · exact prime_ninetyCJ_20662897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1046121149317) ^ 523060574658 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1046121149317) ^ 348707049772 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1046121149317) ^ 247954764 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1046121149317) ^ 50628 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1178568135637 : Nat.Prime 1178568135637 := by
  apply lucas_primality 1178568135637 (2 : ZMod 1178568135637)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (83, 1), (3767, 1), (10133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (83, 1), (3767, 1), (10133, 1)] : List FactorBlock).map factorBlockValue).prod) = 1178568135637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_31
      · exact prime_ninetyCJ_83
      · exact prime_ninetyCJ_3767
      · exact prime_ninetyCJ_10133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1178568135637) ^ 589284067818 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1178568135637) ^ 392856045212 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1178568135637) ^ 38018326956 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1178568135637) ^ 14199616092 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1178568135637) ^ 312866508 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1178568135637) ^ 116309892 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1187002551491 : Nat.Prime 1187002551491 := by
  apply lucas_primality 1187002551491 (2 : ZMod 1187002551491)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (3109, 1), (5454223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (3109, 1), (5454223, 1)] : List FactorBlock).map factorBlockValue).prod) = 1187002551491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_3109
      · exact prime_ninetyCJ_5454223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1187002551491) ^ 593501275745 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1187002551491) ^ 237400510298 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1187002551491) ^ 169571793070 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1187002551491) ^ 381795610 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1187002551491) ^ 217630 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_2041079389421 : Nat.Prime 2041079389421 := by
  apply lucas_primality 2041079389421 (3 : ZMod 2041079389421)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3319, 1), (30748409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3319, 1), (30748409, 1)] : List FactorBlock).map factorBlockValue).prod) = 2041079389421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_3319
      · exact prime_ninetyCJ_30748409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2041079389421) ^ 1020539694710 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2041079389421) ^ 408215877884 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2041079389421) ^ 614968180 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2041079389421) ^ 66380 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_4097896307101 : Nat.Prime 4097896307101 := by
  apply lucas_primality 4097896307101 (6 : ZMod 4097896307101)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (1307, 1), (1161239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (1307, 1), (1161239, 1)] : List FactorBlock).map factorBlockValue).prod) = 4097896307101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_1307
      · exact prime_ninetyCJ_1161239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4097896307101) ^ 2048948153550 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 4097896307101) ^ 1365965435700 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 4097896307101) ^ 819579261420 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 4097896307101) ^ 3135345300 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 4097896307101) ^ 3528900 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_4401458344021 : Nat.Prime 4401458344021 := by
  apply lucas_primality 4401458344021 (2 : ZMod 4401458344021)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (61, 1), (109, 1), (11032883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (61, 1), (109, 1), (11032883, 1)] : List FactorBlock).map factorBlockValue).prod) = 4401458344021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_61
      · exact prime_ninetyCJ_109
      · exact prime_ninetyCJ_11032883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4401458344021) ^ 2200729172010 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4401458344021) ^ 1467152781340 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4401458344021) ^ 880291668804 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4401458344021) ^ 72155054820 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4401458344021) ^ 40380351780 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4401458344021) ^ 398940 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_5079505232449 : Nat.Prime 5079505232449 := by
  apply lucas_primality 5079505232449 (17 : ZMod 5079505232449)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (2939528491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (2939528491, 1)] : List FactorBlock).map factorBlockValue).prod) = 5079505232449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_2939528491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 5079505232449) ^ 2539752616224 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 5079505232449) ^ 1693168410816 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (17 : ZMod 5079505232449) ^ 1728 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_5683803846247 : Nat.Prime 5683803846247 := by
  apply lucas_primality 5683803846247 (6 : ZMod 5683803846247)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (315766880347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (315766880347, 1)] : List FactorBlock).map factorBlockValue).prod) = 5683803846247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_315766880347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 5683803846247) ^ 2841901923123 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 5683803846247) ^ 1894601282082 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 5683803846247) ^ 18 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_6668325710587 : Nat.Prime 6668325710587 := by
  apply lucas_primality 6668325710587 (2 : ZMod 6668325710587)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (47, 1), (1451, 1), (1810747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (47, 1), (1451, 1), (1810747, 1)] : List FactorBlock).map factorBlockValue).prod) = 6668325710587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_47
      · exact prime_ninetyCJ_1451
      · exact prime_ninetyCJ_1810747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6668325710587) ^ 3334162855293 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6668325710587) ^ 2222775236862 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6668325710587) ^ 141879270438 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6668325710587) ^ 4595675886 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6668325710587) ^ 3682638 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_7305104863393 : Nat.Prime 7305104863393 := by
  apply lucas_primality 7305104863393 (10 : ZMod 7305104863393)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (4967, 1), (2188583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (4967, 1), (2188583, 1)] : List FactorBlock).map factorBlockValue).prod) = 7305104863393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_4967
      · exact prime_ninetyCJ_2188583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 7305104863393) ^ 3652552431696 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 7305104863393) ^ 2435034954464 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 7305104863393) ^ 1043586409056 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 7305104863393) ^ 1470727776 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 7305104863393) ^ 3337824 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_8159726304227 : Nat.Prime 8159726304227 := by
  apply lucas_primality 8159726304227 (2 : ZMod 8159726304227)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (337, 1), (1729488407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (337, 1), (1729488407, 1)] : List FactorBlock).map factorBlockValue).prod) = 8159726304227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_337
      · exact prime_ninetyCJ_1729488407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8159726304227) ^ 4079863152113 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8159726304227) ^ 1165675186318 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8159726304227) ^ 24212837698 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8159726304227) ^ 4718 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_8294565740479 : Nat.Prime 8294565740479 := by
  apply lucas_primality 8294565740479 (7 : ZMod 8294565740479)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (224197, 1), (6166129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (224197, 1), (6166129, 1)] : List FactorBlock).map factorBlockValue).prod) = 8294565740479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_224197
      · exact prime_ninetyCJ_6166129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8294565740479) ^ 4147282870239 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8294565740479) ^ 2764855246826 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8294565740479) ^ 36996774 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8294565740479) ^ 1345182 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_10045315410773 : Nat.Prime 10045315410773 := by
  apply lucas_primality 10045315410773 (2 : ZMod 10045315410773)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (147725226629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (147725226629, 1)] : List FactorBlock).map factorBlockValue).prod) = 10045315410773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_17
      · exact prime_ninetyCJ_147725226629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10045315410773) ^ 5022657705386 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10045315410773) ^ 590900906516 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10045315410773) ^ 68 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_17169609358193 : Nat.Prime 17169609358193 := by
  apply lucas_primality 17169609358193 (3 : ZMod 17169609358193)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (61, 1), (18899, 1), (40471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (61, 1), (18899, 1), (40471, 1)] : List FactorBlock).map factorBlockValue).prod) = 17169609358193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_23
      · exact prime_ninetyCJ_61
      · exact prime_ninetyCJ_18899
      · exact prime_ninetyCJ_40471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17169609358193) ^ 8584804679096 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 17169609358193) ^ 746504754704 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 17169609358193) ^ 281469005872 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 17169609358193) ^ 908493008 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 17169609358193) ^ 424244752 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_22735215384989 : Nat.Prime 22735215384989 := by
  apply lucas_primality 22735215384989 (2 : ZMod 22735215384989)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5683803846247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5683803846247, 1)] : List FactorBlock).map factorBlockValue).prod) = 22735215384989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5683803846247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 22735215384989) ^ 11367607692494 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 22735215384989) ^ 4 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_25338885959027 : Nat.Prime 25338885959027 := by
  apply lucas_primality 25338885959027 (2 : ZMod 25338885959027)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (253103, 1), (50056471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (253103, 1), (50056471, 1)] : List FactorBlock).map factorBlockValue).prod) = 25338885959027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_253103
      · exact prime_ninetyCJ_50056471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25338885959027) ^ 12669442979513 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25338885959027) ^ 100112942 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 25338885959027) ^ 506206 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_33228596993509 : Nat.Prime 33228596993509 := by
  apply lucas_primality 33228596993509 (6 : ZMod 33228596993509)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (59, 1), (2234906981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (59, 1), (2234906981, 1)] : List FactorBlock).map factorBlockValue).prod) = 33228596993509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_59
      · exact prime_ninetyCJ_2234906981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 33228596993509) ^ 16614298496754 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 33228596993509) ^ 11076198997836 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 33228596993509) ^ 4746942427644 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 33228596993509) ^ 563196559212 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 33228596993509) ^ 14868 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_44748077918891 : Nat.Prime 44748077918891 := by
  apply lucas_primality 44748077918891 (2 : ZMod 44748077918891)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (523, 1), (2281, 1), (3751003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (523, 1), (2281, 1), (3751003, 1)] : List FactorBlock).map factorBlockValue).prod) = 44748077918891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_523
      · exact prime_ninetyCJ_2281
      · exact prime_ninetyCJ_3751003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44748077918891) ^ 22374038959445 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44748077918891) ^ 8949615583778 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44748077918891) ^ 85560378430 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44748077918891) ^ 19617745690 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44748077918891) ^ 11929630 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_53663402740747 : Nat.Prime 53663402740747 := by
  apply lucas_primality 53663402740747 (2 : ZMod 53663402740747)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (29, 1), (31, 1), (523616911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (29, 1), (31, 1), (523616911, 1)] : List FactorBlock).map factorBlockValue).prod) = 53663402740747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_31
      · exact prime_ninetyCJ_523616911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53663402740747) ^ 26831701370373 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53663402740747) ^ 17887800913582 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53663402740747) ^ 2824389617934 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53663402740747) ^ 1850462163474 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53663402740747) ^ 1731077507766 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53663402740747) ^ 102486 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_57349425254227 : Nat.Prime 57349425254227 := by
  apply lucas_primality 57349425254227 (3 : ZMod 57349425254227)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (101, 1), (711548987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (101, 1), (711548987, 1)] : List FactorBlock).map factorBlockValue).prod) = 57349425254227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_101
      · exact prime_ninetyCJ_711548987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 57349425254227) ^ 28674712627113 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 57349425254227) ^ 19116475084742 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 57349425254227) ^ 8192775036318 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 57349425254227) ^ 3018390802854 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 57349425254227) ^ 567816091626 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 57349425254227) ^ 80598 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_61533968720381 : Nat.Prime 61533968720381 := by
  apply lucas_primality 61533968720381 (2 : ZMod 61533968720381)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (61, 1), (71, 1), (349, 1), (156577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (61, 1), (71, 1), (349, 1), (156577, 1)] : List FactorBlock).map factorBlockValue).prod) = 61533968720381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_61
      · exact prime_ninetyCJ_71
      · exact prime_ninetyCJ_349
      · exact prime_ninetyCJ_156577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61533968720381) ^ 30766984360190 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61533968720381) ^ 12306793744076 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61533968720381) ^ 4733382209260 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61533968720381) ^ 1008753585580 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61533968720381) ^ 866675615780 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61533968720381) ^ 176315096620 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61533968720381) ^ 392994940 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_62144713126043 : Nat.Prime 62144713126043 := by
  apply lucas_primality 62144713126043 (2 : ZMod 62144713126043)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53597, 1), (579740593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53597, 1), (579740593, 1)] : List FactorBlock).map factorBlockValue).prod) = 62144713126043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_53597
      · exact prime_ninetyCJ_579740593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 62144713126043) ^ 31072356563021 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 62144713126043) ^ 1159481186 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 62144713126043) ^ 107194 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_68850834552551 : Nat.Prime 68850834552551 := by
  apply lucas_primality 68850834552551 (7 : ZMod 68850834552551)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (137, 1), (10051216723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (137, 1), (10051216723, 1)] : List FactorBlock).map factorBlockValue).prod) = 68850834552551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_137
      · exact prime_ninetyCJ_10051216723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 68850834552551) ^ 34425417276275 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 68850834552551) ^ 13770166910510 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 68850834552551) ^ 502560836150 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 68850834552551) ^ 6850 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_70558224094507 : Nat.Prime 70558224094507 := by
  apply lucas_primality 70558224094507 (2 : ZMod 70558224094507)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (347, 1), (6833, 1), (4959701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (347, 1), (6833, 1), (4959701, 1)] : List FactorBlock).map factorBlockValue).prod) = 70558224094507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_347
      · exact prime_ninetyCJ_6833
      · exact prime_ninetyCJ_4959701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70558224094507) ^ 35279112047253 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 70558224094507) ^ 23519408031502 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 70558224094507) ^ 203337821598 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 70558224094507) ^ 10326097482 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 70558224094507) ^ 14226306 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_80171491536977 : Nat.Prime 80171491536977 := by
  apply lucas_primality 80171491536977 (3 : ZMod 80171491536977)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (401, 1), (7333, 1), (243431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (401, 1), (7333, 1), (243431, 1)] : List FactorBlock).map factorBlockValue).prod) = 80171491536977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_401
      · exact prime_ninetyCJ_7333
      · exact prime_ninetyCJ_243431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 80171491536977) ^ 40085745768488 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 80171491536977) ^ 11453070219568 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 80171491536977) ^ 199928906576 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 80171491536977) ^ 10932973072 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 80171491536977) ^ 329339696 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_83305780969403 : Nat.Prime 83305780969403 := by
  apply lucas_primality 83305780969403 (2 : ZMod 83305780969403)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (682834270241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (682834270241, 1)] : List FactorBlock).map factorBlockValue).prod) = 83305780969403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_61
      · exact prime_ninetyCJ_682834270241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 83305780969403) ^ 41652890484701 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 83305780969403) ^ 1365668540482 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 83305780969403) ^ 122 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_112034379248591 : Nat.Prime 112034379248591 := by
  apply lucas_primality 112034379248591 (7 : ZMod 112034379248591)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (487105996733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (487105996733, 1)] : List FactorBlock).map factorBlockValue).prod) = 112034379248591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_23
      · exact prime_ninetyCJ_487105996733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 112034379248591) ^ 56017189624295 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 112034379248591) ^ 22406875849718 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 112034379248591) ^ 4871059967330 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 112034379248591) ^ 230 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_194188929245569 : Nat.Prime 194188929245569 := by
  apply lucas_primality 194188929245569 (7 : ZMod 194188929245569)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (229, 1), (2113, 1), (348367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (229, 1), (2113, 1), (348367, 1)] : List FactorBlock).map factorBlockValue).prod) = 194188929245569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_229
      · exact prime_ninetyCJ_2113
      · exact prime_ninetyCJ_348367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 194188929245569) ^ 97094464622784 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 194188929245569) ^ 64729643081856 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 194188929245569) ^ 847986590592 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 194188929245569) ^ 91902001536 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 194188929245569) ^ 557426304 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_209796014043181 : Nat.Prime 209796014043181 := by
  apply lucas_primality 209796014043181 (6 : ZMod 209796014043181)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (17, 1), (22853596301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (17, 1), (22853596301, 1)] : List FactorBlock).map factorBlockValue).prod) = 209796014043181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_17
      · exact prime_ninetyCJ_22853596301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 209796014043181) ^ 104898007021590 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 209796014043181) ^ 69932004681060 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 209796014043181) ^ 41959202808636 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 209796014043181) ^ 12340942002540 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 209796014043181) ^ 9180 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_212557183778263 : Nat.Prime 212557183778263 := by
  apply lucas_primality 212557183778263 (3 : ZMod 212557183778263)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (85691, 1), (4093247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (85691, 1), (4093247, 1)] : List FactorBlock).map factorBlockValue).prod) = 212557183778263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_101
      · exact prime_ninetyCJ_85691
      · exact prime_ninetyCJ_4093247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 212557183778263) ^ 106278591889131 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 212557183778263) ^ 70852394592754 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 212557183778263) ^ 2104526572062 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 212557183778263) ^ 2480507682 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 212557183778263) ^ 51928746 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_291385680279391 : Nat.Prime 291385680279391 := by
  apply lucas_primality 291385680279391 (21 : ZMod 291385680279391)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (67, 1), (653, 1), (1033, 1), (23879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (67, 1), (653, 1), (1033, 1), (23879, 1)] : List FactorBlock).map factorBlockValue).prod) = 291385680279391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_67
      · exact prime_ninetyCJ_653
      · exact prime_ninetyCJ_1033
      · exact prime_ninetyCJ_23879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 291385680279391) ^ 145692840139695 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (21 : ZMod 291385680279391) ^ 97128560093130 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (21 : ZMod 291385680279391) ^ 58277136055878 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (21 : ZMod 291385680279391) ^ 4349040004170 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (21 : ZMod 291385680279391) ^ 446226156630 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (21 : ZMod 291385680279391) ^ 282077134830 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (21 : ZMod 291385680279391) ^ 12202591410 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_302183990091019 : Nat.Prime 302183990091019 := by
  apply lucas_primality 302183990091019 (2 : ZMod 302183990091019)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (4663, 1), (5801, 1), (88661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (4663, 1), (5801, 1), (88661, 1)] : List FactorBlock).map factorBlockValue).prod) = 302183990091019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_4663
      · exact prime_ninetyCJ_5801
      · exact prime_ninetyCJ_88661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 302183990091019) ^ 151091995045509 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 302183990091019) ^ 100727996697006 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 302183990091019) ^ 43169141441574 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 302183990091019) ^ 64804630086 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 302183990091019) ^ 52091706618 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 302183990091019) ^ 3408307938 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_308081079383881 : Nat.Prime 308081079383881 := by
  apply lucas_primality 308081079383881 (14 : ZMod 308081079383881)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (233394757109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (233394757109, 1)] : List FactorBlock).map factorBlockValue).prod) = 308081079383881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_233394757109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 308081079383881) ^ 154040539691940 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 308081079383881) ^ 102693693127960 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 308081079383881) ^ 61616215876776 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 308081079383881) ^ 28007370853080 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 308081079383881) ^ 1320 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_369203812322287 : Nat.Prime 369203812322287 := by
  apply lucas_primality 369203812322287 (6 : ZMod 369203812322287)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61533968720381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61533968720381, 1)] : List FactorBlock).map factorBlockValue).prod) = 369203812322287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_61533968720381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 369203812322287) ^ 184601906161143 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 369203812322287) ^ 123067937440762 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 369203812322287) ^ 6 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_412070624596633 : Nat.Prime 412070624596633 := by
  apply lucas_primality 412070624596633 (11 : ZMod 412070624596633)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17169609358193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17169609358193, 1)] : List FactorBlock).map factorBlockValue).prod) = 412070624596633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_17169609358193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 412070624596633) ^ 206035312298316 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 412070624596633) ^ 137356874865544 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (11 : ZMod 412070624596633) ^ 24 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_522450503165959 : Nat.Prime 522450503165959 := by
  apply lucas_primality 522450503165959 (3 : ZMod 522450503165959)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (743, 1), (6893760103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (743, 1), (6893760103, 1)] : List FactorBlock).map factorBlockValue).prod) = 522450503165959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_17
      · exact prime_ninetyCJ_743
      · exact prime_ninetyCJ_6893760103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 522450503165959) ^ 261225251582979 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 522450503165959) ^ 174150167721986 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 522450503165959) ^ 30732382539174 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 522450503165959) ^ 703163530506 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 522450503165959) ^ 75786 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_656566163363447 : Nat.Prime 656566163363447 := by
  apply lucas_primality 656566163363447 (5 : ZMod 656566163363447)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (29, 1), (85113580939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (29, 1), (85113580939, 1)] : List FactorBlock).map factorBlockValue).prod) = 656566163363447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_85113580939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 656566163363447) ^ 328283081681723 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 656566163363447) ^ 93795166194778 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 656566163363447) ^ 34556113861234 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 656566163363447) ^ 22640212529774 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 656566163363447) ^ 7714 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_672206275491547 : Nat.Prime 672206275491547 := by
  apply lucas_primality 672206275491547 (3 : ZMod 672206275491547)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (112034379248591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (112034379248591, 1)] : List FactorBlock).map factorBlockValue).prod) = 672206275491547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_112034379248591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 672206275491547) ^ 336103137745773 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 672206275491547) ^ 224068758497182 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 672206275491547) ^ 6 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_760419697497533 : Nat.Prime 760419697497533 := by
  apply lucas_primality 760419697497533 (2 : ZMod 760419697497533)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (149, 1), (23459, 1), (688447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (149, 1), (23459, 1), (688447, 1)] : List FactorBlock).map factorBlockValue).prod) = 760419697497533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_79
      · exact prime_ninetyCJ_149
      · exact prime_ninetyCJ_23459
      · exact prime_ninetyCJ_688447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 760419697497533) ^ 380209848748766 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 760419697497533) ^ 9625565791108 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 760419697497533) ^ 5103487902668 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 760419697497533) ^ 32414838548 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 760419697497533) ^ 1104543556 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_792615195391697 : Nat.Prime 792615195391697 := by
  apply lucas_primality 792615195391697 (3 : ZMod 792615195391697)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1097, 1), (45158112773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1097, 1), (45158112773, 1)] : List FactorBlock).map factorBlockValue).prod) = 792615195391697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_1097
      · exact prime_ninetyCJ_45158112773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 792615195391697) ^ 396307597695848 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 792615195391697) ^ 722529804368 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 792615195391697) ^ 17552 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_899442990972073 : Nat.Prime 899442990972073 := by
  apply lucas_primality 899442990972073 (10 : ZMod 899442990972073)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (541, 1), (7697020187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (541, 1), (7697020187, 1)] : List FactorBlock).map factorBlockValue).prod) = 899442990972073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_541
      · exact prime_ninetyCJ_7697020187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 899442990972073) ^ 449721495486036 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 899442990972073) ^ 299814330324024 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 899442990972073) ^ 1662556360392 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 899442990972073) ^ 116856 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_942811776704653 : Nat.Prime 942811776704653 := by
  apply lucas_primality 942811776704653 (2 : ZMod 942811776704653)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (67, 1), (31693282799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (67, 1), (31693282799, 1)] : List FactorBlock).map factorBlockValue).prod) = 942811776704653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_37
      · exact prime_ninetyCJ_67
      · exact prime_ninetyCJ_31693282799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 942811776704653) ^ 471405888352326 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 942811776704653) ^ 314270592234884 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 942811776704653) ^ 25481399370396 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 942811776704653) ^ 14071817562756 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 942811776704653) ^ 29748 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_982533860992429 : Nat.Prime 982533860992429 := by
  apply lucas_primality 982533860992429 (2 : ZMod 982533860992429)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (101, 1), (137, 1), (21529, 1), (274853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (101, 1), (137, 1), (21529, 1), (274853, 1)] : List FactorBlock).map factorBlockValue).prod) = 982533860992429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_101
      · exact prime_ninetyCJ_137
      · exact prime_ninetyCJ_21529
      · exact prime_ninetyCJ_274853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 982533860992429) ^ 491266930496214 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 982533860992429) ^ 327511286997476 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 982533860992429) ^ 9728058029628 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 982533860992429) ^ 7171780007244 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 982533860992429) ^ 45637691532 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 982533860992429) ^ 3574761276 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1159167439754801 : Nat.Prime 1159167439754801 := by
  apply lucas_primality 1159167439754801 (12 : ZMod 1159167439754801)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (7, 1), (6997, 1), (59166553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (7, 1), (6997, 1), (59166553, 1)] : List FactorBlock).map factorBlockValue).prod) = 1159167439754801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_6997
      · exact prime_ninetyCJ_59166553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 1159167439754801) ^ 579583719877400 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (12 : ZMod 1159167439754801) ^ 231833487950960 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (12 : ZMod 1159167439754801) ^ 165595348536400 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (12 : ZMod 1159167439754801) ^ 165666348400 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (12 : ZMod 1159167439754801) ^ 19591600 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1192952858123617 : Nat.Prime 1192952858123617 := by
  apply lucas_primality 1192952858123617 (10 : ZMod 1192952858123617)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (540286620527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (540286620527, 1)] : List FactorBlock).map factorBlockValue).prod) = 1192952858123617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_23
      · exact prime_ninetyCJ_540286620527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1192952858123617) ^ 596476429061808 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1192952858123617) ^ 397650952707872 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1192952858123617) ^ 51867515570592 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1192952858123617) ^ 2208 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1679143190181659 : Nat.Prime 1679143190181659 := by
  apply lucas_primality 1679143190181659 (2 : ZMod 1679143190181659)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (109, 1), (1531, 1), (264790529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (109, 1), (1531, 1), (264790529, 1)] : List FactorBlock).map factorBlockValue).prod) = 1679143190181659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_109
      · exact prime_ninetyCJ_1531
      · exact prime_ninetyCJ_264790529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1679143190181659) ^ 839571595090829 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679143190181659) ^ 88375957377982 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679143190181659) ^ 15404983396162 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679143190181659) ^ 1096762371118 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679143190181659) ^ 6341402 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_3021839900910191 : Nat.Prime 3021839900910191 := by
  apply lucas_primality 3021839900910191 (7 : ZMod 3021839900910191)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (302183990091019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (302183990091019, 1)] : List FactorBlock).map factorBlockValue).prod) = 3021839900910191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_302183990091019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3021839900910191) ^ 1510919950455095 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3021839900910191) ^ 604367980182038 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3021839900910191) ^ 10 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_4402999408712293 : Nat.Prime 4402999408712293 := by
  apply lucas_primality 4402999408712293 (2 : ZMod 4402999408712293)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2153471, 1), (56794607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2153471, 1), (56794607, 1)] : List FactorBlock).map factorBlockValue).prod) = 4402999408712293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_2153471
      · exact prime_ninetyCJ_56794607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4402999408712293) ^ 2201499704356146 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4402999408712293) ^ 1467666469570764 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4402999408712293) ^ 2044605852 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4402999408712293) ^ 77524956 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_4818434013754103 : Nat.Prime 4818434013754103 := by
  apply lucas_primality 4818434013754103 (10 : ZMod 4818434013754103)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (47, 1), (1046121149317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (47, 1), (1046121149317, 1)] : List FactorBlock).map factorBlockValue).prod) = 4818434013754103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_47
      · exact prime_ninetyCJ_1046121149317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 4818434013754103) ^ 2409217006877051 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 4818434013754103) ^ 688347716250586 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 4818434013754103) ^ 102519872633066 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 4818434013754103) ^ 4606 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_5930872795958293 : Nat.Prime 5930872795958293 := by
  apply lucas_primality 5930872795958293 (5 : ZMod 5930872795958293)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (13, 1), (151, 1), (269, 1), (2437, 1), (18289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (13, 1), (151, 1), (269, 1), (2437, 1), (18289, 1)] : List FactorBlock).map factorBlockValue).prod) = 5930872795958293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_151
      · exact prime_ninetyCJ_269
      · exact prime_ninetyCJ_2437
      · exact prime_ninetyCJ_18289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5930872795958293) ^ 2965436397979146 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5930872795958293) ^ 1976957598652764 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5930872795958293) ^ 847267542279756 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5930872795958293) ^ 456220984304484 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5930872795958293) ^ 39277303284492 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5930872795958293) ^ 22047854260068 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5930872795958293) ^ 2433677798916 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5930872795958293) ^ 324286335828 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_13910009277057613 : Nat.Prime 13910009277057613 := by
  apply lucas_primality 13910009277057613 (2 : ZMod 13910009277057613)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1159167439754801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1159167439754801, 1)] : List FactorBlock).map factorBlockValue).prod) = 13910009277057613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_1159167439754801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13910009277057613) ^ 6955004638528806 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13910009277057613) ^ 4636669759019204 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13910009277057613) ^ 12 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_15208393949950661 : Nat.Prime 15208393949950661 := by
  apply lucas_primality 15208393949950661 (2 : ZMod 15208393949950661)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (760419697497533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (760419697497533, 1)] : List FactorBlock).map factorBlockValue).prod) = 15208393949950661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_760419697497533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15208393949950661) ^ 7604196974975330 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 15208393949950661) ^ 3041678789990132 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 15208393949950661) ^ 20 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_20056674324455207 : Nat.Prime 20056674324455207 := by
  apply lucas_primality 20056674324455207 (5 : ZMod 20056674324455207)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (105899, 1), (94697184697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (105899, 1), (94697184697, 1)] : List FactorBlock).map factorBlockValue).prod) = 20056674324455207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_105899
      · exact prime_ninetyCJ_94697184697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 20056674324455207) ^ 10028337162227603 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 20056674324455207) ^ 189394369394 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 20056674324455207) ^ 211798 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_20922048704194787 : Nat.Prime 20922048704194787 := by
  apply lucas_primality 20922048704194787 (2 : ZMod 20922048704194787)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4049, 1), (6389, 1), (404383613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4049, 1), (6389, 1), (404383613, 1)] : List FactorBlock).map factorBlockValue).prod) = 20922048704194787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_4049
      · exact prime_ninetyCJ_6389
      · exact prime_ninetyCJ_404383613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20922048704194787) ^ 10461024352097393 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20922048704194787) ^ 5167213806914 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20922048704194787) ^ 3274698498074 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 20922048704194787) ^ 51738122 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_21473151446225107 : Nat.Prime 21473151446225107 := by
  apply lucas_primality 21473151446225107 (2 : ZMod 21473151446225107)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1192952858123617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1192952858123617, 1)] : List FactorBlock).map factorBlockValue).prod) = 21473151446225107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_1192952858123617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21473151446225107) ^ 10736575723112553 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 21473151446225107) ^ 7157717148741702 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 21473151446225107) ^ 18 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_21525931405343707 : Nat.Prime 21525931405343707 := by
  apply lucas_primality 21525931405343707 (2 : ZMod 21525931405343707)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (6143, 1), (53093028787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (6143, 1), (53093028787, 1)] : List FactorBlock).map factorBlockValue).prod) = 21525931405343707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_6143
      · exact prime_ninetyCJ_53093028787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21525931405343707) ^ 10762965702671853 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 21525931405343707) ^ 7175310468447902 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 21525931405343707) ^ 1956902855031246 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 21525931405343707) ^ 3504139899942 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 21525931405343707) ^ 405438 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_43065264743766751 : Nat.Prime 43065264743766751 := by
  apply lucas_primality 43065264743766751 (3 : ZMod 43065264743766751)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (17077, 1), (3362437957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (17077, 1), (3362437957, 1)] : List FactorBlock).map factorBlockValue).prod) = 43065264743766751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_17077
      · exact prime_ninetyCJ_3362437957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 43065264743766751) ^ 21532632371883375 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 43065264743766751) ^ 14355088247922250 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 43065264743766751) ^ 8613052948753350 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 43065264743766751) ^ 2521828467750 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 43065264743766751) ^ 12807750 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_55640037108230453 : Nat.Prime 55640037108230453 := by
  apply lucas_primality 55640037108230453 (2 : ZMod 55640037108230453)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13910009277057613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13910009277057613, 1)] : List FactorBlock).map factorBlockValue).prod) = 55640037108230453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_13910009277057613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 55640037108230453) ^ 27820018554115226 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 55640037108230453) ^ 4 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_74689472324268877 : Nat.Prime 74689472324268877 := by
  apply lucas_primality 74689472324268877 (5 : ZMod 74689472324268877)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (617, 1), (347852383261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (617, 1), (347852383261, 1)] : List FactorBlock).map factorBlockValue).prod) = 74689472324268877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_617
      · exact prime_ninetyCJ_347852383261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 74689472324268877) ^ 37344736162134438 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 74689472324268877) ^ 24896490774756292 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 74689472324268877) ^ 2575499045664444 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 74689472324268877) ^ 121052629374828 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 74689472324268877) ^ 214716 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_128703842212633943 : Nat.Prime 128703842212633943 := by
  apply lucas_primality 128703842212633943 (5 : ZMod 128703842212633943)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1601, 1), (1270579, 1), (31635049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1601, 1), (1270579, 1), (31635049, 1)] : List FactorBlock).map factorBlockValue).prod) = 128703842212633943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_1601
      · exact prime_ninetyCJ_1270579
      · exact prime_ninetyCJ_31635049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 128703842212633943) ^ 64351921106316971 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 128703842212633943) ^ 80389657846742 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 128703842212633943) ^ 101295426898 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 128703842212633943) ^ 4068393958 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_155611771171533487 : Nat.Prime 155611771171533487 := by
  apply lucas_primality 155611771171533487 (3 : ZMod 155611771171533487)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (67, 1), (701, 1), (3229254433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (67, 1), (701, 1), (3229254433, 1)] : List FactorBlock).map factorBlockValue).prod) = 155611771171533487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_67
      · exact prime_ninetyCJ_701
      · exact prime_ninetyCJ_3229254433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 155611771171533487) ^ 77805885585766743 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 155611771171533487) ^ 51870590390511162 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 155611771171533487) ^ 8190093219554394 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 155611771171533487) ^ 2322563748828858 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 155611771171533487) ^ 221985408233286 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 155611771171533487) ^ 48188142 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_179337987831867407 : Nat.Prime 179337987831867407 := by
  apply lucas_primality 179337987831867407 (5 : ZMod 179337987831867407)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (59669, 1), (13786913143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (59669, 1), (13786913143, 1)] : List FactorBlock).map factorBlockValue).prod) = 179337987831867407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_109
      · exact prime_ninetyCJ_59669
      · exact prime_ninetyCJ_13786913143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 179337987831867407) ^ 89668993915933703 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 179337987831867407) ^ 1645302640659334 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 179337987831867407) ^ 3005547065174 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 179337987831867407) ^ 13007842 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_305810472232639163 : Nat.Prime 305810472232639163 := by
  apply lucas_primality 305810472232639163 (2 : ZMod 305810472232639163)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (4893197, 1), (130747007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (4893197, 1), (130747007, 1)] : List FactorBlock).map factorBlockValue).prod) = 305810472232639163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_239
      · exact prime_ninetyCJ_4893197
      · exact prime_ninetyCJ_130747007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 305810472232639163) ^ 152905236116319581 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 305810472232639163) ^ 1279541724822758 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 305810472232639163) ^ 62497069346 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 305810472232639163) ^ 2338948166 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_393849464959254019 : Nat.Prime 393849464959254019 := by
  apply lucas_primality 393849464959254019 (2 : ZMod 393849464959254019)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (47, 1), (1289, 1), (37087, 1), (204301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (47, 1), (1289, 1), (37087, 1), (204301, 1)] : List FactorBlock).map factorBlockValue).prod) = 393849464959254019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_47
      · exact prime_ninetyCJ_1289
      · exact prime_ninetyCJ_37087
      · exact prime_ninetyCJ_204301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 393849464959254019) ^ 196924732479627009 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 393849464959254019) ^ 131283154986418006 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 393849464959254019) ^ 35804496814477638 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 393849464959254019) ^ 30296112689173386 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 393849464959254019) ^ 8379775850196894 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 393849464959254019) ^ 305546520526962 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 393849464959254019) ^ 10619609700414 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 393849464959254019) ^ 1927790196618 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_704479905393966881 : Nat.Prime 704479905393966881 := by
  apply lucas_primality 704479905393966881 (3 : ZMod 704479905393966881)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (4402999408712293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (4402999408712293, 1)] : List FactorBlock).map factorBlockValue).prod) = 704479905393966881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_4402999408712293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 704479905393966881) ^ 352239952696983440 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 704479905393966881) ^ 140895981078793376 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 704479905393966881) ^ 160 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_844107402681037009 : Nat.Prime 844107402681037009 := by
  apply lucas_primality 844107402681037009 (19 : ZMod 844107402681037009)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (53, 1), (421, 1), (87570130463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (53, 1), (421, 1), (87570130463, 1)] : List FactorBlock).map factorBlockValue).prod) = 844107402681037009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_53
      · exact prime_ninetyCJ_421
      · exact prime_ninetyCJ_87570130463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 844107402681037009) ^ 422053701340518504 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 844107402681037009) ^ 281369134227012336 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 844107402681037009) ^ 15926554767566736 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 844107402681037009) ^ 2005005707080848 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 844107402681037009) ^ 9639216 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_930413335916373217 : Nat.Prime 930413335916373217 := by
  apply lucas_primality 930413335916373217 (5 : ZMod 930413335916373217)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (442469, 1), (21903920009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (442469, 1), (21903920009, 1)] : List FactorBlock).map factorBlockValue).prod) = 930413335916373217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_442469
      · exact prime_ninetyCJ_21903920009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 930413335916373217) ^ 465206667958186608 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 930413335916373217) ^ 310137778638791072 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 930413335916373217) ^ 2102776320864 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 930413335916373217) ^ 42477024 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_930881859214963577 : Nat.Prime 930881859214963577 := by
  apply lucas_primality 930881859214963577 (3 : ZMod 930881859214963577)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (83, 1), (97, 1), (138319, 1), (104489563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (83, 1), (97, 1), (138319, 1), (104489563, 1)] : List FactorBlock).map factorBlockValue).prod) = 930881859214963577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_83
      · exact prime_ninetyCJ_97
      · exact prime_ninetyCJ_138319
      · exact prime_ninetyCJ_104489563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 930881859214963577) ^ 465440929607481788 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 930881859214963577) ^ 11215444086927272 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 930881859214963577) ^ 9596720198092408 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 930881859214963577) ^ 6729963773704 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 930881859214963577) ^ 8908850152 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1011661601846270371 : Nat.Prime 1011661601846270371 := by
  apply lucas_primality 1011661601846270371 (3 : ZMod 1011661601846270371)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (157, 1), (563, 1), (381510033769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (157, 1), (563, 1), (381510033769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1011661601846270371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_157
      · exact prime_ninetyCJ_563
      · exact prime_ninetyCJ_381510033769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1011661601846270371) ^ 505830800923135185 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1011661601846270371) ^ 337220533948756790 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1011661601846270371) ^ 202332320369254074 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1011661601846270371) ^ 6443704470358410 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1011661601846270371) ^ 1796912259051990 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1011661601846270371) ^ 2651730 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1205827412825469029 : Nat.Prime 1205827412825469029 := by
  apply lucas_primality 1205827412825469029 (3 : ZMod 1205827412825469029)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (43065264743766751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (43065264743766751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205827412825469029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_43065264743766751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1205827412825469029) ^ 602913706412734514 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1205827412825469029) ^ 172261058975067004 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1205827412825469029) ^ 28 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1257929436488310881 : Nat.Prime 1257929436488310881 := by
  apply lucas_primality 1257929436488310881 (12 : ZMod 1257929436488310881)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (331, 1), (2099, 1), (1616582321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (331, 1), (2099, 1), (1616582321, 1)] : List FactorBlock).map factorBlockValue).prod) = 1257929436488310881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_331
      · exact prime_ninetyCJ_2099
      · exact prime_ninetyCJ_1616582321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 1257929436488310881) ^ 628964718244155440 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (12 : ZMod 1257929436488310881) ^ 251585887297662176 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (12 : ZMod 1257929436488310881) ^ 179704205212615840 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (12 : ZMod 1257929436488310881) ^ 3800391046792480 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (12 : ZMod 1257929436488310881) ^ 599299398041120 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (12 : ZMod 1257929436488310881) ^ 778141280 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_2492794337607102533 : Nat.Prime 2492794337607102533 := by
  apply lucas_primality 2492794337607102533 (2 : ZMod 2492794337607102533)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (661, 1), (942811776704653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (661, 1), (942811776704653, 1)] : List FactorBlock).map factorBlockValue).prod) = 2492794337607102533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_661
      · exact prime_ninetyCJ_942811776704653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2492794337607102533) ^ 1246397168803551266 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2492794337607102533) ^ 3771247106818612 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2492794337607102533) ^ 2644 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_4520445595122178471 : Nat.Prime 4520445595122178471 := by
  apply lucas_primality 4520445595122178471 (6 : ZMod 4520445595122178471)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (21525931405343707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (21525931405343707, 1)] : List FactorBlock).map factorBlockValue).prod) = 4520445595122178471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_21525931405343707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4520445595122178471) ^ 2260222797561089235 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 4520445595122178471) ^ 1506815198374059490 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 4520445595122178471) ^ 904089119024435694 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 4520445595122178471) ^ 645777942160311210 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 4520445595122178471) ^ 210 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_4987964371917315617 : Nat.Prime 4987964371917315617 := by
  apply lucas_primality 4987964371917315617 (3 : ZMod 4987964371917315617)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (79, 1), (7393, 1), (430691, 1), (619669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (79, 1), (7393, 1), (430691, 1), (619669, 1)] : List FactorBlock).map factorBlockValue).prod) = 4987964371917315617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_79
      · exact prime_ninetyCJ_7393
      · exact prime_ninetyCJ_430691
      · exact prime_ninetyCJ_619669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4987964371917315617) ^ 2493982185958657808 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4987964371917315617) ^ 63138789517940704 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4987964371917315617) ^ 674687457313312 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4987964371917315617) ^ 11581306254176 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4987964371917315617) ^ 8049401167264 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_5582480015498239303 : Nat.Prime 5582480015498239303 := by
  apply lucas_primality 5582480015498239303 (3 : ZMod 5582480015498239303)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (930413335916373217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (930413335916373217, 1)] : List FactorBlock).map factorBlockValue).prod) = 5582480015498239303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_930413335916373217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5582480015498239303) ^ 2791240007749119651 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5582480015498239303) ^ 1860826671832746434 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5582480015498239303) ^ 6 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_9498137275803155363 : Nat.Prime 9498137275803155363 := by
  apply lucas_primality 9498137275803155363 (2 : ZMod 9498137275803155363)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (677, 1), (369203812322287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (677, 1), (369203812322287, 1)] : List FactorBlock).map factorBlockValue).prod) = 9498137275803155363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_677
      · exact prime_ninetyCJ_369203812322287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9498137275803155363) ^ 4749068637901577681 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9498137275803155363) ^ 499901961884376598 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9498137275803155363) ^ 14029744868246906 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9498137275803155363) ^ 25726 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_21435583782221690297 : Nat.Prime 21435583782221690297 := by
  apply lucas_primality 21435583782221690297 (3 : ZMod 21435583782221690297)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (15024749, 1), (178335622963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (15024749, 1), (178335622963, 1)] : List FactorBlock).map factorBlockValue).prod) = 21435583782221690297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_15024749
      · exact prime_ninetyCJ_178335622963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 21435583782221690297) ^ 10717791891110845148 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 21435583782221690297) ^ 1426684983704 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 21435583782221690297) ^ 120197992 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_31804289112194472953 : Nat.Prime 31804289112194472953 := by
  apply lucas_primality 31804289112194472953 (3 : ZMod 31804289112194472953)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (305810472232639163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (305810472232639163, 1)] : List FactorBlock).map factorBlockValue).prod) = 31804289112194472953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_305810472232639163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31804289112194472953) ^ 15902144556097236476 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 31804289112194472953) ^ 2446483777861113304 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 31804289112194472953) ^ 104 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_59833263752006014939 : Nat.Prime 59833263752006014939 := by
  apply lucas_primality 59833263752006014939 (3 : ZMod 59833263752006014939)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13759, 1), (26591, 1), (27256488367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13759, 1), (26591, 1), (27256488367, 1)] : List FactorBlock).map factorBlockValue).prod) = 59833263752006014939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_13759
      · exact prime_ninetyCJ_26591
      · exact prime_ninetyCJ_27256488367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 59833263752006014939) ^ 29916631876003007469 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59833263752006014939) ^ 19944421250668671646 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59833263752006014939) ^ 4348663693001382 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59833263752006014939) ^ 2250132140649318 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59833263752006014939) ^ 2195193414 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_75982103529540238553 : Nat.Prime 75982103529540238553 := by
  apply lucas_primality 75982103529540238553 (3 : ZMod 75982103529540238553)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (152833, 1), (62144713126043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (152833, 1), (62144713126043, 1)] : List FactorBlock).map factorBlockValue).prod) = 75982103529540238553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_152833
      · exact prime_ninetyCJ_62144713126043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 75982103529540238553) ^ 37991051764770119276 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 75982103529540238553) ^ 497157705008344 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 75982103529540238553) ^ 1222664 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_83476550475812065609 : Nat.Prime 83476550475812065609 := by
  apply lucas_primality 83476550475812065609 (19 : ZMod 83476550475812065609)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (102322639, 1), (11330791951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (102322639, 1), (11330791951, 1)] : List FactorBlock).map factorBlockValue).prod) = 83476550475812065609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_102322639
      · exact prime_ninetyCJ_11330791951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 83476550475812065609) ^ 41738275237906032804 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 83476550475812065609) ^ 27825516825270688536 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 83476550475812065609) ^ 815817020472 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (19 : ZMod 83476550475812065609) ^ 7367230008 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_153172955171156848703 : Nat.Prime 153172955171156848703 := by
  apply lucas_primality 153172955171156848703 (5 : ZMod 153172955171156848703)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113933, 1), (672206275491547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113933, 1), (672206275491547, 1)] : List FactorBlock).map factorBlockValue).prod) = 153172955171156848703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_113933
      · exact prime_ninetyCJ_672206275491547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 153172955171156848703) ^ 76586477585578424351 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 153172955171156848703) ^ 1344412550983094 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 153172955171156848703) ^ 227866 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_225707314162607025137 : Nat.Prime 225707314162607025137 := by
  apply lucas_primality 225707314162607025137 (3 : ZMod 225707314162607025137)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (73, 1), (4679, 1), (13033, 1), (102221831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (73, 1), (4679, 1), (13033, 1), (102221831, 1)] : List FactorBlock).map factorBlockValue).prod) = 225707314162607025137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_31
      · exact prime_ninetyCJ_73
      · exact prime_ninetyCJ_4679
      · exact prime_ninetyCJ_13033
      · exact prime_ninetyCJ_102221831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 225707314162607025137) ^ 112853657081303512568 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 225707314162607025137) ^ 7280881102019581456 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 225707314162607025137) ^ 3091881015926123632 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 225707314162607025137) ^ 48238365924899984 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 225707314162607025137) ^ 17318139657991792 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 225707314162607025137) ^ 2208014784656 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_256080329290627525391 : Nat.Prime 256080329290627525391 := by
  apply lucas_primality 256080329290627525391 (7 : ZMod 256080329290627525391)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (29, 1), (1693, 1), (15551, 1), (684489613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (29, 1), (1693, 1), (15551, 1), (684489613, 1)] : List FactorBlock).map factorBlockValue).prod) = 256080329290627525391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_29
      · exact prime_ninetyCJ_1693
      · exact prime_ninetyCJ_15551
      · exact prime_ninetyCJ_684489613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 256080329290627525391) ^ 128040164645313762695 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 256080329290627525391) ^ 51216065858125505078 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 256080329290627525391) ^ 36582904184375360770 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 256080329290627525391) ^ 8830356182435431910 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 256080329290627525391) ^ 151258316178752230 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 256080329290627525391) ^ 16467129399435890 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 256080329290627525391) ^ 374118649030 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_284944118274094660891 : Nat.Prime 284944118274094660891 := by
  apply lucas_primality 284944118274094660891 (2 : ZMod 284944118274094660891)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (9498137275803155363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (9498137275803155363, 1)] : List FactorBlock).map factorBlockValue).prod) = 284944118274094660891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_9498137275803155363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 284944118274094660891) ^ 142472059137047330445 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 284944118274094660891) ^ 94981372758031553630 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 284944118274094660891) ^ 56988823654818932178 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 284944118274094660891) ^ 30 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_376787767201810850359 : Nat.Prime 376787767201810850359 := by
  apply lucas_primality 376787767201810850359 (3 : ZMod 376787767201810850359)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (57269, 1), (33228596993509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (57269, 1), (33228596993509, 1)] : List FactorBlock).map factorBlockValue).prod) = 376787767201810850359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_57269
      · exact prime_ninetyCJ_33228596993509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 376787767201810850359) ^ 188393883600905425179 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 376787767201810850359) ^ 125595922400603616786 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 376787767201810850359) ^ 34253433381982804578 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 376787767201810850359) ^ 6579262204714782 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 376787767201810850359) ^ 11339262 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_484153488554725460197 : Nat.Prime 484153488554725460197 := by
  apply lucas_primality 484153488554725460197 (6 : ZMod 484153488554725460197)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (2646107, 1), (462040960393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (2646107, 1), (462040960393, 1)] : List FactorBlock).map factorBlockValue).prod) = 484153488554725460197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_2646107
      · exact prime_ninetyCJ_462040960393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 484153488554725460197) ^ 242076744277362730098 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 484153488554725460197) ^ 161384496184908486732 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 484153488554725460197) ^ 44013953504975041836 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 484153488554725460197) ^ 182968220315628 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 484153488554725460197) ^ 1047858372 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_684971051212230752339 : Nat.Prime 684971051212230752339 := by
  apply lucas_primality 684971051212230752339 (2 : ZMod 684971051212230752339)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (8179, 1), (212557183778263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (8179, 1), (212557183778263, 1)] : List FactorBlock).map factorBlockValue).prod) = 684971051212230752339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_197
      · exact prime_ninetyCJ_8179
      · exact prime_ninetyCJ_212557183778263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 684971051212230752339) ^ 342485525606115376169 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 684971051212230752339) ^ 3477010412244826154 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 684971051212230752339) ^ 83747530408635622 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 684971051212230752339) ^ 3222526 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1482516483480214413331 : Nat.Prime 1482516483480214413331 := by
  apply lucas_primality 1482516483480214413331 (3 : ZMod 1482516483480214413331)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (315870367, 1), (14222525003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (315870367, 1), (14222525003, 1)] : List FactorBlock).map factorBlockValue).prod) = 1482516483480214413331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_315870367
      · exact prime_ninetyCJ_14222525003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1482516483480214413331) ^ 741258241740107206665 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1482516483480214413331) ^ 494172161160071471110 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1482516483480214413331) ^ 296503296696042882666 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1482516483480214413331) ^ 134774225770928583030 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1482516483480214413331) ^ 4693433250990 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1482516483480214413331) ^ 104237221110 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1518981853067498178019 : Nat.Prime 1518981853067498178019 := by
  apply lucas_primality 1518981853067498178019 (2 : ZMod 1518981853067498178019)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (43, 1), (73, 1), (24691, 1), (98982267859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (43, 1), (73, 1), (24691, 1), (98982267859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1518981853067498178019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_43
      · exact prime_ninetyCJ_73
      · exact prime_ninetyCJ_24691
      · exact prime_ninetyCJ_98982267859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1518981853067498178019) ^ 759490926533749089009 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1518981853067498178019) ^ 506327284355832726006 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1518981853067498178019) ^ 138089259369772561638 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1518981853067498178019) ^ 35325159373662748326 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1518981853067498178019) ^ 20807970589965728466 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1518981853067498178019) ^ 61519657084261398 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1518981853067498178019) ^ 15345999702 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1712454305740181313671 : Nat.Prime 1712454305740181313671 := by
  apply lucas_primality 1712454305740181313671 (7 : ZMod 1712454305740181313671)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (137, 1), (38703011, 1), (1899786293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (137, 1), (38703011, 1), (1899786293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1712454305740181313671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_17
      · exact prime_ninetyCJ_137
      · exact prime_ninetyCJ_38703011
      · exact prime_ninetyCJ_1899786293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1712454305740181313671) ^ 856227152870090656835 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1712454305740181313671) ^ 342490861148036262734 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1712454305740181313671) ^ 100732606220010665510 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1712454305740181313671) ^ 12499666465256797910 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1712454305740181313671) ^ 44246022763970 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1712454305740181313671) ^ 901393126190 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_1840590308451631902349 : Nat.Prime 1840590308451631902349 := by
  apply lucas_primality 1840590308451631902349 (6 : ZMod 1840590308451631902349)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (12401, 1), (13043, 1), (51487, 1), (189877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (12401, 1), (13043, 1), (51487, 1), (189877, 1)] : List FactorBlock).map factorBlockValue).prod) = 1840590308451631902349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_97
      · exact prime_ninetyCJ_12401
      · exact prime_ninetyCJ_13043
      · exact prime_ninetyCJ_51487
      · exact prime_ninetyCJ_189877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1840590308451631902349) ^ 920295154225815951174 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1840590308451631902349) ^ 613530102817210634116 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1840590308451631902349) ^ 18975157819088988684 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1840590308451631902349) ^ 148422732719267148 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1840590308451631902349) ^ 141117097941549636 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1840590308451631902349) ^ 35748641568777204 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1840590308451631902349) ^ 9693592738728924 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_2219410926540983004961 : Nat.Prime 2219410926540983004961 := by
  apply lucas_primality 2219410926540983004961 (7 : ZMod 2219410926540983004961)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (13, 1), (17, 1), (20922048704194787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (13, 1), (17, 1), (20922048704194787, 1)] : List FactorBlock).map factorBlockValue).prod) = 2219410926540983004961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_17
      · exact prime_ninetyCJ_20922048704194787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2219410926540983004961) ^ 1109705463270491502480 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2219410926540983004961) ^ 739803642180327668320 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2219410926540983004961) ^ 443882185308196600992 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2219410926540983004961) ^ 170723917426229461920 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2219410926540983004961) ^ 130553583914175470880 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2219410926540983004961) ^ 106080 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_3170975381681431293103 : Nat.Prime 3170975381681431293103 := by
  apply lucas_primality 3170975381681431293103 (7 : ZMod 3170975381681431293103)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (311, 1), (4765759, 1), (7277011717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (311, 1), (4765759, 1), (7277011717, 1)] : List FactorBlock).map factorBlockValue).prod) = 3170975381681431293103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_311
      · exact prime_ninetyCJ_4765759
      · exact prime_ninetyCJ_7277011717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3170975381681431293103) ^ 1585487690840715646551 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3170975381681431293103) ^ 1056991793893810431034 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3170975381681431293103) ^ 452996483097347327586 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3170975381681431293103) ^ 10196062320519071682 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3170975381681431293103) ^ 665366289332178 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3170975381681431293103) ^ 435752408406 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_3338932095755135487617 : Nat.Prime 3338932095755135487617 := by
  apply lucas_primality 3338932095755135487617 (3 : ZMod 3338932095755135487617)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (124337, 1), (209796014043181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (124337, 1), (209796014043181, 1)] : List FactorBlock).map factorBlockValue).prod) = 3338932095755135487617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_124337
      · exact prime_ninetyCJ_209796014043181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3338932095755135487617) ^ 1669466047877567743808 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3338932095755135487617) ^ 26853889797527168 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3338932095755135487617) ^ 15915136 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_4282134842441259743441 : Nat.Prime 4282134842441259743441 := by
  apply lucas_primality 4282134842441259743441 (3 : ZMod 4282134842441259743441)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (37, 1), (43, 1), (130178273, 1), (258441151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (37, 1), (43, 1), (130178273, 1), (258441151, 1)] : List FactorBlock).map factorBlockValue).prod) = 4282134842441259743441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_37
      · exact prime_ninetyCJ_43
      · exact prime_ninetyCJ_130178273
      · exact prime_ninetyCJ_258441151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4282134842441259743441) ^ 2141067421220629871720 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4282134842441259743441) ^ 856426968488251948688 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4282134842441259743441) ^ 115733374120034047120 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4282134842441259743441) ^ 99584531219564180080 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4282134842441259743441) ^ 32894389699280 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4282134842441259743441) ^ 16569090587440 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_6654316178473901249177 : Nat.Prime 6654316178473901249177 := by
  apply lucas_primality 6654316178473901249177 (3 : ZMod 6654316178473901249177)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (149, 1), (5582480015498239303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (149, 1), (5582480015498239303, 1)] : List FactorBlock).map factorBlockValue).prod) = 6654316178473901249177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_149
      · exact prime_ninetyCJ_5582480015498239303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6654316178473901249177) ^ 3327158089236950624588 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6654316178473901249177) ^ 44659840123985914424 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6654316178473901249177) ^ 1192 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_6695509519676630186497 : Nat.Prime 6695509519676630186497 := by
  apply lucas_primality 6695509519676630186497 (7 : ZMod 6695509519676630186497)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (241, 1), (379, 1), (2089, 1), (7615115047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (241, 1), (379, 1), (2089, 1), (7615115047, 1)] : List FactorBlock).map factorBlockValue).prod) = 6695509519676630186497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_241
      · exact prime_ninetyCJ_379
      · exact prime_ninetyCJ_2089
      · exact prime_ninetyCJ_7615115047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6695509519676630186497) ^ 3347754759838315093248 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6695509519676630186497) ^ 2231836506558876728832 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6695509519676630186497) ^ 27782197177081453056 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6695509519676630186497) ^ 17666252030809050624 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6695509519676630186497) ^ 3205126625024715264 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6695509519676630186497) ^ 879239443968 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_8564269684882519486883 : Nat.Prime 8564269684882519486883 := by
  apply lucas_primality 8564269684882519486883 (2 : ZMod 8564269684882519486883)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4282134842441259743441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4282134842441259743441, 1)] : List FactorBlock).map factorBlockValue).prod) = 8564269684882519486883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_4282134842441259743441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 8564269684882519486883) ^ 4282134842441259743441 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8564269684882519486883) ^ 2 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_13677317677156543722769 : Nat.Prime 13677317677156543722769 := by
  apply lucas_primality 13677317677156543722769 (13 : ZMod 13677317677156543722769)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (284944118274094660891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (284944118274094660891, 1)] : List FactorBlock).map factorBlockValue).prod) = 13677317677156543722769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_284944118274094660891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 13677317677156543722769) ^ 6838658838578271861384 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 13677317677156543722769) ^ 4559105892385514574256 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (13 : ZMod 13677317677156543722769) ^ 48 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_14605285729027281626081 : Nat.Prime 14605285729027281626081 := by
  apply lucas_primality 14605285729027281626081 (3 : ZMod 14605285729027281626081)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (509, 1), (179337987831867407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (509, 1), (179337987831867407, 1)] : List FactorBlock).map factorBlockValue).prod) = 14605285729027281626081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_509
      · exact prime_ninetyCJ_179337987831867407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14605285729027281626081) ^ 7302642864513640813040 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 14605285729027281626081) ^ 2921057145805456325216 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 14605285729027281626081) ^ 28694078053098785120 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 14605285729027281626081) ^ 81440 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_20549131536366922570171 : Nat.Prime 20549131536366922570171 := by
  apply lucas_primality 20549131536366922570171 (10 : ZMod 20549131536366922570171)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (684971051212230752339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (684971051212230752339, 1)] : List FactorBlock).map factorBlockValue).prod) = 20549131536366922570171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_684971051212230752339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 20549131536366922570171) ^ 10274565768183461285085 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 20549131536366922570171) ^ 6849710512122307523390 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 20549131536366922570171) ^ 4109826307273384514034 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (10 : ZMod 20549131536366922570171) ^ 30 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_37793517224971626124003 : Nat.Prime 37793517224971626124003 := by
  apply lucas_primality 37793517224971626124003 (2 : ZMod 37793517224971626124003)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (283, 1), (1103, 1), (80251, 1), (9313006279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (283, 1), (1103, 1), (80251, 1), (9313006279, 1)] : List FactorBlock).map factorBlockValue).prod) = 37793517224971626124003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_283
      · exact prime_ninetyCJ_1103
      · exact prime_ninetyCJ_80251
      · exact prime_ninetyCJ_9313006279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37793517224971626124003) ^ 18896758612485813062001 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37793517224971626124003) ^ 12597839074990542041334 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37793517224971626124003) ^ 133545997261383837894 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37793517224971626124003) ^ 34264294854915345534 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37793517224971626124003) ^ 470941386711338502 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37793517224971626124003) ^ 4058143642638 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_45950195829077781620453 : Nat.Prime 45950195829077781620453 := by
  apply lucas_primality 45950195829077781620453 (2 : ZMod 45950195829077781620453)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (66456831821, 1), (172857306653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (66456831821, 1), (172857306653, 1)] : List FactorBlock).map factorBlockValue).prod) = 45950195829077781620453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_66456831821
      · exact prime_ninetyCJ_172857306653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45950195829077781620453) ^ 22975097914538890810226 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 45950195829077781620453) ^ 691429226612 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 45950195829077781620453) ^ 265827327284 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_105667097233150027782269 : Nat.Prime 105667097233150027782269 := by
  apply lucas_primality 105667097233150027782269 (2 : ZMod 105667097233150027782269)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (90659137, 1), (291385680279391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (90659137, 1), (291385680279391, 1)] : List FactorBlock).map factorBlockValue).prod) = 105667097233150027782269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_90659137
      · exact prime_ninetyCJ_291385680279391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 105667097233150027782269) ^ 52833548616575013891134 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 105667097233150027782269) ^ 1165542721117564 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 105667097233150027782269) ^ 362636548 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_124556511951534850597559 : Nat.Prime 124556511951534850597559 := by
  apply lucas_primality 124556511951534850597559 (7 : ZMod 124556511951534850597559)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (1518981853067498178019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (1518981853067498178019, 1)] : List FactorBlock).map factorBlockValue).prod) = 124556511951534850597559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_41
      · exact prime_ninetyCJ_1518981853067498178019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 124556511951534850597559) ^ 62278255975767425298779 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 124556511951534850597559) ^ 3037963706134996356038 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 124556511951534850597559) ^ 82 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_181617115689920999668907 : Nat.Prime 181617115689920999668907 := by
  apply lucas_primality 181617115689920999668907 (2 : ZMod 181617115689920999668907)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3571, 1), (9413, 1), (9649, 1), (279979712539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3571, 1), (9413, 1), (9649, 1), (279979712539, 1)] : List FactorBlock).map factorBlockValue).prod) = 181617115689920999668907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3571
      · exact prime_ninetyCJ_9413
      · exact prime_ninetyCJ_9649
      · exact prime_ninetyCJ_279979712539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 181617115689920999668907) ^ 90808557844960499834453 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 181617115689920999668907) ^ 50858895460633155886 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 181617115689920999668907) ^ 19294286166994688162 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 181617115689920999668907) ^ 18822377001753653194 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 181617115689920999668907) ^ 648679556254 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_187474266550945645221917 : Nat.Prime 187474266550945645221917 := by
  apply lucas_primality 187474266550945645221917 (2 : ZMod 187474266550945645221917)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (6695509519676630186497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (6695509519676630186497, 1)] : List FactorBlock).map factorBlockValue).prod) = 187474266550945645221917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_6695509519676630186497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 187474266550945645221917) ^ 93737133275472822610958 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 187474266550945645221917) ^ 26782038078706520745988 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 187474266550945645221917) ^ 28 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_192873414508561182566683 : Nat.Prime 192873414508561182566683 := by
  apply lucas_primality 192873414508561182566683 (2 : ZMod 192873414508561182566683)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (168599, 1), (1038449, 1), (1154738983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (168599, 1), (1038449, 1), (1154738983, 1)] : List FactorBlock).map factorBlockValue).prod) = 192873414508561182566683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_53
      · exact prime_ninetyCJ_168599
      · exact prime_ninetyCJ_1038449
      · exact prime_ninetyCJ_1154738983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 192873414508561182566683) ^ 96436707254280591283341 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 192873414508561182566683) ^ 64291138169520394188894 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 192873414508561182566683) ^ 3639121028463418538994 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 192873414508561182566683) ^ 1143977215218128118 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 192873414508561182566683) ^ 185732197256255418 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 192873414508561182566683) ^ 167027715655254 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_203433809210106332357033 : Nat.Prime 203433809210106332357033 := by
  apply lucas_primality 203433809210106332357033 (3 : ZMod 203433809210106332357033)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (1231, 1), (1651477, 1), (962186389259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (1231, 1), (1651477, 1), (962186389259, 1)] : List FactorBlock).map factorBlockValue).prod) = 203433809210106332357033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_1231
      · exact prime_ninetyCJ_1651477
      · exact prime_ninetyCJ_962186389259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 203433809210106332357033) ^ 101716904605053166178516 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 203433809210106332357033) ^ 15648754554623564027464 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 203433809210106332357033) ^ 165258983923725696472 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 203433809210106332357033) ^ 123182950298494216 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 203433809210106332357033) ^ 211428691448 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_211133748512801516129141 : Nat.Prime 211133748512801516129141 := by
  apply lucas_primality 211133748512801516129141 (2 : ZMod 211133748512801516129141)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (67, 1), (75707, 1), (277213, 1), (153217069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (67, 1), (75707, 1), (277213, 1), (153217069, 1)] : List FactorBlock).map factorBlockValue).prod) = 211133748512801516129141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_67
      · exact prime_ninetyCJ_75707
      · exact prime_ninetyCJ_277213
      · exact prime_ninetyCJ_153217069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 211133748512801516129141) ^ 105566874256400758064570 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 211133748512801516129141) ^ 42226749702560303225828 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 211133748512801516129141) ^ 30161964073257359447020 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 211133748512801516129141) ^ 3151249977803007703420 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 211133748512801516129141) ^ 2788827301475445020 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 211133748512801516129141) ^ 761630040845131780 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 211133748512801516129141) ^ 1378004095045060 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_278221176353280522314437 : Nat.Prime 278221176353280522314437 := by
  apply lucas_primality 278221176353280522314437 (5 : ZMod 278221176353280522314437)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (227, 1), (844107402681037009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (227, 1), (844107402681037009, 1)] : List FactorBlock).map factorBlockValue).prod) = 278221176353280522314437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_227
      · exact prime_ninetyCJ_844107402681037009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 278221176353280522314437) ^ 139110588176640261157218 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 278221176353280522314437) ^ 92740392117760174104812 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 278221176353280522314437) ^ 25292834213934592937676 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 278221176353280522314437) ^ 1225643948692865737068 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 278221176353280522314437) ^ 329604 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_596294703989273915759869 : Nat.Prime 596294703989273915759869 := by
  apply lucas_primality 596294703989273915759869 (2 : ZMod 596294703989273915759869)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (149, 1), (834107, 1), (8159726304227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (149, 1), (834107, 1), (8159726304227, 1)] : List FactorBlock).map factorBlockValue).prod) = 596294703989273915759869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_149
      · exact prime_ninetyCJ_834107
      · exact prime_ninetyCJ_8159726304227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 596294703989273915759869) ^ 298147351994636957879934 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 596294703989273915759869) ^ 198764901329757971919956 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 596294703989273915759869) ^ 85184957712753416537124 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 596294703989273915759869) ^ 4001977879122643729932 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 596294703989273915759869) ^ 714889940965935924 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 596294703989273915759869) ^ 73077782484 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_736314136623006290791733 : Nat.Prime 736314136623006290791733 := by
  apply lucas_primality 736314136623006290791733 (2 : ZMod 736314136623006290791733)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (503, 1), (571, 1), (537403, 1), (838367, 1), (1422541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (503, 1), (571, 1), (537403, 1), (838367, 1), (1422541, 1)] : List FactorBlock).map factorBlockValue).prod) = 736314136623006290791733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_503
      · exact prime_ninetyCJ_571
      · exact prime_ninetyCJ_537403
      · exact prime_ninetyCJ_838367
      · exact prime_ninetyCJ_1422541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 736314136623006290791733) ^ 368157068311503145395866 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 736314136623006290791733) ^ 1463845202033809723244 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 736314136623006290791733) ^ 1289516876747821875292 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 736314136623006290791733) ^ 1370134027206782044 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 736314136623006290791733) ^ 878271850660875596 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 736314136623006290791733) ^ 517604861035995652 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_768315543138522753094249 : Nat.Prime 768315543138522753094249 := by
  apply lucas_primality 768315543138522753094249 (43 : ZMod 768315543138522753094249)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (19, 1), (153172955171156848703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (19, 1), (153172955171156848703, 1)] : List FactorBlock).map factorBlockValue).prod) = 768315543138522753094249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_19
      · exact prime_ninetyCJ_153172955171156848703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (43 : ZMod 768315543138522753094249) ^ 384157771569261376547124 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (43 : ZMod 768315543138522753094249) ^ 256105181046174251031416 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (43 : ZMod 768315543138522753094249) ^ 69846867558047523008568 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (43 : ZMod 768315543138522753094249) ^ 40437660165185408057592 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (43 : ZMod 768315543138522753094249) ^ 5016 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_2216750407692792001583803 : Nat.Prime 2216750407692792001583803 := by
  apply lucas_primality 2216750407692792001583803 (2 : ZMod 2216750407692792001583803)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (151, 1), (1699, 1), (6157199, 1), (233890202717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (151, 1), (1699, 1), (6157199, 1), (233890202717, 1)] : List FactorBlock).map factorBlockValue).prod) = 2216750407692792001583803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_151
      · exact prime_ninetyCJ_1699
      · exact prime_ninetyCJ_6157199
      · exact prime_ninetyCJ_233890202717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2216750407692792001583803) ^ 1108375203846396000791901 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2216750407692792001583803) ^ 738916802564264000527934 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2216750407692792001583803) ^ 14680466276111205308502 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2216750407692792001583803) ^ 1304738321184692172798 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2216750407692792001583803) ^ 360025785701061798 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2216750407692792001583803) ^ 9477739477506 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_4166987255502409088546017 : Nat.Prime 4166987255502409088546017 := by
  apply lucas_primality 4166987255502409088546017 (7 : ZMod 4166987255502409088546017)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (3338932095755135487617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (3338932095755135487617, 1)] : List FactorBlock).map factorBlockValue).prod) = 4166987255502409088546017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_3338932095755135487617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4166987255502409088546017) ^ 2083493627751204544273008 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4166987255502409088546017) ^ 1388995751834136362848672 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4166987255502409088546017) ^ 320537481192493006811232 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4166987255502409088546017) ^ 1248 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_11935391987577567703423729 : Nat.Prime 11935391987577567703423729 := by
  apply lucas_primality 11935391987577567703423729 (14 : ZMod 11935391987577567703423729)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (971, 1), (256080329290627525391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (971, 1), (256080329290627525391, 1)] : List FactorBlock).map factorBlockValue).prod) = 11935391987577567703423729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_971
      · exact prime_ninetyCJ_256080329290627525391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 11935391987577567703423729) ^ 5967695993788783851711864 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 11935391987577567703423729) ^ 3978463995859189234474576 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 11935391987577567703423729) ^ 12291855805950121218768 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (14 : ZMod 11935391987577567703423729) ^ 46608 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_18687042425229015819463039 : Nat.Prime 18687042425229015819463039 := by
  apply lucas_primality 18687042425229015819463039 (3 : ZMod 18687042425229015819463039)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (41, 1), (2267483, 1), (11415697, 1), (31555571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (41, 1), (2267483, 1), (11415697, 1), (31555571, 1)] : List FactorBlock).map factorBlockValue).prod) = 18687042425229015819463039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_31
      · exact prime_ninetyCJ_41
      · exact prime_ninetyCJ_2267483
      · exact prime_ninetyCJ_11415697
      · exact prime_ninetyCJ_31555571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18687042425229015819463039) ^ 9343521212614507909731519 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18687042425229015819463039) ^ 6229014141743005273154346 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18687042425229015819463039) ^ 602807820168677929660098 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18687042425229015819463039) ^ 455781522566561361450318 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18687042425229015819463039) ^ 8241315337415546586 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18687042425229015819463039) ^ 1636960268411908254 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18687042425229015819463039) ^ 592194716591533578 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_28480733289414886529984621 : Nat.Prime 28480733289414886529984621 := by
  apply lucas_primality 28480733289414886529984621 (3 : ZMod 28480733289414886529984621)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (203433809210106332357033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (203433809210106332357033, 1)] : List FactorBlock).map factorBlockValue).prod) = 28480733289414886529984621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_203433809210106332357033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28480733289414886529984621) ^ 14240366644707443264992310 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 28480733289414886529984621) ^ 5696146657882977305996924 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 28480733289414886529984621) ^ 4068676184202126647140660 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 28480733289414886529984621) ^ 140 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_34932376746307950123447979 : Nat.Prime 34932376746307950123447979 := by
  apply lucas_primality 34932376746307950123447979 (3 : ZMod 34932376746307950123447979)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (9341, 1), (4996608863, 1), (7337687933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (9341, 1), (4996608863, 1), (7337687933, 1)] : List FactorBlock).map factorBlockValue).prod) = 34932376746307950123447979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_17
      · exact prime_ninetyCJ_9341
      · exact prime_ninetyCJ_4996608863
      · exact prime_ninetyCJ_7337687933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34932376746307950123447979) ^ 17466188373153975061723989 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34932376746307950123447979) ^ 11644125582102650041149326 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34932376746307950123447979) ^ 2054845690959291183732234 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34932376746307950123447979) ^ 3739682769115506918258 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34932376746307950123447979) ^ 6991216984179606 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34932376746307950123447979) ^ 4760678985706866 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_56387927699657666177012477 : Nat.Prime 56387927699657666177012477 := by
  apply lucas_primality 56387927699657666177012477 (2 : ZMod 56387927699657666177012477)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (373, 1), (37793517224971626124003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (373, 1), (37793517224971626124003, 1)] : List FactorBlock).map factorBlockValue).prod) = 56387927699657666177012477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_373
      · exact prime_ninetyCJ_37793517224971626124003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 56387927699657666177012477) ^ 28193963849828833088506238 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 56387927699657666177012477) ^ 151174068899886504496012 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 56387927699657666177012477) ^ 1492 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_115280627919018435618659311 : Nat.Prime 115280627919018435618659311 := by
  apply lucas_primality 115280627919018435618659311 (6 : ZMod 115280627919018435618659311)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (20549131536366922570171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (20549131536366922570171, 1)] : List FactorBlock).map factorBlockValue).prod) = 115280627919018435618659311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_11
      · exact prime_ninetyCJ_17
      · exact prime_ninetyCJ_20549131536366922570171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 115280627919018435618659311) ^ 57640313959509217809329655 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 115280627919018435618659311) ^ 38426875973006145206219770 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 115280627919018435618659311) ^ 23056125583803687123731862 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 115280627919018435618659311) ^ 10480057083547130510787210 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 115280627919018435618659311) ^ 6781213407001084448156430 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 115280627919018435618659311) ^ 5610 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_587867511432342630254268199 : Nat.Prime 587867511432342630254268199 := by
  apply lucas_primality 587867511432342630254268199 (3 : ZMod 587867511432342630254268199)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1447, 1), (983445889, 1), (68850834552551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1447, 1), (983445889, 1), (68850834552551, 1)] : List FactorBlock).map factorBlockValue).prod) = 587867511432342630254268199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_1447
      · exact prime_ninetyCJ_983445889
      · exact prime_ninetyCJ_68850834552551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 587867511432342630254268199) ^ 293933755716171315127134099 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 587867511432342630254268199) ^ 195955837144114210084756066 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 587867511432342630254268199) ^ 406266421169552612477034 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 587867511432342630254268199) ^ 597762945585247782 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 587867511432342630254268199) ^ 8538277208298 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_633357259340797714738229429 : Nat.Prime 633357259340797714738229429 := by
  apply lucas_primality 633357259340797714738229429 (2 : ZMod 633357259340797714738229429)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (80537, 1), (6381581, 1), (308081079383881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (80537, 1), (6381581, 1), (308081079383881, 1)] : List FactorBlock).map factorBlockValue).prod) = 633357259340797714738229429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_80537
      · exact prime_ninetyCJ_6381581
      · exact prime_ninetyCJ_308081079383881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 633357259340797714738229429) ^ 316678629670398857369114714 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 633357259340797714738229429) ^ 7864177450622666783444 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 633357259340797714738229429) ^ 99247703561358496388 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 633357259340797714738229429) ^ 2055813555988 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_3800143556044786288429376573 : Nat.Prime 3800143556044786288429376573 := by
  apply lucas_primality 3800143556044786288429376573 (2 : ZMod 3800143556044786288429376573)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (192651929, 1), (704479905393966881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (192651929, 1), (704479905393966881, 1)] : List FactorBlock).map factorBlockValue).prod) = 3800143556044786288429376573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_7
      · exact prime_ninetyCJ_192651929
      · exact prime_ninetyCJ_704479905393966881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3800143556044786288429376573) ^ 1900071778022393144214688286 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3800143556044786288429376573) ^ 542877650863540898347053796 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3800143556044786288429376573) ^ 19725437351031072668 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3800143556044786288429376573) ^ 5394254012 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_8867001630771168006335212001 : Nat.Prime 8867001630771168006335212001 := by
  apply lucas_primality 8867001630771168006335212001 (6 : ZMod 8867001630771168006335212001)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 3), (2216750407692792001583803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 3), (2216750407692792001583803, 1)] : List FactorBlock).map factorBlockValue).prod) = 8867001630771168006335212001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_2216750407692792001583803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 8867001630771168006335212001) ^ 4433500815385584003167606000 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 8867001630771168006335212001) ^ 1773400326154233601267042400 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 8867001630771168006335212001) ^ 4000 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_11822668841028224008446949337 : Nat.Prime 11822668841028224008446949337 := by
  apply lucas_primality 11822668841028224008446949337 (3 : ZMod 11822668841028224008446949337)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (55207, 1), (5269992269, 1), (5079505232449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (55207, 1), (5269992269, 1), (5079505232449, 1)] : List FactorBlock).map factorBlockValue).prod) = 11822668841028224008446949337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_55207
      · exact prime_ninetyCJ_5269992269
      · exact prime_ninetyCJ_5079505232449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11822668841028224008446949337) ^ 5911334420514112004223474668 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11822668841028224008446949337) ^ 214151626442810223494248 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11822668841028224008446949337) ^ 2243393962942495544 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11822668841028224008446949337) ^ 2327523705557464 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_53202009784627008038011272013 : Nat.Prime 53202009784627008038011272013 := by
  apply lucas_primality 53202009784627008038011272013 (5 : ZMod 53202009784627008038011272013)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (55207, 1), (5269992269, 1), (5079505232449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (55207, 1), (5269992269, 1), (5079505232449, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627008038011272013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_55207
      · exact prime_ninetyCJ_5269992269
      · exact prime_ninetyCJ_5079505232449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 53202009784627008038011272013) ^ 26601004892313504019005636006 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 53202009784627008038011272013) ^ 17734003261542336012670424004 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 53202009784627008038011272013) ^ 963682318992646005724116 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 53202009784627008038011272013) ^ 10095272833241229948 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 53202009784627008038011272013) ^ 10473856675008588 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_53202009784627008038011272047 : Nat.Prime 53202009784627008038011272047 := by
  apply lucas_primality 53202009784627008038011272047 (5 : ZMod 53202009784627008038011272047)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (43, 1), (795323, 1), (59833263752006014939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (43, 1), (795323, 1), (59833263752006014939, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627008038011272047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_43
      · exact prime_ninetyCJ_795323
      · exact prime_ninetyCJ_59833263752006014939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 53202009784627008038011272047) ^ 26601004892313504019005636023 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 53202009784627008038011272047) ^ 4092462291125154464462405542 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 53202009784627008038011272047) ^ 1237256041502953675302587722 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 53202009784627008038011272047) ^ 66893588874742724701802 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (5 : ZMod 53202009784627008038011272047) ^ 889171114 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_106404019569254016076022544041 : Nat.Prime 106404019569254016076022544041 := by
  apply lucas_primality 106404019569254016076022544041 (6 : ZMod 106404019569254016076022544041)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (263, 1), (1607, 1), (484153488554725460197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (263, 1), (1607, 1), (484153488554725460197, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_5
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_263
      · exact prime_ninetyCJ_1607
      · exact prime_ninetyCJ_484153488554725460197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 106404019569254016076022544041) ^ 53202009784627008038011272020 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 106404019569254016076022544041) ^ 21280803913850803215204508808 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 106404019569254016076022544041) ^ 8184924582250308928924811080 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 106404019569254016076022544041) ^ 404578021175870783559021080 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 106404019569254016076022544041) ^ 66212831094744253936541720 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (6 : ZMod 106404019569254016076022544041) ^ 219773320 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem prime_ninetyCJ_106404019569254016076022544067 : Nat.Prime 106404019569254016076022544067 := by
  apply lucas_primality 106404019569254016076022544067 (2 : ZMod 106404019569254016076022544067)
  · rw [← ninetyCJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (73, 1), (18687042425229015819463039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (73, 1), (18687042425229015819463039, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyCJ_2
      · exact prime_ninetyCJ_3
      · exact prime_ninetyCJ_13
      · exact prime_ninetyCJ_73
      · exact prime_ninetyCJ_18687042425229015819463039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 106404019569254016076022544067) ^ 53202009784627008038011272033 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 106404019569254016076022544067) ^ 35468006523084672025340848022 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 106404019569254016076022544067) ^ 8184924582250308928924811082 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 106404019569254016076022544067) ^ 1457589309167863233918117042 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide
    · change (2 : ZMod 106404019569254016076022544067) ^ 5694 ≠ 1
      rw [← ninetyCJFastPow_eq_pow]
      decide

private theorem phi_ninetyCJ_106404019569254016076022544000 : Nat.totient 106404019569254016076022544000 = 28374405218467737620272665600 := by
  rw [← show ((([(2, 7), (3, 1), (5, 3), (2216750407692792001583803, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_5, prime_ninetyCJ_2216750407692792001583803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544001 : Nat.totient 106404019569254016076022544001 = 98219077196805905384458521360 := by
  rw [← show ((([(13, 1), (5520967, 1), (1482516483480214413331, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_13, prime_ninetyCJ_5520967, prime_ninetyCJ_1482516483480214413331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544002 : Nat.totient 106404019569254016076022544002 = 45601682746640364617738170848 := by
  rw [← show ((([(2, 1), (7, 1), (1142159, 1), (6654316178473901249177, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_7, prime_ninetyCJ_1142159, prime_ninetyCJ_6654316178473901249177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544003 : Nat.totient 106404019569254016076022544003 = 70936012894205136990667630464 := by
  rw [← show ((([(3, 1), (466794217, 1), (75982103529540238553, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_466794217, prime_ninetyCJ_75982103529540238553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544004 : Nat.totient 106404019569254016076022544004 = 53011832079464706274340433920 := by
  rw [← show ((([(2, 2), (281, 1), (86399, 1), (227393, 1), (4818434013754103, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_281, prime_ninetyCJ_86399, prime_ninetyCJ_227393, prime_ninetyCJ_4818434013754103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544005 : Nat.totient 106404019569254016076022544005 = 81081506403480571946571620160 := by
  rw [← show ((([(5, 1), (23, 1), (239, 1), (3826723, 1), (1011661601846270371, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_5, prime_ninetyCJ_23, prime_ninetyCJ_239, prime_ninetyCJ_3826723, prime_ninetyCJ_1011661601846270371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544006 : Nat.totient 106404019569254016076022544006 = 34616541053579949101470996800 := by
  rw [← show ((([(2, 1), (3, 2), (43, 1), (1301, 1), (105667097233150027782269, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_43, prime_ninetyCJ_1301, prime_ninetyCJ_105667097233150027782269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544007 : Nat.totient 106404019569254016076022544007 = 104717284634375408485129812480 := by
  rw [← show ((([(67, 1), (1063, 1), (10102733, 1), (111557489, 1), (1325599591, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_67, prime_ninetyCJ_1063, prime_ninetyCJ_10102733, prime_ninetyCJ_111557489, prime_ninetyCJ_1325599591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544008 : Nat.totient 106404019569254016076022544008 = 53200279130340005123562493440 := by
  rw [← show ((([(2, 3), (34127, 1), (309823, 1), (1257929436488310881, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_34127, prime_ninetyCJ_309823, prime_ninetyCJ_1257929436488310881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544009 : Nat.totient 106404019569254016076022544009 = 60394079535673562547657145344 := by
  rw [← show ((([(3, 1), (7, 1), (149, 1), (407369, 1), (83476550475812065609, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_7, prime_ninetyCJ_149, prime_ninetyCJ_407369, prime_ninetyCJ_83476550475812065609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544010 : Nat.totient 106404019569254016076022544010 = 38661638130730464935702559360 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (1259, 1), (768315543138522753094249, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_5, prime_ninetyCJ_11, prime_ninetyCJ_1259, prime_ninetyCJ_768315543138522753094249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544011 : Nat.totient 106404019569254016076022544011 = 100803803657319257012702553600 := by
  rw [← show ((([(19, 1), (23286269, 1), (4019502061, 1), (59831827441, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_19, prime_ninetyCJ_23286269, prime_ninetyCJ_4019502061, prime_ninetyCJ_59831827441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544012 : Nat.totient 106404019569254016076022544012 = 35468006523084672025340848000 := by
  rw [← show ((([(2, 2), (3, 1), (8867001630771168006335212001, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_8867001630771168006335212001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544013 : Nat.totient 106404019569254016076022544013 = 106400231169117099069463320240 := by
  rw [← show ((([(28087, 1), (3855717031, 1), (982533860992429, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_28087, prime_ninetyCJ_3855717031, prime_ninetyCJ_982533860992429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544014 : Nat.totient 106404019569254016076022544014 = 44729758627857475740612794880 := by
  rw [← show ((([(2, 1), (13, 3), (17, 1), (31, 1), (45950195829077781620453, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_13, prime_ninetyCJ_17, prime_ninetyCJ_31, prime_ninetyCJ_45950195829077781620453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544015 : Nat.totient 106404019569254016076022544015 = 56744416325423035544073822720 := by
  rw [← show ((([(3, 3), (5, 1), (16253, 1), (65599, 1), (1513661, 1), (488387893967, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_5, prime_ninetyCJ_16253, prime_ninetyCJ_65599, prime_ninetyCJ_1513661, prime_ninetyCJ_488387893967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544016 : Nat.totient 106404019569254016076022544016 = 45601722435832187184048599040 := by
  rw [← show ((([(2, 4), (7, 2), (192651929, 1), (704479905393966881, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_7, prime_ninetyCJ_192651929, prime_ninetyCJ_704479905393966881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544017 : Nat.totient 106404019569254016076022544017 = 106403895012742064541171092196 := by
  rw [← show ((([(854263, 1), (124556511951534850597559, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_854263, prime_ninetyCJ_124556511951534850597559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544018 : Nat.totient 106404019569254016076022544018 = 35233109521380159080955120000 := by
  rw [← show ((([(2, 1), (3, 1), (151, 1), (3692701, 1), (31804289112194472953, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_151, prime_ninetyCJ_3692701, prime_ninetyCJ_31804289112194472953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544019 : Nat.totient 106404019569254016076022544019 = 105816152057821673445768275640 := by
  rw [← show ((([(181, 1), (587867511432342630254268199, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_181, prime_ninetyCJ_587867511432342630254268199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544020 : Nat.totient 106404019569254016076022544020 = 41758558615061771104305540480 := by
  rw [← show ((([(2, 2), (5, 1), (53, 1), (5004875131, 1), (20056674324455207, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_5, prime_ninetyCJ_53, prime_ninetyCJ_5004875131, prime_ninetyCJ_20056674324455207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544021 : Nat.totient 106404019569254016076022544021 = 62245882931208199535172591360 := by
  rw [← show ((([(3, 1), (11, 1), (29, 1), (3547, 1), (419687, 1), (74689472324268877, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_11, prime_ninetyCJ_29, prime_ninetyCJ_3547, prime_ninetyCJ_419687, prime_ninetyCJ_74689472324268877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544022 : Nat.totient 106404019569254016076022544022 = 52845246255380558475153682080 := by
  rw [← show ((([(2, 1), (163, 1), (1741, 1), (187474266550945645221917, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_163, prime_ninetyCJ_1741, prime_ninetyCJ_187474266550945645221917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544023 : Nat.totient 106404019569254016076022544023 = 91203427579596384532969213920 := by
  rw [← show ((([(7, 1), (5988271, 1), (35975837, 1), (70558224094507, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_7, prime_ninetyCJ_5988271, prime_ninetyCJ_35975837, prime_ninetyCJ_70558224094507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544024 : Nat.totient 106404019569254016076022544024 = 35467364061468301169332924416 := by
  rw [← show ((([(2, 3), (3, 2), (55207, 1), (5269992269, 1), (5079505232449, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_55207, prime_ninetyCJ_5269992269, prime_ninetyCJ_5079505232449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544025 : Nat.totient 106404019569254016076022544025 = 82821262980235094905781237760 := by
  rw [← show ((([(5, 2), (37, 1), (62497, 1), (1840590308451631902349, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_5, prime_ninetyCJ_37, prime_ninetyCJ_62497, prime_ninetyCJ_1840590308451631902349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544026 : Nat.totient 106404019569254016076022544026 = 53202009784627008038011272012 := by
  rw [← show ((([(2, 1), (53202009784627008038011272013, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_53202009784627008038011272013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544027 : Nat.totient 106404019569254016076022544027 = 64979532651776821268424000000 := by
  rw [← show ((([(3, 1), (13, 1), (131, 1), (3620501, 1), (19479701, 1), (295305253703, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_13, prime_ninetyCJ_131, prime_ninetyCJ_3620501, prime_ninetyCJ_19479701, prime_ninetyCJ_295305253703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544028 : Nat.totient 106404019569254016076022544028 = 50876637192666289432507024704 := by
  rw [← show ((([(2, 2), (23, 1), (4157, 1), (278221176353280522314437, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_23, prime_ninetyCJ_4157, prime_ninetyCJ_278221176353280522314437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544029 : Nat.totient 106404019569254016076022544029 = 105408041319534458660087985280 := by
  rw [← show ((([(107, 1), (68087, 1), (14605285729027281626081, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_107, prime_ninetyCJ_68087, prime_ninetyCJ_14605285729027281626081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544030 : Nat.totient 106404019569254016076022544030 = 22422419786606740436252344320 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (41, 1), (419, 1), (7927, 1), (84216413, 1), (2325314293, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_5, prime_ninetyCJ_7, prime_ninetyCJ_19, prime_ninetyCJ_41, prime_ninetyCJ_419, prime_ninetyCJ_7927, prime_ninetyCJ_84216413, prime_ninetyCJ_2325314293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544031 : Nat.totient 106404019569254016076022544031 = 97728991839082516005216921600 := by
  rw [← show ((([(17, 1), (59, 2), (137, 1), (3202753819, 1), (4097896307101, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_17, prime_ninetyCJ_59, prime_ninetyCJ_137, prime_ninetyCJ_3202753819, prime_ninetyCJ_4097896307101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544032 : Nat.totient 106404019569254016076022544032 = 48365189447881088878244544000 := by
  rw [← show ((([(2, 5), (11, 1), (176521, 1), (1712454305740181313671, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_11, prime_ninetyCJ_176521, prime_ninetyCJ_1712454305740181313671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544033 : Nat.totient 106404019569254016076022544033 = 70936013046169344050681696016 := by
  rw [← show ((([(3, 2), (11822668841028224008446949337, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_11822668841028224008446949337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544034 : Nat.totient 106404019569254016076022544034 = 53167077407880700087887822516 := by
  rw [← show ((([(2, 1), (1523, 1), (34932376746307950123447979, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_1523, prime_ninetyCJ_34932376746307950123447979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544035 : Nat.totient 106404019569254016076022544035 = 85075474087452902590004333184 := by
  rw [← show ((([(5, 1), (1783, 1), (11935391987577567703423729, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_5, prime_ninetyCJ_1783, prime_ninetyCJ_11935391987577567703423729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544036 : Nat.totient 106404019569254016076022544036 = 34885802759106434514190963200 := by
  rw [← show ((([(2, 2), (3, 1), (61, 1), (45841, 1), (3170975381681431293103, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_61, prime_ninetyCJ_45841, prime_ninetyCJ_3170975381681431293103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544037 : Nat.totient 106404019569254016076022544037 = 91024263723490951673261233728 := by
  rw [← show ((([(7, 1), (509, 1), (1178568135637, 1), (25338885959027, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_7, prime_ninetyCJ_509, prime_ninetyCJ_1178568135637, prime_ninetyCJ_25338885959027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544038 : Nat.totient 106404019569254016076022544038 = 53202009558919693875168534496 := by
  rw [← show ((([(2, 1), (235712387, 1), (225707314162607025137, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_235712387, prime_ninetyCJ_225707314162607025137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544039 : Nat.totient 106404019569254016076022544039 = 69233198050200202031583679200 := by
  rw [← show ((([(3, 1), (47, 1), (359, 1), (465011, 1), (4520445595122178471, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_47, prime_ninetyCJ_359, prime_ninetyCJ_465011, prime_ninetyCJ_4520445595122178471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544040 : Nat.totient 106404019569254016076022544040 = 39113900483740596736817531904 := by
  rw [← show ((([(2, 3), (5, 1), (13, 1), (263, 1), (1607, 1), (484153488554725460197, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_5, prime_ninetyCJ_13, prime_ninetyCJ_263, prime_ninetyCJ_1607, prime_ninetyCJ_484153488554725460197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544041 : Nat.totient 106404019569254016076022544041 = 106404019569254016076022544040 := by
  rw [← show ((([(106404019569254016076022544041, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_106404019569254016076022544041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544042 : Nat.totient 106404019569254016076022544042 = 34994381839831458001181952000 := by
  rw [← show ((([(2, 1), (3, 3), (79, 1), (1451, 1), (71419, 1), (917041, 1), (262462494953, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_79, prime_ninetyCJ_1451, prime_ninetyCJ_71419, prime_ninetyCJ_917041, prime_ninetyCJ_262462494953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544043 : Nat.totient 106404019569254016076022544043 = 96730284426533356025681164960 := by
  rw [← show ((([(11, 1), (150797, 1), (97699907, 1), (656566163363447, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_11, prime_ninetyCJ_150797, prime_ninetyCJ_97699907, prime_ninetyCJ_656566163363447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544044 : Nat.totient 106404019569254016076022544044 = 45601722672537435461152518864 := by
  rw [← show ((([(2, 2), (7, 1), (3800143556044786288429376573, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_7, prime_ninetyCJ_3800143556044786288429376573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544045 : Nat.totient 106404019569254016076022544045 = 54918113219583105669003731520 := by
  rw [← show ((([(3, 1), (5, 1), (31, 1), (607307, 1), (376787767201810850359, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_5, prime_ninetyCJ_31, prime_ninetyCJ_607307, prime_ninetyCJ_376787767201810850359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544046 : Nat.totient 106404019569254016076022544046 = 53196480807289220942289036288 := by
  rw [← show ((([(2, 1), (9629, 1), (14028673, 1), (393849464959254019, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_9629, prime_ninetyCJ_14028673, prime_ninetyCJ_393849464959254019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544047 : Nat.totient 106404019569254016076022544047 = 106402564388095466199199340128 := by
  rw [← show ((([(85703, 1), (498053, 1), (2492794337607102533, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_85703, prime_ninetyCJ_498053, prime_ninetyCJ_2492794337607102533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544048 : Nat.totient 106404019569254016076022544048 = 33381652959891582381900464128 := by
  rw [← show ((([(2, 4), (3, 1), (17, 1), (140079089, 1), (930881859214963577, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_17, prime_ninetyCJ_140079089, prime_ninetyCJ_930881859214963577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544049 : Nat.totient 106404019569254016076022544049 = 98459533407712759724972065536 := by
  rw [← show ((([(19, 1), (43, 1), (316056205609, 1), (412070624596633, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_19, prime_ninetyCJ_43, prime_ninetyCJ_316056205609, prime_ninetyCJ_412070624596633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544050 : Nat.totient 106404019569254016076022544050 = 41093966178460800318144829440 := by
  rw [← show ((([(2, 1), (5, 2), (29, 1), (7305104863393, 1), (10045315410773, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_5, prime_ninetyCJ_29, prime_ninetyCJ_7305104863393, prime_ninetyCJ_10045315410773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544051 : Nat.totient 106404019569254016076022544051 = 58056864621727413730637764800 := by
  rw [← show ((([(3, 2), (7, 1), (23, 1), (571, 1), (108343257259, 1), (1187002551491, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_7, prime_ninetyCJ_23, prime_ninetyCJ_571, prime_ninetyCJ_108343257259, prime_ninetyCJ_1187002551491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544052 : Nat.totient 106404019569254016076022544052 = 53202006591483810546647969760 := by
  rw [← show ((([(2, 2), (27185311, 1), (43039247, 1), (22735215384989, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_27185311, prime_ninetyCJ_43039247, prime_ninetyCJ_22735215384989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544053 : Nat.totient 106404019569254016076022544053 = 96835727451975485919673820400 := by
  rw [← show ((([(13, 1), (71, 1), (115280627919018435618659311, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_13, prime_ninetyCJ_71, prime_ninetyCJ_115280627919018435618659311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544054 : Nat.totient 106404019569254016076022544054 = 32243624176444090640593495200 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (1803667, 1), (134042011, 1), (6668325710587, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_11, prime_ninetyCJ_1803667, prime_ninetyCJ_134042011, prime_ninetyCJ_6668325710587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544055 : Nat.totient 106404019569254016076022544055 = 84910897257370140034560000000 := by
  rw [← show ((([(5, 1), (401, 1), (2074481, 1), (715261531, 1), (35765914001, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_5, prime_ninetyCJ_401, prime_ninetyCJ_2074481, prime_ninetyCJ_715261531, prime_ninetyCJ_35765914001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544056 : Nat.totient 106404019569254016076022544056 = 53088086851469348491891331680 := by
  rw [← show ((([(2, 3), (467, 1), (28480733289414886529984621, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_467, prime_ninetyCJ_28480733289414886529984621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544057 : Nat.totient 106404019569254016076022544057 = 70719765236626060433629642752 := by
  rw [← show ((([(3, 1), (337, 1), (12289, 1), (8564269684882519486883, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_337, prime_ninetyCJ_12289, prime_ninetyCJ_8564269684882519486883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544058 : Nat.totient 106404019569254016076022544058 = 45601659998722690242236685360 := by
  rw [← show ((([(2, 1), (7, 1), (841411, 1), (5379403, 1), (1679143190181659, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_7, prime_ninetyCJ_841411, prime_ninetyCJ_5379403, prime_ninetyCJ_1679143190181659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544059 : Nat.totient 106404019569254016076022544059 = 106402933097048790244565035776 := by
  rw [← show ((([(99349, 1), (6882593, 1), (155611771171533487, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_99349, prime_ninetyCJ_6882593, prime_ninetyCJ_155611771171533487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544060 : Nat.totient 106404019569254016076022544060 = 28023809313223911616932372480 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (83, 1), (3209, 1), (2219410926540983004961, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_5, prime_ninetyCJ_83, prime_ninetyCJ_3209, prime_ninetyCJ_2219410926540983004961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544061 : Nat.totient 106404019569254016076022544061 = 106112796076870795704059934720 := by
  rw [← show ((([(383, 1), (8017, 1), (651863, 1), (18478217, 1), (2876941181, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_383, prime_ninetyCJ_8017, prime_ninetyCJ_651863, prime_ninetyCJ_18478217, prime_ninetyCJ_2876941181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544062 : Nat.totient 106404019569254016076022544062 = 51705599887722850439783648256 := by
  rw [← show ((([(2, 1), (37, 1), (887, 1), (324997, 1), (4987964371917315617, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_37, prime_ninetyCJ_887, prime_ninetyCJ_324997, prime_ninetyCJ_4987964371917315617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544063 : Nat.totient 106404019569254016076022544063 = 70076521226955451454153107200 := by
  rw [← show ((([(3, 1), (89, 1), (1123, 1), (59834051, 1), (5930872795958293, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_89, prime_ninetyCJ_1123, prime_ninetyCJ_59834051, prime_ninetyCJ_5930872795958293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544064 : Nat.totient 106404019569254016076022544064 = 53081611769516387307662929920 := by
  rw [← show ((([(2, 6), (443, 1), (175081, 1), (21435583782221690297, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_443, prime_ninetyCJ_175081, prime_ninetyCJ_21435583782221690297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544065 : Nat.totient 106404019569254016076022544065 = 62428026760265152289064115200 := by
  rw [← show ((([(5, 1), (7, 2), (11, 2), (17, 1), (211133748512801516129141, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_5, prime_ninetyCJ_7, prime_ninetyCJ_11, prime_ninetyCJ_17, prime_ninetyCJ_211133748512801516129141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544066 : Nat.totient 106404019569254016076022544066 = 32291209310795739336032129664 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (73, 1), (18687042425229015819463039, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_13, prime_ninetyCJ_73, prime_ninetyCJ_18687042425229015819463039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544067 : Nat.totient 106404019569254016076022544067 = 106404019569254016076022544066 := by
  rw [← show ((([(106404019569254016076022544067, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_106404019569254016076022544067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544068 : Nat.totient 106404019569254016076022544068 = 50401784932650331513476466176 := by
  rw [← show ((([(2, 2), (19, 1), (427717, 1), (40828927, 1), (80171491536977, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_19, prime_ninetyCJ_427717, prime_ninetyCJ_40828927, prime_ninetyCJ_80171491536977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544069 : Nat.totient 106404019569254016076022544069 = 70171954582090797443690496000 := by
  rw [← show ((([(3, 4), (97, 1), (2371, 1), (22433, 1), (3278701, 1), (77656990819, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_97, prime_ninetyCJ_2371, prime_ninetyCJ_22433, prime_ninetyCJ_3278701, prime_ninetyCJ_77656990819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544070 : Nat.totient 106404019569254016076022544070 = 42561589492587671393627541600 := by
  rw [← show ((([(2, 1), (5, 1), (2331151, 1), (550292983, 1), (8294565740479, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_5, prime_ninetyCJ_2331151, prime_ninetyCJ_550292983, prime_ninetyCJ_8294565740479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544071 : Nat.totient 106404019569254016076022544071 = 102715666056922606389402624000 := by
  rw [← show ((([(41, 1), (113, 1), (619, 1), (12451, 1), (73835959, 1), (40358306297, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_41, prime_ninetyCJ_113, prime_ninetyCJ_619, prime_ninetyCJ_12451, prime_ninetyCJ_73835959, prime_ninetyCJ_40358306297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544072 : Nat.totient 106404019569254016076022544072 = 30401148448358290307435012544 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (633357259340797714738229429, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_7, prime_ninetyCJ_633357259340797714738229429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544073 : Nat.totient 106404019569254016076022544073 = 104027083005314021937727000320 := by
  rw [← show ((([(53, 1), (283, 1), (246781, 1), (682775959, 1), (42102296813, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_53, prime_ninetyCJ_283, prime_ninetyCJ_246781, prime_ninetyCJ_682775959, prime_ninetyCJ_42102296813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544074 : Nat.totient 106404019569254016076022544074 = 49849291220224689001454362992 := by
  rw [← show ((([(2, 1), (23, 1), (67, 1), (179, 1), (192873414508561182566683, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_23, prime_ninetyCJ_67, prime_ninetyCJ_179, prime_ninetyCJ_192873414508561182566683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544075 : Nat.totient 106404019569254016076022544075 = 56494331465625824371581502080 := by
  rw [← show ((([(3, 1), (5, 2), (223, 1), (76368940909, 1), (83305780969403, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_5, prime_ninetyCJ_223, prime_ninetyCJ_76368940909, prime_ninetyCJ_83305780969403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544076 : Nat.totient 106404019569254016076022544076 = 46803918499614646482747801600 := by
  rw [← show ((([(2, 2), (11, 1), (31, 1), (34297, 1), (11712863, 1), (194188929245569, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_11, prime_ninetyCJ_31, prime_ninetyCJ_34297, prime_ninetyCJ_11712863, prime_ninetyCJ_194188929245569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544077 : Nat.totient 106404019569254016076022544077 = 105972786060851066563592084160 := by
  rw [← show ((([(373, 1), (727, 1), (6842041781, 1), (57349425254227, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_373, prime_ninetyCJ_727, prime_ninetyCJ_6842041781, prime_ninetyCJ_57349425254227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544078 : Nat.totient 106404019569254016076022544078 = 35142572018639779435395282240 := by
  rw [← show ((([(2, 1), (3, 2), (109, 1), (885371, 1), (136964263, 1), (447225412903, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_109, prime_ninetyCJ_885371, prime_ninetyCJ_136964263, prime_ninetyCJ_447225412903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544079 : Nat.totient 106404019569254016076022544079 = 80925802461633667726235174400 := by
  rw [← show ((([(7, 1), (13, 1), (29, 1), (227, 1), (91703, 1), (128096911, 1), (15120654371, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_7, prime_ninetyCJ_13, prime_ninetyCJ_29, prime_ninetyCJ_227, prime_ninetyCJ_91703, prime_ninetyCJ_128096911, prime_ninetyCJ_15120654371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544080 : Nat.totient 106404019569254016076022544080 = 41990862407391892952432640000 := by
  rw [← show ((([(2, 4), (5, 1), (101, 1), (311, 1), (3833, 1), (14983, 1), (507029, 1), (1454172361, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_5, prime_ninetyCJ_101, prime_ninetyCJ_311, prime_ninetyCJ_3833, prime_ninetyCJ_14983, prime_ninetyCJ_507029, prime_ninetyCJ_1454172361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544081 : Nat.totient 106404019569254016076022544081 = 70936013046167669324135074880 := by
  rw [← show ((([(3, 1), (44748077918891, 1), (792615195391697, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_44748077918891, prime_ninetyCJ_792615195391697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544082 : Nat.totient 106404019569254016076022544082 = 50069101223672420985030587904 := by
  rw [← show ((([(2, 1), (17, 1), (14843, 1), (9818873, 1), (21473151446225107, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_17, prime_ninetyCJ_14843, prime_ninetyCJ_9818873, prime_ninetyCJ_21473151446225107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544083 : Nat.totient 106404019569254016076022544083 = 106397246183742781541360968320 := by
  rw [← show ((([(28069, 1), (46141, 1), (157253, 1), (522450503165959, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_28069, prime_ninetyCJ_46141, prime_ninetyCJ_157253, prime_ninetyCJ_522450503165959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544084 : Nat.totient 106404019569254016076022544084 = 35460058716041321561923584000 := by
  rw [← show ((([(2, 2), (3, 1), (4649, 1), (111301, 1), (953385283, 1), (17974206721, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_4649, prime_ninetyCJ_111301, prime_ninetyCJ_953385283, prime_ninetyCJ_17974206721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544085 : Nat.totient 106404019569254016076022544085 = 85122960616322016889299079680 := by
  rw [← show ((([(5, 1), (333769, 1), (31237921933, 1), (2041079389421, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_5, prime_ninetyCJ_333769, prime_ninetyCJ_31237921933, prime_ninetyCJ_2041079389421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544086 : Nat.totient 106404019569254016076022544086 = 44609353811547350252881668480 := by
  rw [← show ((([(2, 1), (7, 1), (47, 1), (2083, 1), (64381, 1), (1205827412825469029, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_7, prime_ninetyCJ_47, prime_ninetyCJ_2083, prime_ninetyCJ_64381, prime_ninetyCJ_1205827412825469029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544087 : Nat.totient 106404019569254016076022544087 = 60843117056088381612213288960 := by
  rw [← show ((([(3, 2), (11, 1), (19, 1), (347, 1), (1289, 1), (2273, 1), (55640037108230453, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_11, prime_ninetyCJ_19, prime_ninetyCJ_347, prime_ninetyCJ_1289, prime_ninetyCJ_2273, prime_ninetyCJ_55640037108230453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544088 : Nat.totient 106404019569254016076022544088 = 53202009784614903072574255200 := by
  rw [← show ((([(2, 3), (4401458344021, 1), (3021839900910191, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_4401458344021, prime_ninetyCJ_3021839900910191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544089 : Nat.totient 106404019569254016076022544089 = 106403891854360502915605681776 := by
  rw [← show ((([(833429, 1), (2379091903, 1), (53663402740747, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_833429, prime_ninetyCJ_2379091903, prime_ninetyCJ_53663402740747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544090 : Nat.totient 106404019569254016076022544090 = 27809212754440703469302886720 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (59, 1), (331, 1), (181617115689920999668907, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_5, prime_ninetyCJ_59, prime_ninetyCJ_331, prime_ninetyCJ_181617115689920999668907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544091 : Nat.totient 106404019569254016076022544091 = 106404019569125311407074532712 := by
  rw [← show ((([(826735377437, 1), (128703842212633943, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_826735377437, prime_ninetyCJ_128703842212633943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544092 : Nat.totient 106404019569254016076022544092 = 47967404681723111235020196288 := by
  rw [← show ((([(2, 2), (13, 1), (43, 1), (795323, 1), (59833263752006014939, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_13, prime_ninetyCJ_43, prime_ninetyCJ_795323, prime_ninetyCJ_59833263752006014939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544093 : Nat.totient 106404019569254016076022544093 = 60533619668266517469975525120 := by
  rw [← show ((([(3, 1), (7, 1), (271, 1), (1367, 1), (13677317677156543722769, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_7, prime_ninetyCJ_271, prime_ninetyCJ_1367, prime_ninetyCJ_13677317677156543722769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544094 : Nat.totient 106404019569254016076022544094 = 53202009784627008038011272046 := by
  rw [← show ((([(2, 1), (53202009784627008038011272047, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_53202009784627008038011272047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544095 : Nat.totient 106404019569254016076022544095 = 85106547706381203224463830784 := by
  rw [← show ((([(5, 1), (5107, 1), (4166987255502409088546017, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_5, prime_ninetyCJ_5107, prime_ninetyCJ_4166987255502409088546017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544096 : Nat.totient 106404019569254016076022544096 = 35431703295315138676293746688 := by
  rw [← show ((([(2, 5), (3, 3), (977, 1), (140144509, 1), (899442990972073, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_3, prime_ninetyCJ_977, prime_ninetyCJ_140144509, prime_ninetyCJ_899442990972073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544097 : Nat.totient 106404019569254016076022544097 = 99137335354921566992198796480 := by
  rw [← show ((([(23, 1), (61, 1), (103, 1), (736314136623006290791733, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_23, prime_ninetyCJ_61, prime_ninetyCJ_103, prime_ninetyCJ_736314136623006290791733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544098 : Nat.totient 106404019569254016076022544098 = 48359500493530114568125294800 := by
  rw [← show ((([(2, 1), (11, 1), (8111, 1), (596294703989273915759869, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_11, prime_ninetyCJ_8111, prime_ninetyCJ_596294703989273915759869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544099 : Nat.totient 106404019569254016076022544099 = 64958892710005631435918372352 := by
  rw [← show ((([(3, 1), (17, 1), (37, 1), (56387927699657666177012477, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_3, prime_ninetyCJ_17, prime_ninetyCJ_37, prime_ninetyCJ_56387927699657666177012477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544100 : Nat.totient 106404019569254016076022544100 = 36333090913246468752622387200 := by
  rw [← show ((([(2, 2), (5, 2), (7, 1), (269, 1), (4289, 1), (8663, 1), (15208393949950661, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_2, prime_ninetyCJ_5, prime_ninetyCJ_7, prime_ninetyCJ_269, prime_ninetyCJ_4289, prime_ninetyCJ_8663, prime_ninetyCJ_15208393949950661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyCJ_106404019569254016076022544101 : Nat.totient 106404019569254016076022544101 = 106226971345284574083130915200 := by
  rw [← show ((([(601, 1), (40018213, 1), (174824659, 1), (25305981203, 1)] : List FactorBlock).map factorBlockValue).prod) = 106404019569254016076022544101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyCJ_601, prime_ninetyCJ_40018213, prime_ninetyCJ_174824659, prime_ninetyCJ_25305981203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NinetyCJ : certifiedKill 1 106404019569254016076022543999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_ninetyCJ_106404019569254016076022544000, phi_ninetyCJ_106404019569254016076022544001, phi_ninetyCJ_106404019569254016076022544002,
    phi_ninetyCJ_106404019569254016076022544003, phi_ninetyCJ_106404019569254016076022544004, phi_ninetyCJ_106404019569254016076022544005,
    phi_ninetyCJ_106404019569254016076022544006, phi_ninetyCJ_106404019569254016076022544007, phi_ninetyCJ_106404019569254016076022544008,
    phi_ninetyCJ_106404019569254016076022544009, phi_ninetyCJ_106404019569254016076022544010, phi_ninetyCJ_106404019569254016076022544011,
    phi_ninetyCJ_106404019569254016076022544012, phi_ninetyCJ_106404019569254016076022544013, phi_ninetyCJ_106404019569254016076022544014,
    phi_ninetyCJ_106404019569254016076022544015, phi_ninetyCJ_106404019569254016076022544016, phi_ninetyCJ_106404019569254016076022544017,
    phi_ninetyCJ_106404019569254016076022544018, phi_ninetyCJ_106404019569254016076022544019, phi_ninetyCJ_106404019569254016076022544020,
    phi_ninetyCJ_106404019569254016076022544021, phi_ninetyCJ_106404019569254016076022544022, phi_ninetyCJ_106404019569254016076022544023,
    phi_ninetyCJ_106404019569254016076022544024, phi_ninetyCJ_106404019569254016076022544025, phi_ninetyCJ_106404019569254016076022544026,
    phi_ninetyCJ_106404019569254016076022544027, phi_ninetyCJ_106404019569254016076022544028, phi_ninetyCJ_106404019569254016076022544029,
    phi_ninetyCJ_106404019569254016076022544030, phi_ninetyCJ_106404019569254016076022544031, phi_ninetyCJ_106404019569254016076022544032,
    phi_ninetyCJ_106404019569254016076022544033, phi_ninetyCJ_106404019569254016076022544034, phi_ninetyCJ_106404019569254016076022544035,
    phi_ninetyCJ_106404019569254016076022544036, phi_ninetyCJ_106404019569254016076022544037, phi_ninetyCJ_106404019569254016076022544038,
    phi_ninetyCJ_106404019569254016076022544039, phi_ninetyCJ_106404019569254016076022544040, phi_ninetyCJ_106404019569254016076022544041,
    phi_ninetyCJ_106404019569254016076022544042, phi_ninetyCJ_106404019569254016076022544043, phi_ninetyCJ_106404019569254016076022544044,
    phi_ninetyCJ_106404019569254016076022544045, phi_ninetyCJ_106404019569254016076022544046, phi_ninetyCJ_106404019569254016076022544047,
    phi_ninetyCJ_106404019569254016076022544048, phi_ninetyCJ_106404019569254016076022544049, phi_ninetyCJ_106404019569254016076022544050,
    phi_ninetyCJ_106404019569254016076022544051, phi_ninetyCJ_106404019569254016076022544052, phi_ninetyCJ_106404019569254016076022544053,
    phi_ninetyCJ_106404019569254016076022544054, phi_ninetyCJ_106404019569254016076022544055, phi_ninetyCJ_106404019569254016076022544056,
    phi_ninetyCJ_106404019569254016076022544057, phi_ninetyCJ_106404019569254016076022544058, phi_ninetyCJ_106404019569254016076022544059,
    phi_ninetyCJ_106404019569254016076022544060, phi_ninetyCJ_106404019569254016076022544061, phi_ninetyCJ_106404019569254016076022544062,
    phi_ninetyCJ_106404019569254016076022544063, phi_ninetyCJ_106404019569254016076022544064, phi_ninetyCJ_106404019569254016076022544065,
    phi_ninetyCJ_106404019569254016076022544066, phi_ninetyCJ_106404019569254016076022544067, phi_ninetyCJ_106404019569254016076022544068,
    phi_ninetyCJ_106404019569254016076022544069, phi_ninetyCJ_106404019569254016076022544070, phi_ninetyCJ_106404019569254016076022544071,
    phi_ninetyCJ_106404019569254016076022544072, phi_ninetyCJ_106404019569254016076022544073, phi_ninetyCJ_106404019569254016076022544074,
    phi_ninetyCJ_106404019569254016076022544075, phi_ninetyCJ_106404019569254016076022544076, phi_ninetyCJ_106404019569254016076022544077,
    phi_ninetyCJ_106404019569254016076022544078, phi_ninetyCJ_106404019569254016076022544079, phi_ninetyCJ_106404019569254016076022544080,
    phi_ninetyCJ_106404019569254016076022544081, phi_ninetyCJ_106404019569254016076022544082, phi_ninetyCJ_106404019569254016076022544083,
    phi_ninetyCJ_106404019569254016076022544084, phi_ninetyCJ_106404019569254016076022544085, phi_ninetyCJ_106404019569254016076022544086,
    phi_ninetyCJ_106404019569254016076022544087, phi_ninetyCJ_106404019569254016076022544088, phi_ninetyCJ_106404019569254016076022544089,
    phi_ninetyCJ_106404019569254016076022544090, phi_ninetyCJ_106404019569254016076022544091, phi_ninetyCJ_106404019569254016076022544092,
    phi_ninetyCJ_106404019569254016076022544093, phi_ninetyCJ_106404019569254016076022544094, phi_ninetyCJ_106404019569254016076022544095,
    phi_ninetyCJ_106404019569254016076022544096, phi_ninetyCJ_106404019569254016076022544097, phi_ninetyCJ_106404019569254016076022544098,
    phi_ninetyCJ_106404019569254016076022544099, phi_ninetyCJ_106404019569254016076022544100, phi_ninetyCJ_106404019569254016076022544101
    ]

end TotientTailPeriodKiller
end Erdos249257
