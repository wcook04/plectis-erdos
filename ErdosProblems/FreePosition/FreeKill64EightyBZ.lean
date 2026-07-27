import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def eightyBZFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem eightyBZFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : eightyBZFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [eightyBZFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [eightyBZFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then eightyBZFastPow a n * eightyBZFastPow a n * a else eightyBZFastPow a n * eightyBZFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_eightyBZ_2 : Nat.Prime 2 := by norm_num
private theorem prime_eightyBZ_3 : Nat.Prime 3 := by norm_num
private theorem prime_eightyBZ_5 : Nat.Prime 5 := by norm_num
private theorem prime_eightyBZ_7 : Nat.Prime 7 := by norm_num
private theorem prime_eightyBZ_11 : Nat.Prime 11 := by norm_num
private theorem prime_eightyBZ_13 : Nat.Prime 13 := by norm_num
private theorem prime_eightyBZ_17 : Nat.Prime 17 := by norm_num
private theorem prime_eightyBZ_19 : Nat.Prime 19 := by norm_num
private theorem prime_eightyBZ_23 : Nat.Prime 23 := by norm_num
private theorem prime_eightyBZ_29 : Nat.Prime 29 := by norm_num
private theorem prime_eightyBZ_31 : Nat.Prime 31 := by norm_num
private theorem prime_eightyBZ_37 : Nat.Prime 37 := by norm_num
private theorem prime_eightyBZ_41 : Nat.Prime 41 := by norm_num
private theorem prime_eightyBZ_43 : Nat.Prime 43 := by norm_num
private theorem prime_eightyBZ_47 : Nat.Prime 47 := by norm_num
private theorem prime_eightyBZ_53 : Nat.Prime 53 := by norm_num
private theorem prime_eightyBZ_59 : Nat.Prime 59 := by norm_num
private theorem prime_eightyBZ_61 : Nat.Prime 61 := by norm_num
private theorem prime_eightyBZ_67 : Nat.Prime 67 := by norm_num
private theorem prime_eightyBZ_71 : Nat.Prime 71 := by norm_num
private theorem prime_eightyBZ_73 : Nat.Prime 73 := by norm_num
private theorem prime_eightyBZ_79 : Nat.Prime 79 := by norm_num
private theorem prime_eightyBZ_83 : Nat.Prime 83 := by norm_num
private theorem prime_eightyBZ_89 : Nat.Prime 89 := by norm_num
private theorem prime_eightyBZ_97 : Nat.Prime 97 := by norm_num
private theorem prime_eightyBZ_101 : Nat.Prime 101 := by norm_num
private theorem prime_eightyBZ_103 : Nat.Prime 103 := by norm_num
private theorem prime_eightyBZ_107 : Nat.Prime 107 := by norm_num
private theorem prime_eightyBZ_109 : Nat.Prime 109 := by norm_num
private theorem prime_eightyBZ_113 : Nat.Prime 113 := by norm_num
private theorem prime_eightyBZ_127 : Nat.Prime 127 := by norm_num
private theorem prime_eightyBZ_131 : Nat.Prime 131 := by norm_num
private theorem prime_eightyBZ_137 : Nat.Prime 137 := by norm_num
private theorem prime_eightyBZ_139 : Nat.Prime 139 := by norm_num
private theorem prime_eightyBZ_149 : Nat.Prime 149 := by norm_num
private theorem prime_eightyBZ_151 : Nat.Prime 151 := by norm_num
private theorem prime_eightyBZ_157 : Nat.Prime 157 := by norm_num
private theorem prime_eightyBZ_163 : Nat.Prime 163 := by norm_num
private theorem prime_eightyBZ_167 : Nat.Prime 167 := by norm_num
private theorem prime_eightyBZ_173 : Nat.Prime 173 := by norm_num
private theorem prime_eightyBZ_179 : Nat.Prime 179 := by norm_num
private theorem prime_eightyBZ_181 : Nat.Prime 181 := by norm_num
private theorem prime_eightyBZ_191 : Nat.Prime 191 := by norm_num
private theorem prime_eightyBZ_193 : Nat.Prime 193 := by norm_num
private theorem prime_eightyBZ_197 : Nat.Prime 197 := by norm_num
private theorem prime_eightyBZ_211 : Nat.Prime 211 := by norm_num
private theorem prime_eightyBZ_223 : Nat.Prime 223 := by norm_num
private theorem prime_eightyBZ_227 : Nat.Prime 227 := by norm_num
private theorem prime_eightyBZ_229 : Nat.Prime 229 := by norm_num
private theorem prime_eightyBZ_233 : Nat.Prime 233 := by norm_num
private theorem prime_eightyBZ_239 : Nat.Prime 239 := by norm_num
private theorem prime_eightyBZ_241 : Nat.Prime 241 := by norm_num
private theorem prime_eightyBZ_251 : Nat.Prime 251 := by norm_num
private theorem prime_eightyBZ_257 : Nat.Prime 257 := by norm_num
private theorem prime_eightyBZ_269 : Nat.Prime 269 := by norm_num
private theorem prime_eightyBZ_281 : Nat.Prime 281 := by norm_num
private theorem prime_eightyBZ_283 : Nat.Prime 283 := by norm_num
private theorem prime_eightyBZ_293 : Nat.Prime 293 := by norm_num
private theorem prime_eightyBZ_307 : Nat.Prime 307 := by norm_num
private theorem prime_eightyBZ_311 : Nat.Prime 311 := by norm_num
private theorem prime_eightyBZ_317 : Nat.Prime 317 := by norm_num
private theorem prime_eightyBZ_331 : Nat.Prime 331 := by norm_num
private theorem prime_eightyBZ_337 : Nat.Prime 337 := by norm_num
private theorem prime_eightyBZ_349 : Nat.Prime 349 := by norm_num
private theorem prime_eightyBZ_359 : Nat.Prime 359 := by norm_num
private theorem prime_eightyBZ_373 : Nat.Prime 373 := by norm_num
private theorem prime_eightyBZ_383 : Nat.Prime 383 := by norm_num
private theorem prime_eightyBZ_389 : Nat.Prime 389 := by norm_num
private theorem prime_eightyBZ_401 : Nat.Prime 401 := by norm_num
private theorem prime_eightyBZ_409 : Nat.Prime 409 := by norm_num
private theorem prime_eightyBZ_431 : Nat.Prime 431 := by norm_num
private theorem prime_eightyBZ_433 : Nat.Prime 433 := by norm_num
private theorem prime_eightyBZ_443 : Nat.Prime 443 := by norm_num
private theorem prime_eightyBZ_449 : Nat.Prime 449 := by norm_num
private theorem prime_eightyBZ_457 : Nat.Prime 457 := by norm_num
private theorem prime_eightyBZ_461 : Nat.Prime 461 := by norm_num
private theorem prime_eightyBZ_499 : Nat.Prime 499 := by norm_num
private theorem prime_eightyBZ_521 : Nat.Prime 521 := by norm_num
private theorem prime_eightyBZ_523 : Nat.Prime 523 := by norm_num
private theorem prime_eightyBZ_541 : Nat.Prime 541 := by norm_num
private theorem prime_eightyBZ_557 : Nat.Prime 557 := by norm_num
private theorem prime_eightyBZ_563 : Nat.Prime 563 := by norm_num
private theorem prime_eightyBZ_577 : Nat.Prime 577 := by norm_num
private theorem prime_eightyBZ_587 : Nat.Prime 587 := by norm_num
private theorem prime_eightyBZ_619 : Nat.Prime 619 := by norm_num
private theorem prime_eightyBZ_643 : Nat.Prime 643 := by norm_num
private theorem prime_eightyBZ_653 : Nat.Prime 653 := by norm_num
private theorem prime_eightyBZ_659 : Nat.Prime 659 := by norm_num
private theorem prime_eightyBZ_673 : Nat.Prime 673 := by norm_num
private theorem prime_eightyBZ_683 : Nat.Prime 683 := by norm_num
private theorem prime_eightyBZ_701 : Nat.Prime 701 := by norm_num
private theorem prime_eightyBZ_709 : Nat.Prime 709 := by norm_num
private theorem prime_eightyBZ_727 : Nat.Prime 727 := by norm_num
private theorem prime_eightyBZ_739 : Nat.Prime 739 := by norm_num
private theorem prime_eightyBZ_769 : Nat.Prime 769 := by norm_num
private theorem prime_eightyBZ_773 : Nat.Prime 773 := by norm_num
private theorem prime_eightyBZ_787 : Nat.Prime 787 := by norm_num
private theorem prime_eightyBZ_809 : Nat.Prime 809 := by norm_num
private theorem prime_eightyBZ_857 : Nat.Prime 857 := by norm_num
private theorem prime_eightyBZ_863 : Nat.Prime 863 := by norm_num
private theorem prime_eightyBZ_919 : Nat.Prime 919 := by norm_num
private theorem prime_eightyBZ_941 : Nat.Prime 941 := by norm_num
private theorem prime_eightyBZ_947 : Nat.Prime 947 := by norm_num
private theorem prime_eightyBZ_991 : Nat.Prime 991 := by norm_num
private theorem prime_eightyBZ_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_eightyBZ_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_eightyBZ_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_eightyBZ_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_eightyBZ_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_eightyBZ_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_eightyBZ_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_eightyBZ_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_eightyBZ_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_eightyBZ_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_eightyBZ_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_eightyBZ_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_eightyBZ_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_eightyBZ_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_eightyBZ_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_eightyBZ_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_eightyBZ_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_eightyBZ_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_eightyBZ_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_eightyBZ_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_eightyBZ_1543 : Nat.Prime 1543 := by norm_num
private theorem prime_eightyBZ_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_eightyBZ_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_eightyBZ_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_eightyBZ_1583 : Nat.Prime 1583 := by norm_num
private theorem prime_eightyBZ_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_eightyBZ_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_eightyBZ_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_eightyBZ_1699 : Nat.Prime 1699 := by norm_num
private theorem prime_eightyBZ_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_eightyBZ_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_eightyBZ_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_eightyBZ_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_eightyBZ_1877 : Nat.Prime 1877 := by norm_num
private theorem prime_eightyBZ_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_eightyBZ_1951 : Nat.Prime 1951 := by norm_num
private theorem prime_eightyBZ_1987 : Nat.Prime 1987 := by norm_num
private theorem prime_eightyBZ_2027 : Nat.Prime 2027 := by norm_num
private theorem prime_eightyBZ_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_eightyBZ_2083 : Nat.Prime 2083 := by norm_num
private theorem prime_eightyBZ_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_eightyBZ_2267 : Nat.Prime 2267 := by norm_num
private theorem prime_eightyBZ_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_eightyBZ_2339 : Nat.Prime 2339 := by norm_num
private theorem prime_eightyBZ_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_eightyBZ_2347 : Nat.Prime 2347 := by norm_num
private theorem prime_eightyBZ_2437 : Nat.Prime 2437 := by norm_num
private theorem prime_eightyBZ_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_eightyBZ_2647 : Nat.Prime 2647 := by norm_num
private theorem prime_eightyBZ_2689 : Nat.Prime 2689 := by norm_num
private theorem prime_eightyBZ_2713 : Nat.Prime 2713 := by norm_num
private theorem prime_eightyBZ_2753 : Nat.Prime 2753 := by norm_num
private theorem prime_eightyBZ_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_eightyBZ_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_eightyBZ_2887 : Nat.Prime 2887 := by norm_num
private theorem prime_eightyBZ_2927 : Nat.Prime 2927 := by norm_num
private theorem prime_eightyBZ_2969 : Nat.Prime 2969 := by norm_num
private theorem prime_eightyBZ_3001 : Nat.Prime 3001 := by norm_num
private theorem prime_eightyBZ_3049 : Nat.Prime 3049 := by norm_num
private theorem prime_eightyBZ_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_eightyBZ_3169 : Nat.Prime 3169 := by norm_num
private theorem prime_eightyBZ_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_eightyBZ_3251 : Nat.Prime 3251 := by norm_num
private theorem prime_eightyBZ_3343 : Nat.Prime 3343 := by norm_num
private theorem prime_eightyBZ_3433 : Nat.Prime 3433 := by norm_num
private theorem prime_eightyBZ_3499 : Nat.Prime 3499 := by norm_num
private theorem prime_eightyBZ_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_eightyBZ_3593 : Nat.Prime 3593 := by norm_num
private theorem prime_eightyBZ_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_eightyBZ_3803 : Nat.Prime 3803 := by norm_num
private theorem prime_eightyBZ_3821 : Nat.Prime 3821 := by norm_num
private theorem prime_eightyBZ_3847 : Nat.Prime 3847 := by norm_num
private theorem prime_eightyBZ_3911 : Nat.Prime 3911 := by norm_num
private theorem prime_eightyBZ_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_eightyBZ_4231 : Nat.Prime 4231 := by norm_num
private theorem prime_eightyBZ_4451 : Nat.Prime 4451 := by norm_num
private theorem prime_eightyBZ_4517 : Nat.Prime 4517 := by norm_num
private theorem prime_eightyBZ_4801 : Nat.Prime 4801 := by norm_num
private theorem prime_eightyBZ_4903 : Nat.Prime 4903 := by norm_num
private theorem prime_eightyBZ_4931 : Nat.Prime 4931 := by norm_num
private theorem prime_eightyBZ_4943 : Nat.Prime 4943 := by norm_num
private theorem prime_eightyBZ_4957 : Nat.Prime 4957 := by norm_num
private theorem prime_eightyBZ_5059 : Nat.Prime 5059 := by norm_num
private theorem prime_eightyBZ_5197 : Nat.Prime 5197 := by norm_num
private theorem prime_eightyBZ_5233 : Nat.Prime 5233 := by norm_num
private theorem prime_eightyBZ_5507 : Nat.Prime 5507 := by norm_num
private theorem prime_eightyBZ_5653 : Nat.Prime 5653 := by norm_num
private theorem prime_eightyBZ_5813 : Nat.Prime 5813 := by norm_num
private theorem prime_eightyBZ_6257 : Nat.Prime 6257 := by norm_num
private theorem prime_eightyBZ_6287 : Nat.Prime 6287 := by norm_num
private theorem prime_eightyBZ_6329 : Nat.Prime 6329 := by norm_num
private theorem prime_eightyBZ_6619 : Nat.Prime 6619 := by norm_num
private theorem prime_eightyBZ_7103 : Nat.Prime 7103 := by norm_num
private theorem prime_eightyBZ_7159 : Nat.Prime 7159 := by norm_num
private theorem prime_eightyBZ_7243 : Nat.Prime 7243 := by norm_num
private theorem prime_eightyBZ_7507 : Nat.Prime 7507 := by norm_num
private theorem prime_eightyBZ_7523 : Nat.Prime 7523 := by norm_num
private theorem prime_eightyBZ_7559 : Nat.Prime 7559 := by norm_num
private theorem prime_eightyBZ_7573 : Nat.Prime 7573 := by norm_num
private theorem prime_eightyBZ_7759 : Nat.Prime 7759 := by norm_num
private theorem prime_eightyBZ_8167 : Nat.Prime 8167 := by norm_num
private theorem prime_eightyBZ_8803 : Nat.Prime 8803 := by norm_num
private theorem prime_eightyBZ_8929 : Nat.Prime 8929 := by norm_num
private theorem prime_eightyBZ_9661 : Nat.Prime 9661 := by norm_num
private theorem prime_eightyBZ_9689 : Nat.Prime 9689 := by norm_num
private theorem prime_eightyBZ_9743 : Nat.Prime 9743 := by norm_num
private theorem prime_eightyBZ_9787 : Nat.Prime 9787 := by norm_num
private theorem prime_eightyBZ_9973 : Nat.Prime 9973 := by norm_num
private theorem prime_eightyBZ_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_eightyBZ_10487 : Nat.Prime 10487 := by norm_num
private theorem prime_eightyBZ_10597 : Nat.Prime 10597 := by norm_num
private theorem prime_eightyBZ_10631 : Nat.Prime 10631 := by norm_num
private theorem prime_eightyBZ_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_eightyBZ_11243 : Nat.Prime 11243 := by norm_num
private theorem prime_eightyBZ_11447 : Nat.Prime 11447 := by norm_num
private theorem prime_eightyBZ_11597 : Nat.Prime 11597 := by norm_num
private theorem prime_eightyBZ_11699 : Nat.Prime 11699 := by norm_num
private theorem prime_eightyBZ_12479 : Nat.Prime 12479 := by norm_num
private theorem prime_eightyBZ_12611 : Nat.Prime 12611 := by norm_num
private theorem prime_eightyBZ_13007 : Nat.Prime 13007 := by norm_num
private theorem prime_eightyBZ_14009 : Nat.Prime 14009 := by norm_num
private theorem prime_eightyBZ_15031 : Nat.Prime 15031 := by norm_num
private theorem prime_eightyBZ_15541 : Nat.Prime 15541 := by norm_num
private theorem prime_eightyBZ_15581 : Nat.Prime 15581 := by norm_num
private theorem prime_eightyBZ_15601 : Nat.Prime 15601 := by norm_num
private theorem prime_eightyBZ_15797 : Nat.Prime 15797 := by norm_num
private theorem prime_eightyBZ_15877 : Nat.Prime 15877 := by norm_num
private theorem prime_eightyBZ_16319 : Nat.Prime 16319 := by norm_num
private theorem prime_eightyBZ_16759 : Nat.Prime 16759 := by norm_num
private theorem prime_eightyBZ_16987 : Nat.Prime 16987 := by norm_num
private theorem prime_eightyBZ_17293 : Nat.Prime 17293 := by norm_num
private theorem prime_eightyBZ_17383 : Nat.Prime 17383 := by norm_num
private theorem prime_eightyBZ_17431 : Nat.Prime 17431 := by norm_num
private theorem prime_eightyBZ_17519 : Nat.Prime 17519 := by norm_num
private theorem prime_eightyBZ_18089 : Nat.Prime 18089 := by norm_num
private theorem prime_eightyBZ_18223 : Nat.Prime 18223 := by norm_num
private theorem prime_eightyBZ_18289 : Nat.Prime 18289 := by norm_num
private theorem prime_eightyBZ_18539 : Nat.Prime 18539 := by norm_num
private theorem prime_eightyBZ_18749 : Nat.Prime 18749 := by norm_num
private theorem prime_eightyBZ_19219 : Nat.Prime 19219 := by norm_num
private theorem prime_eightyBZ_20029 : Nat.Prime 20029 := by norm_num
private theorem prime_eightyBZ_20107 : Nat.Prime 20107 := by norm_num
private theorem prime_eightyBZ_20113 : Nat.Prime 20113 := by norm_num
private theorem prime_eightyBZ_20341 : Nat.Prime 20341 := by norm_num
private theorem prime_eightyBZ_20563 : Nat.Prime 20563 := by norm_num
private theorem prime_eightyBZ_21149 : Nat.Prime 21149 := by norm_num
private theorem prime_eightyBZ_21433 : Nat.Prime 21433 := by norm_num
private theorem prime_eightyBZ_21481 : Nat.Prime 21481 := by norm_num
private theorem prime_eightyBZ_22129 : Nat.Prime 22129 := by norm_num
private theorem prime_eightyBZ_22279 : Nat.Prime 22279 := by norm_num
private theorem prime_eightyBZ_22409 : Nat.Prime 22409 := by norm_num
private theorem prime_eightyBZ_22643 : Nat.Prime 22643 := by norm_num
private theorem prime_eightyBZ_22679 : Nat.Prime 22679 := by norm_num
private theorem prime_eightyBZ_22783 : Nat.Prime 22783 := by norm_num
private theorem prime_eightyBZ_22817 : Nat.Prime 22817 := by norm_num
private theorem prime_eightyBZ_23593 : Nat.Prime 23593 := by norm_num
private theorem prime_eightyBZ_24371 : Nat.Prime 24371 := by norm_num
private theorem prime_eightyBZ_25793 : Nat.Prime 25793 := by norm_num
private theorem prime_eightyBZ_26591 : Nat.Prime 26591 := by norm_num
private theorem prime_eightyBZ_27109 : Nat.Prime 27109 := by norm_num
private theorem prime_eightyBZ_28843 : Nat.Prime 28843 := by norm_num
private theorem prime_eightyBZ_31957 : Nat.Prime 31957 := by norm_num
private theorem prime_eightyBZ_32537 : Nat.Prime 32537 := by norm_num
private theorem prime_eightyBZ_33289 : Nat.Prime 33289 := by norm_num
private theorem prime_eightyBZ_35117 : Nat.Prime 35117 := by norm_num
private theorem prime_eightyBZ_35831 : Nat.Prime 35831 := by norm_num
private theorem prime_eightyBZ_36313 : Nat.Prime 36313 := by norm_num
private theorem prime_eightyBZ_38903 : Nat.Prime 38903 := by norm_num
private theorem prime_eightyBZ_38971 : Nat.Prime 38971 := by norm_num
private theorem prime_eightyBZ_39019 : Nat.Prime 39019 := by norm_num
private theorem prime_eightyBZ_39857 : Nat.Prime 39857 := by norm_num
private theorem prime_eightyBZ_39877 : Nat.Prime 39877 := by norm_num
private theorem prime_eightyBZ_40063 : Nat.Prime 40063 := by norm_num
private theorem prime_eightyBZ_41081 : Nat.Prime 41081 := by norm_num
private theorem prime_eightyBZ_41681 : Nat.Prime 41681 := by norm_num
private theorem prime_eightyBZ_41957 : Nat.Prime 41957 := by norm_num
private theorem prime_eightyBZ_42433 : Nat.Prime 42433 := by norm_num
private theorem prime_eightyBZ_43577 : Nat.Prime 43577 := by norm_num
private theorem prime_eightyBZ_44501 : Nat.Prime 44501 := by norm_num
private theorem prime_eightyBZ_46511 : Nat.Prime 46511 := by norm_num
private theorem prime_eightyBZ_48247 : Nat.Prime 48247 := by norm_num
private theorem prime_eightyBZ_50777 : Nat.Prime 50777 := by norm_num
private theorem prime_eightyBZ_50867 : Nat.Prime 50867 := by norm_num
private theorem prime_eightyBZ_53719 : Nat.Prime 53719 := by norm_num
private theorem prime_eightyBZ_60091 : Nat.Prime 60091 := by norm_num
private theorem prime_eightyBZ_61729 : Nat.Prime 61729 := by norm_num
private theorem prime_eightyBZ_62273 : Nat.Prime 62273 := by norm_num
private theorem prime_eightyBZ_62819 : Nat.Prime 62819 := by norm_num
private theorem prime_eightyBZ_63647 : Nat.Prime 63647 := by norm_num
private theorem prime_eightyBZ_65063 : Nat.Prime 65063 := by norm_num
private theorem prime_eightyBZ_65599 : Nat.Prime 65599 := by norm_num
private theorem prime_eightyBZ_68711 : Nat.Prime 68711 := by norm_num
private theorem prime_eightyBZ_74167 : Nat.Prime 74167 := by norm_num
private theorem prime_eightyBZ_78031 : Nat.Prime 78031 := by norm_num
private theorem prime_eightyBZ_80803 : Nat.Prime 80803 := by norm_num
private theorem prime_eightyBZ_82787 : Nat.Prime 82787 := by norm_num
private theorem prime_eightyBZ_83903 : Nat.Prime 83903 := by norm_num
private theorem prime_eightyBZ_84521 : Nat.Prime 84521 := by norm_num
private theorem prime_eightyBZ_85259 : Nat.Prime 85259 := by norm_num
private theorem prime_eightyBZ_95231 : Nat.Prime 95231 := by norm_num
private theorem prime_eightyBZ_98221 : Nat.Prime 98221 := by norm_num
private theorem prime_eightyBZ_103651 : Nat.Prime 103651 := by norm_num
private theorem prime_eightyBZ_106739 : Nat.Prime 106739 := by norm_num
private theorem prime_eightyBZ_108881 : Nat.Prime 108881 := by norm_num
private theorem prime_eightyBZ_110753 : Nat.Prime 110753 := by norm_num
private theorem prime_eightyBZ_120511 : Nat.Prime 120511 := by norm_num
private theorem prime_eightyBZ_127453 : Nat.Prime 127453 := by norm_num
private theorem prime_eightyBZ_134777 : Nat.Prime 134777 := by norm_num
private theorem prime_eightyBZ_148501 : Nat.Prime 148501 := by norm_num
private theorem prime_eightyBZ_150221 : Nat.Prime 150221 := by norm_num
private theorem prime_eightyBZ_157259 : Nat.Prime 157259 := by norm_num
private theorem prime_eightyBZ_157427 : Nat.Prime 157427 := by norm_num
private theorem prime_eightyBZ_163417 : Nat.Prime 163417 := by norm_num
private theorem prime_eightyBZ_163997 : Nat.Prime 163997 := by norm_num
private theorem prime_eightyBZ_182339 : Nat.Prime 182339 := by norm_num
private theorem prime_eightyBZ_203449 : Nat.Prime 203449 := by norm_num
private theorem prime_eightyBZ_208993 : Nat.Prime 208993 := by norm_num
private theorem prime_eightyBZ_213043 : Nat.Prime 213043 := by norm_num
private theorem prime_eightyBZ_215899 : Nat.Prime 215899 := by norm_num
private theorem prime_eightyBZ_220411 : Nat.Prime 220411 := by norm_num
private theorem prime_eightyBZ_230327 : Nat.Prime 230327 := by norm_num
private theorem prime_eightyBZ_241931 : Nat.Prime 241931 := by norm_num
private theorem prime_eightyBZ_247241 : Nat.Prime 247241 := by norm_num
private theorem prime_eightyBZ_249677 : Nat.Prime 249677 := by norm_num
private theorem prime_eightyBZ_251081 : Nat.Prime 251081 := by norm_num
private theorem prime_eightyBZ_262459 : Nat.Prime 262459 := by norm_num
private theorem prime_eightyBZ_265747 : Nat.Prime 265747 := by norm_num
private theorem prime_eightyBZ_267193 : Nat.Prime 267193 := by norm_num
private theorem prime_eightyBZ_270899 : Nat.Prime 270899 := by norm_num
private theorem prime_eightyBZ_274213 : Nat.Prime 274213 := by norm_num
private theorem prime_eightyBZ_275963 : Nat.Prime 275963 := by norm_num
private theorem prime_eightyBZ_301531 : Nat.Prime 301531 := by norm_num
private theorem prime_eightyBZ_307481 : Nat.Prime 307481 := by norm_num
private theorem prime_eightyBZ_321359 : Nat.Prime 321359 := by norm_num
private theorem prime_eightyBZ_322417 : Nat.Prime 322417 := by norm_num
private theorem prime_eightyBZ_355951 : Nat.Prime 355951 := by norm_num
private theorem prime_eightyBZ_361469 : Nat.Prime 361469 := by norm_num
private theorem prime_eightyBZ_417383 : Nat.Prime 417383 := by norm_num
private theorem prime_eightyBZ_420769 : Nat.Prime 420769 := by norm_num
private theorem prime_eightyBZ_434407 : Nat.Prime 434407 := by norm_num
private theorem prime_eightyBZ_445019 : Nat.Prime 445019 := by norm_num
private theorem prime_eightyBZ_457679 : Nat.Prime 457679 := by norm_num
private theorem prime_eightyBZ_461609 : Nat.Prime 461609 := by norm_num
private theorem prime_eightyBZ_464257 : Nat.Prime 464257 := by norm_num
private theorem prime_eightyBZ_475051 : Nat.Prime 475051 := by norm_num
private theorem prime_eightyBZ_512249 : Nat.Prime 512249 := by norm_num
private theorem prime_eightyBZ_529723 : Nat.Prime 529723 := by norm_num
private theorem prime_eightyBZ_540121 : Nat.Prime 540121 := by norm_num
private theorem prime_eightyBZ_566549 : Nat.Prime 566549 := by norm_num
private theorem prime_eightyBZ_583021 : Nat.Prime 583021 := by norm_num
private theorem prime_eightyBZ_601949 : Nat.Prime 601949 := by norm_num
private theorem prime_eightyBZ_668527 : Nat.Prime 668527 := by norm_num
private theorem prime_eightyBZ_676099 : Nat.Prime 676099 := by norm_num
private theorem prime_eightyBZ_682819 : Nat.Prime 682819 := by norm_num
private theorem prime_eightyBZ_743167 : Nat.Prime 743167 := by norm_num
private theorem prime_eightyBZ_749543 : Nat.Prime 749543 := by norm_num
private theorem prime_eightyBZ_750713 : Nat.Prime 750713 := by norm_num
private theorem prime_eightyBZ_771623 : Nat.Prime 771623 := by norm_num
private theorem prime_eightyBZ_796379 : Nat.Prime 796379 := by norm_num
private theorem prime_eightyBZ_807869 : Nat.Prime 807869 := by norm_num
private theorem prime_eightyBZ_815653 : Nat.Prime 815653 := by norm_num
private theorem prime_eightyBZ_867343 : Nat.Prime 867343 := by norm_num
private theorem prime_eightyBZ_911341 : Nat.Prime 911341 := by norm_num
private theorem prime_eightyBZ_938263 : Nat.Prime 938263 := by norm_num
private theorem prime_eightyBZ_940097 : Nat.Prime 940097 := by norm_num
private theorem prime_eightyBZ_940127 : Nat.Prime 940127 := by norm_num
private theorem prime_eightyBZ_1005239 : Nat.Prime 1005239 := by norm_num
private theorem prime_eightyBZ_1030529 : Nat.Prime 1030529 := by norm_num
private theorem prime_eightyBZ_1036459 : Nat.Prime 1036459 := by norm_num
private theorem prime_eightyBZ_1038199 : Nat.Prime 1038199 := by norm_num
private theorem prime_eightyBZ_1192699 : Nat.Prime 1192699 := by norm_num
private theorem prime_eightyBZ_1213469 : Nat.Prime 1213469 := by norm_num
private theorem prime_eightyBZ_1284713 : Nat.Prime 1284713 := by norm_num
private theorem prime_eightyBZ_1315019 : Nat.Prime 1315019 := by norm_num
private theorem prime_eightyBZ_1324097 : Nat.Prime 1324097 := by norm_num
private theorem prime_eightyBZ_1335391 : Nat.Prime 1335391 := by norm_num
private theorem prime_eightyBZ_1486523 : Nat.Prime 1486523 := by norm_num
private theorem prime_eightyBZ_1538531 : Nat.Prime 1538531 := by norm_num
private theorem prime_eightyBZ_1622839 : Nat.Prime 1622839 := by norm_num
private theorem prime_eightyBZ_1802687 : Nat.Prime 1802687 := by norm_num
private theorem prime_eightyBZ_1874387 : Nat.Prime 1874387 := by norm_num
private theorem prime_eightyBZ_2158369 : Nat.Prime 2158369 := by norm_num
private theorem prime_eightyBZ_2173337 : Nat.Prime 2173337 := by norm_num
private theorem prime_eightyBZ_2261789 : Nat.Prime 2261789 := by norm_num
private theorem prime_eightyBZ_2380393 : Nat.Prime 2380393 := by norm_num
private theorem prime_eightyBZ_2473217 : Nat.Prime 2473217 := by norm_num
private theorem prime_eightyBZ_2679337 : Nat.Prime 2679337 := by norm_num
private theorem prime_eightyBZ_2753237 : Nat.Prime 2753237 := by norm_num
private theorem prime_eightyBZ_2823671 : Nat.Prime 2823671 := by norm_num
private theorem prime_eightyBZ_2831407 : Nat.Prime 2831407 := by norm_num
private theorem prime_eightyBZ_2905163 : Nat.Prime 2905163 := by norm_num
private theorem prime_eightyBZ_2991871 : Nat.Prime 2991871 := by norm_num
private theorem prime_eightyBZ_3154187 : Nat.Prime 3154187 := by norm_num
private theorem prime_eightyBZ_3356657 : Nat.Prime 3356657 := by norm_num
private theorem prime_eightyBZ_3453283 : Nat.Prime 3453283 := by norm_num
private theorem prime_eightyBZ_3526247 : Nat.Prime 3526247 := by norm_num
private theorem prime_eightyBZ_3832597 : Nat.Prime 3832597 := by norm_num
private theorem prime_eightyBZ_3897161 : Nat.Prime 3897161 := by norm_num
private theorem prime_eightyBZ_4098469 : Nat.Prime 4098469 := by norm_num
private theorem prime_eightyBZ_4372477 : Nat.Prime 4372477 := by norm_num
private theorem prime_eightyBZ_4427623 : Nat.Prime 4427623 := by norm_num
private theorem prime_eightyBZ_4459577 : Nat.Prime 4459577 := by norm_num
private theorem prime_eightyBZ_4629983 : Nat.Prime 4629983 := by norm_num
private theorem prime_eightyBZ_4862519 : Nat.Prime 4862519 := by norm_num
private theorem prime_eightyBZ_4920841 : Nat.Prime 4920841 := by norm_num
private theorem prime_eightyBZ_5230297 : Nat.Prime 5230297 := by norm_num
private theorem prime_eightyBZ_5442457 : Nat.Prime 5442457 := by norm_num
private theorem prime_eightyBZ_5840773 : Nat.Prime 5840773 := by norm_num
private theorem prime_eightyBZ_6328331 : Nat.Prime 6328331 := by norm_num
private theorem prime_eightyBZ_6391243 : Nat.Prime 6391243 := by norm_num
private theorem prime_eightyBZ_6411793 : Nat.Prime 6411793 := by norm_num
private theorem prime_eightyBZ_6472079 : Nat.Prime 6472079 := by norm_num
private theorem prime_eightyBZ_6831131 : Nat.Prime 6831131 := by norm_num
private theorem prime_eightyBZ_7227007 : Nat.Prime 7227007 := by norm_num
private theorem prime_eightyBZ_7237987 : Nat.Prime 7237987 := by norm_num
private theorem prime_eightyBZ_8140009 : Nat.Prime 8140009 := by norm_num
private theorem prime_eightyBZ_8292203 : Nat.Prime 8292203 := by norm_num
private theorem prime_eightyBZ_8595787 : Nat.Prime 8595787 := by norm_num
private theorem prime_eightyBZ_8919737 : Nat.Prime 8919737 := by norm_num
private theorem prime_eightyBZ_9194023 : Nat.Prime 9194023 := by norm_num
private theorem prime_eightyBZ_10619989 : Nat.Prime 10619989 := by norm_num
private theorem prime_eightyBZ_11141587 : Nat.Prime 11141587 := by norm_num
private theorem prime_eightyBZ_12216499 : Nat.Prime 12216499 := by norm_num
private theorem prime_eightyBZ_12283819 : Nat.Prime 12283819 := by norm_num
private theorem prime_eightyBZ_12964069 : Nat.Prime 12964069 := by norm_num
private theorem prime_eightyBZ_13299851 : Nat.Prime 13299851 := by norm_num
private theorem prime_eightyBZ_13809589 : Nat.Prime 13809589 := by norm_num
private theorem prime_eightyBZ_14101481 : Nat.Prime 14101481 := by norm_num
private theorem prime_eightyBZ_14309201 : Nat.Prime 14309201 := by norm_num
private theorem prime_eightyBZ_16067803 : Nat.Prime 16067803 := by norm_num
private theorem prime_eightyBZ_16350221 : Nat.Prime 16350221 := by norm_num
private theorem prime_eightyBZ_17056367 : Nat.Prime 17056367 := by norm_num
private theorem prime_eightyBZ_17623777 : Nat.Prime 17623777 := by norm_num
private theorem prime_eightyBZ_18044597 : Nat.Prime 18044597 := by norm_num
private theorem prime_eightyBZ_18452411 : Nat.Prime 18452411 := by norm_num
private theorem prime_eightyBZ_19122899 : Nat.Prime 19122899 := by norm_num
private theorem prime_eightyBZ_19394213 : Nat.Prime 19394213 := by norm_num
private theorem prime_eightyBZ_19676807 : Nat.Prime 19676807 := by norm_num
private theorem prime_eightyBZ_20783177 : Nat.Prime 20783177 := by norm_num
private theorem prime_eightyBZ_22660177 : Nat.Prime 22660177 := by norm_num
private theorem prime_eightyBZ_24051089 : Nat.Prime 24051089 := by norm_num
private theorem prime_eightyBZ_24135401 : Nat.Prime 24135401 := by norm_num
private theorem prime_eightyBZ_26670967 : Nat.Prime 26670967 := by norm_num
private theorem prime_eightyBZ_28856273 : Nat.Prime 28856273 := by norm_num
private theorem prime_eightyBZ_31045307 : Nat.Prime 31045307 := by
  apply lucas_primality 31045307 (2 : ZMod 31045307)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (163, 1), (95231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (163, 1), (95231, 1)] : List FactorBlock).map factorBlockValue).prod) = 31045307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_163
      · exact prime_eightyBZ_95231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31045307) ^ 15522653 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31045307) ^ 190462 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31045307) ^ 326 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_33738967 : Nat.Prime 33738967 := by
  apply lucas_primality 33738967 (3 : ZMod 33738967)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1874387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1874387, 1)] : List FactorBlock).map factorBlockValue).prod) = 33738967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_1874387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33738967) ^ 16869483 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 33738967) ^ 11246322 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 33738967) ^ 18 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_34383149 : Nat.Prime 34383149 := by
  apply lucas_primality 34383149 (2 : ZMod 34383149)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8595787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8595787, 1)] : List FactorBlock).map factorBlockValue).prod) = 34383149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_8595787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34383149) ^ 17191574 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 34383149) ^ 4 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_34694579 : Nat.Prime 34694579 := by
  apply lucas_primality 34694579 (2 : ZMod 34694579)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1637, 1), (10597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1637, 1), (10597, 1)] : List FactorBlock).map factorBlockValue).prod) = 34694579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_1637
      · exact prime_eightyBZ_10597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34694579) ^ 17347289 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 34694579) ^ 21194 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 34694579) ^ 3274 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_36432181 : Nat.Prime 36432181 := by
  apply lucas_primality 36432181 (2 : ZMod 36432181)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (43, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (43, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) = 36432181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_43
      · exact prime_eightyBZ_523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36432181) ^ 18216090 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36432181) ^ 12144060 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36432181) ^ 7286436 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36432181) ^ 847260 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36432181) ^ 69660 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_37987153 : Nat.Prime 37987153 := by
  apply lucas_primality 37987153 (34 : ZMod 37987153)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (31, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (31, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) = 37987153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_31
      · exact prime_eightyBZ_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 37987153) ^ 18993576 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (34 : ZMod 37987153) ^ 12662384 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (34 : ZMod 37987153) ^ 5426736 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (34 : ZMod 37987153) ^ 1225392 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (34 : ZMod 37987153) ^ 72912 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_38153263 : Nat.Prime 38153263 := by
  apply lucas_primality 38153263 (5 : ZMod 38153263)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) = 38153263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_18539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 38153263) ^ 19076631 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 38153263) ^ 12717754 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 38153263) ^ 5450466 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 38153263) ^ 2058 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_38303231 : Nat.Prime 38303231 := by
  apply lucas_primality 38303231 (7 : ZMod 38303231)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (67, 1), (8167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (67, 1), (8167, 1)] : List FactorBlock).map factorBlockValue).prod) = 38303231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_67
      · exact prime_eightyBZ_8167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 38303231) ^ 19151615 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 38303231) ^ 7660646 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 38303231) ^ 5471890 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 38303231) ^ 571690 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 38303231) ^ 4690 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_38581111 : Nat.Prime 38581111 := by
  apply lucas_primality 38581111 (3 : ZMod 38581111)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (15877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (15877, 1)] : List FactorBlock).map factorBlockValue).prod) = 38581111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_15877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38581111) ^ 19290555 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 38581111) ^ 12860370 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 38581111) ^ 7716222 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 38581111) ^ 2430 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_38878481 : Nat.Prime 38878481 := by
  apply lucas_primality 38878481 (3 : ZMod 38878481)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (307, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (307, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) = 38878481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_307
      · exact prime_eightyBZ_1583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38878481) ^ 19439240 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 38878481) ^ 7775696 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 38878481) ^ 126640 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 38878481) ^ 24560 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_41974409 : Nat.Prime 41974409 := by
  apply lucas_primality 41974409 (3 : ZMod 41974409)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (749543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (749543, 1)] : List FactorBlock).map factorBlockValue).prod) = 41974409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_749543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 41974409) ^ 20987204 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 41974409) ^ 5996344 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 41974409) ^ 56 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_42077611 : Nat.Prime 42077611 := by
  apply lucas_primality 42077611 (7 : ZMod 42077611)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (101, 1), (1543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (101, 1), (1543, 1)] : List FactorBlock).map factorBlockValue).prod) = 42077611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_101
      · exact prime_eightyBZ_1543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 42077611) ^ 21038805 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 42077611) ^ 14025870 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 42077611) ^ 8415522 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 42077611) ^ 416610 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 42077611) ^ 27270 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_43295341 : Nat.Prime 43295341 := by
  apply lucas_primality 43295341 (6 : ZMod 43295341)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (65599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (65599, 1)] : List FactorBlock).map factorBlockValue).prod) = 43295341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_65599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 43295341) ^ 21647670 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 43295341) ^ 14431780 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 43295341) ^ 8659068 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 43295341) ^ 3935940 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 43295341) ^ 660 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_48865997 : Nat.Prime 48865997 := by
  apply lucas_primality 48865997 (2 : ZMod 48865997)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (12216499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (12216499, 1)] : List FactorBlock).map factorBlockValue).prod) = 48865997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_12216499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 48865997) ^ 24432998 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 48865997) ^ 4 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_50981201 : Nat.Prime 50981201 := by
  apply lucas_primality 50981201 (6 : ZMod 50981201)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (127453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (127453, 1)] : List FactorBlock).map factorBlockValue).prod) = 50981201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_127453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 50981201) ^ 25490600 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 50981201) ^ 10196240 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 50981201) ^ 400 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_52368647 : Nat.Prime 52368647 := by
  apply lucas_primality 52368647 (5 : ZMod 52368647)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2380393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2380393, 1)] : List FactorBlock).map factorBlockValue).prod) = 52368647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_2380393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52368647) ^ 26184323 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 52368647) ^ 4760786 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 52368647) ^ 22 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_59961953 : Nat.Prime 59961953 := by
  apply lucas_primality 59961953 (5 : ZMod 59961953)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (43, 1), (43577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (43, 1), (43577, 1)] : List FactorBlock).map factorBlockValue).prod) = 59961953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_43
      · exact prime_eightyBZ_43577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 59961953) ^ 29980976 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 59961953) ^ 1394464 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 59961953) ^ 1376 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_61607417 : Nat.Prime 61607417 := by
  apply lucas_primality 61607417 (3 : ZMod 61607417)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (31, 1), (97, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (31, 1), (97, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) = 61607417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_31
      · exact prime_eightyBZ_97
      · exact prime_eightyBZ_197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 61607417) ^ 30803708 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 61607417) ^ 4739032 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 61607417) ^ 1987336 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 61607417) ^ 635128 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 61607417) ^ 312728 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_63341087 : Nat.Prime 63341087 := by
  apply lucas_primality 63341087 (5 : ZMod 63341087)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (307481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (307481, 1)] : List FactorBlock).map factorBlockValue).prod) = 63341087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_103
      · exact prime_eightyBZ_307481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 63341087) ^ 31670543 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 63341087) ^ 614962 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 63341087) ^ 206 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_64209283 : Nat.Prime 64209283 := by
  apply lucas_primality 64209283 (3 : ZMod 64209283)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (223, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (223, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod) = 64209283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_37
      · exact prime_eightyBZ_223
      · exact prime_eightyBZ_1297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64209283) ^ 32104641 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64209283) ^ 21403094 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64209283) ^ 1735386 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64209283) ^ 287934 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64209283) ^ 49506 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_65771177 : Nat.Prime 65771177 := by
  apply lucas_primality 65771177 (3 : ZMod 65771177)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (134777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (134777, 1)] : List FactorBlock).map factorBlockValue).prod) = 65771177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_61
      · exact prime_eightyBZ_134777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 65771177) ^ 32885588 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 65771177) ^ 1078216 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 65771177) ^ 488 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_65810999 : Nat.Prime 65810999 := by
  apply lucas_primality 65810999 (7 : ZMod 65810999)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (47, 1), (63647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (47, 1), (63647, 1)] : List FactorBlock).map factorBlockValue).prod) = 65810999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_47
      · exact prime_eightyBZ_63647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 65810999) ^ 32905499 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 65810999) ^ 5982818 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 65810999) ^ 1400234 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 65810999) ^ 1034 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_65955503 : Nat.Prime 65955503 := by
  apply lucas_primality 65955503 (5 : ZMod 65955503)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1907, 1), (17293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1907, 1), (17293, 1)] : List FactorBlock).map factorBlockValue).prod) = 65955503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_1907
      · exact prime_eightyBZ_17293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 65955503) ^ 32977751 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 65955503) ^ 34586 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 65955503) ^ 3814 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_67227001 : Nat.Prime 67227001 := by
  apply lucas_primality 67227001 (22 : ZMod 67227001)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (22409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (22409, 1)] : List FactorBlock).map factorBlockValue).prod) = 67227001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_22409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 67227001) ^ 33613500 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (22 : ZMod 67227001) ^ 22409000 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (22 : ZMod 67227001) ^ 13445400 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (22 : ZMod 67227001) ^ 3000 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_72854233 : Nat.Prime 72854233 := by
  apply lucas_primality 72854233 (5 : ZMod 72854233)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (275963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (275963, 1)] : List FactorBlock).map factorBlockValue).prod) = 72854233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_275963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 72854233) ^ 36427116 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 72854233) ^ 24284744 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 72854233) ^ 6623112 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 72854233) ^ 264 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_80982469 : Nat.Prime 80982469 := by
  apply lucas_primality 80982469 (10 : ZMod 80982469)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (321359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (321359, 1)] : List FactorBlock).map factorBlockValue).prod) = 80982469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_321359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 80982469) ^ 40491234 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 80982469) ^ 26994156 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 80982469) ^ 11568924 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 80982469) ^ 252 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_87079313 : Nat.Prime 87079313 := by
  apply lucas_primality 87079313 (3 : ZMod 87079313)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5442457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5442457, 1)] : List FactorBlock).map factorBlockValue).prod) = 87079313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5442457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 87079313) ^ 43539656 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 87079313) ^ 16 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_94124663 : Nat.Prime 94124663 := by
  apply lucas_primality 94124663 (5 : ZMod 94124663)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (1622839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (1622839, 1)] : List FactorBlock).map factorBlockValue).prod) = 94124663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_29
      · exact prime_eightyBZ_1622839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 94124663) ^ 47062331 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 94124663) ^ 3245678 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 94124663) ^ 58 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_101962403 : Nat.Prime 101962403 := by
  apply lucas_primality 101962403 (2 : ZMod 101962403)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (50981201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (50981201, 1)] : List FactorBlock).map factorBlockValue).prod) = 101962403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_50981201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 101962403) ^ 50981201 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 101962403) ^ 2 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_103862573 : Nat.Prime 103862573 := by
  apply lucas_primality 103862573 (3 : ZMod 103862573)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (23, 1), (29, 1), (3539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (23, 1), (29, 1), (3539, 1)] : List FactorBlock).map factorBlockValue).prod) = 103862573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_23
      · exact prime_eightyBZ_29
      · exact prime_eightyBZ_3539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 103862573) ^ 51931286 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 103862573) ^ 9442052 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 103862573) ^ 4515764 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 103862573) ^ 3581468 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 103862573) ^ 29348 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_104390743 : Nat.Prime 104390743 := by
  apply lucas_primality 104390743 (3 : ZMod 104390743)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (106739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (106739, 1)] : List FactorBlock).map factorBlockValue).prod) = 104390743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_163
      · exact prime_eightyBZ_106739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 104390743) ^ 52195371 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 104390743) ^ 34796914 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 104390743) ^ 640434 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 104390743) ^ 978 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_107199097 : Nat.Prime 107199097 := by
  apply lucas_primality 107199097 (5 : ZMod 107199097)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (461, 1), (9689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (461, 1), (9689, 1)] : List FactorBlock).map factorBlockValue).prod) = 107199097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_461
      · exact prime_eightyBZ_9689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 107199097) ^ 53599548 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 107199097) ^ 35733032 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 107199097) ^ 232536 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 107199097) ^ 11064 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_119859107 : Nat.Prime 119859107 := by
  apply lucas_primality 119859107 (2 : ZMod 119859107)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (3154187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (3154187, 1)] : List FactorBlock).map factorBlockValue).prod) = 119859107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_3154187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 119859107) ^ 59929553 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 119859107) ^ 6308374 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 119859107) ^ 38 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_119923907 : Nat.Prime 119923907 := by
  apply lucas_primality 119923907 (2 : ZMod 119923907)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59961953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59961953, 1)] : List FactorBlock).map factorBlockValue).prod) = 119923907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_59961953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 119923907) ^ 59961953 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 119923907) ^ 2 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_124583881 : Nat.Prime 124583881 := by
  apply lucas_primality 124583881 (26 : ZMod 124583881)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (1038199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (1038199, 1)] : List FactorBlock).map factorBlockValue).prod) = 124583881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_1038199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 124583881) ^ 62291940 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (26 : ZMod 124583881) ^ 41527960 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (26 : ZMod 124583881) ^ 24916776 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (26 : ZMod 124583881) ^ 120 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_131621999 : Nat.Prime 131621999 := by
  apply lucas_primality 131621999 (11 : ZMod 131621999)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (65810999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (65810999, 1)] : List FactorBlock).map factorBlockValue).prod) = 131621999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_65810999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 131621999) ^ 65810999 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 131621999) ^ 2 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_152613053 : Nat.Prime 152613053 := by
  apply lucas_primality 152613053 (2 : ZMod 152613053)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (38153263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (38153263, 1)] : List FactorBlock).map factorBlockValue).prod) = 152613053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_38153263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 152613053) ^ 76306526 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 152613053) ^ 4 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_156121741 : Nat.Prime 156121741 := by
  apply lucas_primality 156121741 (6 : ZMod 156121741)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (867343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (867343, 1)] : List FactorBlock).map factorBlockValue).prod) = 156121741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_867343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 156121741) ^ 78060870 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 156121741) ^ 52040580 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 156121741) ^ 31224348 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 156121741) ^ 180 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_156924613 : Nat.Prime 156924613 := by
  apply lucas_primality 156924613 (2 : ZMod 156924613)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 2), (25793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 2), (25793, 1)] : List FactorBlock).map factorBlockValue).prod) = 156924613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_25793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 156924613) ^ 78462306 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 156924613) ^ 52308204 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 156924613) ^ 12071124 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 156924613) ^ 6084 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_161984281 : Nat.Prime 161984281 := by
  apply lucas_primality 161984281 (22 : ZMod 161984281)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (61, 1), (22129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (61, 1), (22129, 1)] : List FactorBlock).map factorBlockValue).prod) = 161984281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_61
      · exact prime_eightyBZ_22129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 161984281) ^ 80992140 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (22 : ZMod 161984281) ^ 53994760 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (22 : ZMod 161984281) ^ 32396856 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (22 : ZMod 161984281) ^ 2655480 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (22 : ZMod 161984281) ^ 7320 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_180550151 : Nat.Prime 180550151 := by
  apply lucas_primality 180550151 (11 : ZMod 180550151)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 3), (2713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 3), (2713, 1)] : List FactorBlock).map factorBlockValue).prod) = 180550151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_2713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 180550151) ^ 90275075 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 180550151) ^ 36110030 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 180550151) ^ 16413650 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 180550151) ^ 66550 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_192813637 : Nat.Prime 192813637 := by
  apply lucas_primality 192813637 (2 : ZMod 192813637)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (16067803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (16067803, 1)] : List FactorBlock).map factorBlockValue).prod) = 192813637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_16067803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 192813637) ^ 96406818 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 192813637) ^ 64271212 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 192813637) ^ 12 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_192906559 : Nat.Prime 192906559 := by
  apply lucas_primality 192906559 (6 : ZMod 192906559)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (41, 1), (20107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (41, 1), (20107, 1)] : List FactorBlock).map factorBlockValue).prod) = 192906559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_41
      · exact prime_eightyBZ_20107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 192906559) ^ 96453279 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 192906559) ^ 64302186 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 192906559) ^ 14838966 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 192906559) ^ 4705038 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 192906559) ^ 9594 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_203924807 : Nat.Prime 203924807 := by
  apply lucas_primality 203924807 (5 : ZMod 203924807)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101962403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101962403, 1)] : List FactorBlock).map factorBlockValue).prod) = 203924807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_101962403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 203924807) ^ 101962403 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 203924807) ^ 2 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_223188893 : Nat.Prime 223188893 := by
  apply lucas_primality 223188893 (2 : ZMod 223188893)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (137, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (137, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) = 223188893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_131
      · exact prime_eightyBZ_137
      · exact prime_eightyBZ_3109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 223188893) ^ 111594446 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 223188893) ^ 1703732 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 223188893) ^ 1629116 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 223188893) ^ 71788 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_227438557 : Nat.Prime 227438557 := by
  apply lucas_primality 227438557 (5 : ZMod 227438557)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (512249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (512249, 1)] : List FactorBlock).map factorBlockValue).prod) = 227438557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_37
      · exact prime_eightyBZ_512249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 227438557) ^ 113719278 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 227438557) ^ 75812852 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 227438557) ^ 6146988 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 227438557) ^ 444 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_232730557 : Nat.Prime 232730557 := by
  apply lucas_primality 232730557 (2 : ZMod 232730557)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19394213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19394213, 1)] : List FactorBlock).map factorBlockValue).prod) = 232730557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_19394213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 232730557) ^ 116365278 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 232730557) ^ 77576852 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 232730557) ^ 12 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_268629457 : Nat.Prime 268629457 := by
  apply lucas_primality 268629457 (10 : ZMod 268629457)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (739, 1), (7573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (739, 1), (7573, 1)] : List FactorBlock).map factorBlockValue).prod) = 268629457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_739
      · exact prime_eightyBZ_7573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 268629457) ^ 134314728 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 268629457) ^ 89543152 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 268629457) ^ 363504 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 268629457) ^ 35472 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_271114517 : Nat.Prime 271114517 := by
  apply lucas_primality 271114517 (2 : ZMod 271114517)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (431, 1), (157259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (431, 1), (157259, 1)] : List FactorBlock).map factorBlockValue).prod) = 271114517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_431
      · exact prime_eightyBZ_157259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 271114517) ^ 135557258 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271114517) ^ 629036 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271114517) ^ 1724 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_275698603 : Nat.Prime 275698603 := by
  apply lucas_primality 275698603 (2 : ZMod 275698603)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1019, 1), (15031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1019, 1), (15031, 1)] : List FactorBlock).map factorBlockValue).prod) = 275698603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_1019
      · exact prime_eightyBZ_15031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 275698603) ^ 137849301 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 275698603) ^ 91899534 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 275698603) ^ 270558 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 275698603) ^ 18342 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_295244297 : Nat.Prime 295244297 := by
  apply lucas_primality 295244297 (3 : ZMod 295244297)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (947, 1), (38971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (947, 1), (38971, 1)] : List FactorBlock).map factorBlockValue).prod) = 295244297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_947
      · exact prime_eightyBZ_38971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 295244297) ^ 147622148 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 295244297) ^ 311768 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 295244297) ^ 7576 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_317227987 : Nat.Prime 317227987 := by
  apply lucas_primality 317227987 (3 : ZMod 317227987)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17623777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17623777, 1)] : List FactorBlock).map factorBlockValue).prod) = 317227987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_17623777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 317227987) ^ 158613993 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 317227987) ^ 105742662 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 317227987) ^ 18 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_342618743 : Nat.Prime 342618743 := by
  apply lucas_primality 342618743 (5 : ZMod 342618743)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (4629983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (4629983, 1)] : List FactorBlock).map factorBlockValue).prod) = 342618743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_37
      · exact prime_eightyBZ_4629983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 342618743) ^ 171309371 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 342618743) ^ 9259966 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 342618743) ^ 74 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_347779889 : Nat.Prime 347779889 := by
  apply lucas_primality 347779889 (3 : ZMod 347779889)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3001, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3001, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod) = 347779889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3001
      · exact prime_eightyBZ_7243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 347779889) ^ 173889944 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 347779889) ^ 115888 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 347779889) ^ 48016 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_354182527 : Nat.Prime 354182527 := by
  apply lucas_primality 354182527 (3 : ZMod 354182527)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19676807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19676807, 1)] : List FactorBlock).map factorBlockValue).prod) = 354182527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_19676807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 354182527) ^ 177091263 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 354182527) ^ 118060842 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 354182527) ^ 18 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_377483969 : Nat.Prime 377483969 := by
  apply lucas_primality 377483969 (3 : ZMod 377483969)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (139, 1), (42433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (139, 1), (42433, 1)] : List FactorBlock).map factorBlockValue).prod) = 377483969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_139
      · exact prime_eightyBZ_42433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 377483969) ^ 188741984 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 377483969) ^ 2715712 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 377483969) ^ 8896 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_389325191 : Nat.Prime 389325191 := by
  apply lucas_primality 389325191 (17 : ZMod 389325191)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (197, 1), (229, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (197, 1), (229, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) = 389325191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_197
      · exact prime_eightyBZ_229
      · exact prime_eightyBZ_863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 389325191) ^ 194662595 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 389325191) ^ 77865038 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 389325191) ^ 1976270 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 389325191) ^ 1700110 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 389325191) ^ 451130 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_416487571 : Nat.Prime 416487571 := by
  apply lucas_primality 416487571 (2 : ZMod 416487571)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (991, 1), (14009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (991, 1), (14009, 1)] : List FactorBlock).map factorBlockValue).prod) = 416487571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_991
      · exact prime_eightyBZ_14009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 416487571) ^ 208243785 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 416487571) ^ 138829190 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 416487571) ^ 83297514 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 416487571) ^ 420270 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 416487571) ^ 29730 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_420533579 : Nat.Prime 420533579 := by
  apply lucas_primality 420533579 (2 : ZMod 420533579)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (311, 1), (676099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (311, 1), (676099, 1)] : List FactorBlock).map factorBlockValue).prod) = 420533579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_311
      · exact prime_eightyBZ_676099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 420533579) ^ 210266789 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 420533579) ^ 1352198 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 420533579) ^ 622 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_507670679 : Nat.Prime 507670679 := by
  apply lucas_primality 507670679 (29 : ZMod 507670679)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12479, 1), (20341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12479, 1), (20341, 1)] : List FactorBlock).map factorBlockValue).prod) = 507670679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_12479
      · exact prime_eightyBZ_20341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (29 : ZMod 507670679) ^ 253835339 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (29 : ZMod 507670679) ^ 40682 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (29 : ZMod 507670679) ^ 24958 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_560515261 : Nat.Prime 560515261 := by
  apply lucas_primality 560515261 (6 : ZMod 560515261)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2531, 1), (3691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2531, 1), (3691, 1)] : List FactorBlock).map factorBlockValue).prod) = 560515261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_2531
      · exact prime_eightyBZ_3691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 560515261) ^ 280257630 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 560515261) ^ 186838420 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 560515261) ^ 112103052 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 560515261) ^ 221460 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 560515261) ^ 151860 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_579391369 : Nat.Prime 579391369 := by
  apply lucas_primality 579391369 (22 : ZMod 579391369)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3209, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3209, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) = 579391369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_3209
      · exact prime_eightyBZ_7523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 579391369) ^ 289695684 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (22 : ZMod 579391369) ^ 193130456 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (22 : ZMod 579391369) ^ 180552 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (22 : ZMod 579391369) ^ 77016 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_580981039 : Nat.Prime 580981039 := by
  apply lucas_primality 580981039 (6 : ZMod 580981039)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (769, 1), (11447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (769, 1), (11447, 1)] : List FactorBlock).map factorBlockValue).prod) = 580981039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_769
      · exact prime_eightyBZ_11447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 580981039) ^ 290490519 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 580981039) ^ 193660346 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 580981039) ^ 52816458 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 580981039) ^ 755502 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 580981039) ^ 50754 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_655420769 : Nat.Prime 655420769 := by
  apply lucas_primality 655420769 (3 : ZMod 655420769)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2861, 1), (7159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2861, 1), (7159, 1)] : List FactorBlock).map factorBlockValue).prod) = 655420769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_2861
      · exact prime_eightyBZ_7159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 655420769) ^ 327710384 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 655420769) ^ 229088 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 655420769) ^ 91552 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_668214361 : Nat.Prime 668214361 := by
  apply lucas_primality 668214361 (7 : ZMod 668214361)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (11, 1), (18749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (11, 1), (18749, 1)] : List FactorBlock).map factorBlockValue).prod) = 668214361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_18749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 668214361) ^ 334107180 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 668214361) ^ 222738120 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 668214361) ^ 133642872 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 668214361) ^ 60746760 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 668214361) ^ 35640 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_679805311 : Nat.Prime 679805311 := by
  apply lucas_primality 679805311 (19 : ZMod 679805311)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (22660177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (22660177, 1)] : List FactorBlock).map factorBlockValue).prod) = 679805311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_22660177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 679805311) ^ 339902655 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 679805311) ^ 226601770 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 679805311) ^ 135961062 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 679805311) ^ 30 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_684123959 : Nat.Prime 684123959 := by
  apply lucas_primality 684123959 (7 : ZMod 684123959)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (48865997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (48865997, 1)] : List FactorBlock).map factorBlockValue).prod) = 684123959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_48865997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 684123959) ^ 342061979 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 684123959) ^ 97731994 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 684123959) ^ 14 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_693891581 : Nat.Prime 693891581 := by
  apply lucas_primality 693891581 (2 : ZMod 693891581)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (34694579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (34694579, 1)] : List FactorBlock).map factorBlockValue).prod) = 693891581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_34694579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 693891581) ^ 346945790 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 693891581) ^ 138778316 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 693891581) ^ 20 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_695559779 : Nat.Prime 695559779 := by
  apply lucas_primality 695559779 (2 : ZMod 695559779)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347779889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347779889, 1)] : List FactorBlock).map factorBlockValue).prod) = 695559779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_347779889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 695559779) ^ 347779889 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 695559779) ^ 2 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_719543443 : Nat.Prime 719543443 := by
  apply lucas_primality 719543443 (2 : ZMod 719543443)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (119923907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (119923907, 1)] : List FactorBlock).map factorBlockValue).prod) = 719543443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_119923907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 719543443) ^ 359771721 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 719543443) ^ 239847814 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 719543443) ^ 6 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_791195789 : Nat.Prime 791195789 := by
  apply lucas_primality 791195789 (2 : ZMod 791195789)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (227, 1), (709, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (227, 1), (709, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) = 791195789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_227
      · exact prime_eightyBZ_709
      · exact prime_eightyBZ_1229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 791195789) ^ 395597894 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 791195789) ^ 3485444 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 791195789) ^ 1115932 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 791195789) ^ 643772 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_865217959 : Nat.Prime 865217959 := by
  apply lucas_primality 865217959 (3 : ZMod 865217959)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (29, 1), (26591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (29, 1), (26591, 1)] : List FactorBlock).map factorBlockValue).prod) = 865217959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_17
      · exact prime_eightyBZ_29
      · exact prime_eightyBZ_26591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 865217959) ^ 432608979 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 865217959) ^ 288405986 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 865217959) ^ 78656178 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 865217959) ^ 50895174 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 865217959) ^ 29835102 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 865217959) ^ 32538 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_909754229 : Nat.Prime 909754229 := by
  apply lucas_primality 909754229 (2 : ZMod 909754229)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (227438557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (227438557, 1)] : List FactorBlock).map factorBlockValue).prod) = 909754229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_227438557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 909754229) ^ 454877114 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 909754229) ^ 4 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1039816121 : Nat.Prime 1039816121 := by
  apply lucas_primality 1039816121 (3 : ZMod 1039816121)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (163, 1), (22783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (163, 1), (22783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1039816121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_163
      · exact prime_eightyBZ_22783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1039816121) ^ 519908060 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1039816121) ^ 207963224 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1039816121) ^ 148545160 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1039816121) ^ 6379240 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1039816121) ^ 45640 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1091223437 : Nat.Prime 1091223437 := by
  apply lucas_primality 1091223437 (2 : ZMod 1091223437)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (373, 1), (23593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (373, 1), (23593, 1)] : List FactorBlock).map factorBlockValue).prod) = 1091223437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_31
      · exact prime_eightyBZ_373
      · exact prime_eightyBZ_23593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1091223437) ^ 545611718 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091223437) ^ 35200756 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091223437) ^ 2925532 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091223437) ^ 46252 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1129495957 : Nat.Prime 1129495957 := by
  apply lucas_primality 1129495957 (2 : ZMod 1129495957)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (94124663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (94124663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1129495957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_94124663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1129495957) ^ 564747978 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1129495957) ^ 376498652 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1129495957) ^ 12 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1225703393 : Nat.Prime 1225703393 := by
  apply lucas_primality 1225703393 (3 : ZMod 1225703393)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (38303231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (38303231, 1)] : List FactorBlock).map factorBlockValue).prod) = 1225703393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_38303231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1225703393) ^ 612851696 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1225703393) ^ 32 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1361936311 : Nat.Prime 1361936311 := by
  apply lucas_primality 1361936311 (3 : ZMod 1361936311)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (181, 1), (35831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (181, 1), (35831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1361936311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_181
      · exact prime_eightyBZ_35831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1361936311) ^ 680968155 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1361936311) ^ 453978770 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1361936311) ^ 272387262 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1361936311) ^ 194562330 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1361936311) ^ 7524510 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1361936311) ^ 38010 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1412604227 : Nat.Prime 1412604227 := by
  apply lucas_primality 1412604227 (2 : ZMod 1412604227)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (64209283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (64209283, 1)] : List FactorBlock).map factorBlockValue).prod) = 1412604227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_64209283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1412604227) ^ 706302113 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1412604227) ^ 128418566 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1412604227) ^ 22 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1474364357 : Nat.Prime 1474364357 := by
  apply lucas_primality 1474364357 (2 : ZMod 1474364357)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (73, 1), (265747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (73, 1), (265747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1474364357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_73
      · exact prime_eightyBZ_265747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1474364357) ^ 737182178 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1474364357) ^ 77598124 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1474364357) ^ 20196772 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1474364357) ^ 5548 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1557792077 : Nat.Prime 1557792077 := by
  apply lucas_primality 1557792077 (2 : ZMod 1557792077)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 2), (67, 1), (20113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 2), (67, 1), (20113, 1)] : List FactorBlock).map factorBlockValue).prod) = 1557792077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_17
      · exact prime_eightyBZ_67
      · exact prime_eightyBZ_20113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1557792077) ^ 778896038 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1557792077) ^ 91634828 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1557792077) ^ 23250628 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1557792077) ^ 77452 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1557966947 : Nat.Prime 1557966947 := by
  apply lucas_primality 1557966947 (2 : ZMod 1557966947)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (149, 1), (78031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (149, 1), (78031, 1)] : List FactorBlock).map factorBlockValue).prod) = 1557966947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_67
      · exact prime_eightyBZ_149
      · exact prime_eightyBZ_78031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1557966947) ^ 778983473 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1557966947) ^ 23253238 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1557966947) ^ 10456154 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1557966947) ^ 19966 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1582391579 : Nat.Prime 1582391579 := by
  apply lucas_primality 1582391579 (2 : ZMod 1582391579)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (791195789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (791195789, 1)] : List FactorBlock).map factorBlockValue).prod) = 1582391579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_791195789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1582391579) ^ 791195789 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1582391579) ^ 2 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1781614319 : Nat.Prime 1781614319 := by
  apply lucas_primality 1781614319 (7 : ZMod 1781614319)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (80982469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (80982469, 1)] : List FactorBlock).map factorBlockValue).prod) = 1781614319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_80982469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1781614319) ^ 890807159 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1781614319) ^ 161964938 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1781614319) ^ 22 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1978550867 : Nat.Prime 1978550867 := by
  apply lucas_primality 1978550867 (2 : ZMod 1978550867)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (643, 1), (1538531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (643, 1), (1538531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1978550867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_643
      · exact prime_eightyBZ_1538531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1978550867) ^ 989275433 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1978550867) ^ 3077062 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1978550867) ^ 1286 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2077286557 : Nat.Prime 2077286557 := by
  apply lucas_primality 2077286557 (2 : ZMod 2077286557)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7103, 1), (24371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7103, 1), (24371, 1)] : List FactorBlock).map factorBlockValue).prod) = 2077286557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7103
      · exact prime_eightyBZ_24371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2077286557) ^ 1038643278 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2077286557) ^ 692428852 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2077286557) ^ 292452 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2077286557) ^ 85236 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2304220469 : Nat.Prime 2304220469 := by
  apply lucas_primality 2304220469 (2 : ZMod 2304220469)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (52368647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (52368647, 1)] : List FactorBlock).map factorBlockValue).prod) = 2304220469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_52368647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2304220469) ^ 1152110234 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2304220469) ^ 209474588 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2304220469) ^ 44 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2321402401 : Nat.Prime 2321402401 := by
  apply lucas_primality 2321402401 (7 : ZMod 2321402401)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 2), (322417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 2), (322417, 1)] : List FactorBlock).map factorBlockValue).prod) = 2321402401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_322417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2321402401) ^ 1160701200 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2321402401) ^ 773800800 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2321402401) ^ 464280480 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2321402401) ^ 7200 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2361954377 : Nat.Prime 2361954377 := by
  apply lucas_primality 2361954377 (3 : ZMod 2361954377)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (295244297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (295244297, 1)] : List FactorBlock).map factorBlockValue).prod) = 2361954377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_295244297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2361954377) ^ 1180977188 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2361954377) ^ 8 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2369048809 : Nat.Prime 2369048809 := by
  apply lucas_primality 2369048809 (11 : ZMod 2369048809)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (14101481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (14101481, 1)] : List FactorBlock).map factorBlockValue).prod) = 2369048809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_14101481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2369048809) ^ 1184524404 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2369048809) ^ 789682936 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2369048809) ^ 338435544 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2369048809) ^ 168 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2623117033 : Nat.Prime 2623117033 := by
  apply lucas_primality 2623117033 (5 : ZMod 2623117033)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (36432181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (36432181, 1)] : List FactorBlock).map factorBlockValue).prod) = 2623117033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_36432181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2623117033) ^ 1311558516 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2623117033) ^ 874372344 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2623117033) ^ 72 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2795021797 : Nat.Prime 2795021797 := by
  apply lucas_primality 2795021797 (6 : ZMod 2795021797)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1549, 1), (21481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1549, 1), (21481, 1)] : List FactorBlock).map factorBlockValue).prod) = 2795021797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_1549
      · exact prime_eightyBZ_21481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2795021797) ^ 1397510898 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2795021797) ^ 931673932 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2795021797) ^ 399288828 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2795021797) ^ 1804404 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2795021797) ^ 130116 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2869108261 : Nat.Prime 2869108261 := by
  apply lucas_primality 2869108261 (2 : ZMod 2869108261)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (103, 1), (464257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (103, 1), (464257, 1)] : List FactorBlock).map factorBlockValue).prod) = 2869108261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_103
      · exact prime_eightyBZ_464257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2869108261) ^ 1434554130 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2869108261) ^ 956369420 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2869108261) ^ 573821652 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2869108261) ^ 27855420 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2869108261) ^ 6180 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3174964739 : Nat.Prime 3174964739 := by
  apply lucas_primality 3174964739 (2 : ZMod 3174964739)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 3), (1192699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 3), (1192699, 1)] : List FactorBlock).map factorBlockValue).prod) = 3174964739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_1192699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3174964739) ^ 1587482369 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3174964739) ^ 288633158 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3174964739) ^ 2662 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3358179247 : Nat.Prime 3358179247 := by
  apply lucas_primality 3358179247 (5 : ZMod 3358179247)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (1553, 1), (3499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (1553, 1), (3499, 1)] : List FactorBlock).map factorBlockValue).prod) = 3358179247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_103
      · exact prime_eightyBZ_1553
      · exact prime_eightyBZ_3499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3358179247) ^ 1679089623 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3358179247) ^ 1119393082 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3358179247) ^ 32603682 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3358179247) ^ 2162382 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3358179247) ^ 959754 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3494744291 : Nat.Prime 3494744291 := by
  apply lucas_primality 3494744291 (2 : ZMod 3494744291)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (61, 1), (301531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (61, 1), (301531, 1)] : List FactorBlock).map factorBlockValue).prod) = 3494744291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_61
      · exact prime_eightyBZ_301531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3494744291) ^ 1747372145 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3494744291) ^ 698948858 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3494744291) ^ 183933910 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3494744291) ^ 57290890 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3494744291) ^ 11590 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3660578063 : Nat.Prime 3660578063 := by
  apply lucas_primality 3660578063 (5 : ZMod 3660578063)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (12283819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (12283819, 1)] : List FactorBlock).map factorBlockValue).prod) = 3660578063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_149
      · exact prime_eightyBZ_12283819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3660578063) ^ 1830289031 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3660578063) ^ 24567638 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3660578063) ^ 298 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3662713273 : Nat.Prime 3662713273 := by
  apply lucas_primality 3662713273 (5 : ZMod 3662713273)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (152613053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (152613053, 1)] : List FactorBlock).map factorBlockValue).prod) = 3662713273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_152613053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3662713273) ^ 1831356636 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662713273) ^ 1220904424 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662713273) ^ 24 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3902359931 : Nat.Prime 3902359931 := by
  apply lucas_primality 3902359931 (2 : ZMod 3902359931)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1433, 1), (38903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1433, 1), (38903, 1)] : List FactorBlock).map factorBlockValue).prod) = 3902359931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_1433
      · exact prime_eightyBZ_38903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3902359931) ^ 1951179965 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3902359931) ^ 780471986 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3902359931) ^ 557479990 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3902359931) ^ 2723210 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3902359931) ^ 100310 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_4441724117 : Nat.Prime 4441724117 := by
  apply lucas_primality 4441724117 (2 : ZMod 4441724117)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (317, 1), (787, 1), (4451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (317, 1), (787, 1), (4451, 1)] : List FactorBlock).map factorBlockValue).prod) = 4441724117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_317
      · exact prime_eightyBZ_787
      · exact prime_eightyBZ_4451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4441724117) ^ 2220862058 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4441724117) ^ 14011748 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4441724117) ^ 5643868 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4441724117) ^ 997916 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_6375285487 : Nat.Prime 6375285487 := by
  apply lucas_primality 6375285487 (3 : ZMod 6375285487)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (354182527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (354182527, 1)] : List FactorBlock).map factorBlockValue).prod) = 6375285487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_354182527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6375285487) ^ 3187642743 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6375285487) ^ 2125095162 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6375285487) ^ 18 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_6547340623 : Nat.Prime 6547340623 := by
  apply lucas_primality 6547340623 (3 : ZMod 6547340623)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1091223437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1091223437, 1)] : List FactorBlock).map factorBlockValue).prod) = 6547340623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_1091223437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6547340623) ^ 3273670311 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6547340623) ^ 2182446874 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6547340623) ^ 6 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_6766843807 : Nat.Prime 6766843807 := by
  apply lucas_primality 6766843807 (5 : ZMod 6766843807)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (239, 1), (82787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (239, 1), (82787, 1)] : List FactorBlock).map factorBlockValue).prod) = 6766843807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_239
      · exact prime_eightyBZ_82787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6766843807) ^ 3383421903 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6766843807) ^ 2255614602 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6766843807) ^ 356149674 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6766843807) ^ 28313154 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6766843807) ^ 81738 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_7884100957 : Nat.Prime 7884100957 := by
  apply lucas_primality 7884100957 (2 : ZMod 7884100957)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (359, 1), (20563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (359, 1), (20563, 1)] : List FactorBlock).map factorBlockValue).prod) = 7884100957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_89
      · exact prime_eightyBZ_359
      · exact prime_eightyBZ_20563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7884100957) ^ 3942050478 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7884100957) ^ 2628033652 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7884100957) ^ 88585404 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7884100957) ^ 21961284 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7884100957) ^ 383412 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_8482100239 : Nat.Prime 8482100239 := by
  apply lucas_primality 8482100239 (3 : ZMod 8482100239)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (317, 1), (1486523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (317, 1), (1486523, 1)] : List FactorBlock).map factorBlockValue).prod) = 8482100239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_317
      · exact prime_eightyBZ_1486523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8482100239) ^ 4241050119 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8482100239) ^ 2827366746 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8482100239) ^ 26757414 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8482100239) ^ 5706 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_8546559743 : Nat.Prime 8546559743 := by
  apply lucas_primality 8546559743 (7 : ZMod 8546559743)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (127, 1), (208993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (127, 1), (208993, 1)] : List FactorBlock).map factorBlockValue).prod) = 8546559743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_23
      · exact prime_eightyBZ_127
      · exact prime_eightyBZ_208993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8546559743) ^ 4273279871 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8546559743) ^ 1220937106 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8546559743) ^ 371589554 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8546559743) ^ 67295746 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8546559743) ^ 40894 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_10201746409 : Nat.Prime 10201746409 := by
  apply lucas_primality 10201746409 (11 : ZMod 10201746409)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (251, 1), (241931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (251, 1), (241931, 1)] : List FactorBlock).map factorBlockValue).prod) = 10201746409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_251
      · exact prime_eightyBZ_241931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 10201746409) ^ 5100873204 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 10201746409) ^ 3400582136 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 10201746409) ^ 1457392344 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 10201746409) ^ 40644408 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 10201746409) ^ 42168 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_12123432133 : Nat.Prime 12123432133 := by
  apply lucas_primality 12123432133 (2 : ZMod 12123432133)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (109, 1), (1324097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (109, 1), (1324097, 1)] : List FactorBlock).map factorBlockValue).prod) = 12123432133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_109
      · exact prime_eightyBZ_1324097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12123432133) ^ 6061716066 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12123432133) ^ 4041144044 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12123432133) ^ 1731918876 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12123432133) ^ 111224148 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12123432133) ^ 9156 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_13559228219 : Nat.Prime 13559228219 := by
  apply lucas_primality 13559228219 (2 : ZMod 13559228219)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (80803, 1), (83903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (80803, 1), (83903, 1)] : List FactorBlock).map factorBlockValue).prod) = 13559228219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_80803
      · exact prime_eightyBZ_83903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13559228219) ^ 6779614109 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13559228219) ^ 167806 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13559228219) ^ 161606 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_16454835613 : Nat.Prime 16454835613 := by
  apply lucas_primality 16454835613 (5 : ZMod 16454835613)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (3803, 1), (40063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (3803, 1), (40063, 1)] : List FactorBlock).map factorBlockValue).prod) = 16454835613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_3803
      · exact prime_eightyBZ_40063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16454835613) ^ 8227417806 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 16454835613) ^ 5484945204 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 16454835613) ^ 4326804 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 16454835613) ^ 410724 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_17965509301 : Nat.Prime 17965509301 := by
  apply lucas_primality 17965509301 (2 : ZMod 17965509301)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (23, 1), (167, 1), (5197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (23, 1), (167, 1), (5197, 1)] : List FactorBlock).map factorBlockValue).prod) = 17965509301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_23
      · exact prime_eightyBZ_167
      · exact prime_eightyBZ_5197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17965509301) ^ 8982754650 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17965509301) ^ 5988503100 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17965509301) ^ 3593101860 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17965509301) ^ 781109100 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17965509301) ^ 107577900 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17965509301) ^ 3456900 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_18393763103 : Nat.Prime 18393763103 := by
  apply lucas_primality 18393763103 (5 : ZMod 18393763103)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (53, 1), (1213469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (53, 1), (1213469, 1)] : List FactorBlock).map factorBlockValue).prod) = 18393763103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_53
      · exact prime_eightyBZ_1213469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18393763103) ^ 9196881551 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 18393763103) ^ 1672160282 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 18393763103) ^ 1414904854 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 18393763103) ^ 347052134 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 18393763103) ^ 15158 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_18809131609 : Nat.Prime 18809131609 := by
  apply lucas_primality 18809131609 (13 : ZMod 18809131609)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (87079313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (87079313, 1)] : List FactorBlock).map factorBlockValue).prod) = 18809131609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_87079313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 18809131609) ^ 9404565804 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 18809131609) ^ 6269710536 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 18809131609) ^ 216 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_21624458147 : Nat.Prime 21624458147 := by
  apply lucas_primality 21624458147 (2 : ZMod 21624458147)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (101, 1), (3453283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (101, 1), (3453283, 1)] : List FactorBlock).map factorBlockValue).prod) = 21624458147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_31
      · exact prime_eightyBZ_101
      · exact prime_eightyBZ_3453283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21624458147) ^ 10812229073 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21624458147) ^ 697563166 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21624458147) ^ 214103546 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21624458147) ^ 6262 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_23572321933 : Nat.Prime 23572321933 := by
  apply lucas_primality 23572321933 (2 : ZMod 23572321933)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1471, 1), (1335391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1471, 1), (1335391, 1)] : List FactorBlock).map factorBlockValue).prod) = 23572321933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_1471
      · exact prime_eightyBZ_1335391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23572321933) ^ 11786160966 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23572321933) ^ 7857440644 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23572321933) ^ 16024692 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23572321933) ^ 17652 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_28691082611 : Nat.Prime 28691082611 := by
  apply lucas_primality 28691082611 (2 : ZMod 28691082611)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2869108261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2869108261, 1)] : List FactorBlock).map factorBlockValue).prod) = 28691082611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_2869108261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28691082611) ^ 14345541305 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 28691082611) ^ 5738216522 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 28691082611) ^ 10 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_29732046577 : Nat.Prime 29732046577 := by
  apply lucas_primality 29732046577 (5 : ZMod 29732046577)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (15541, 1), (39857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (15541, 1), (39857, 1)] : List FactorBlock).map factorBlockValue).prod) = 29732046577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_15541
      · exact prime_eightyBZ_39857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29732046577) ^ 14866023288 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 29732046577) ^ 9910682192 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 29732046577) ^ 1913136 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 29732046577) ^ 745968 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_30844194737 : Nat.Prime 30844194737 := by
  apply lucas_primality 30844194737 (3 : ZMod 30844194737)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (8929, 1), (215899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (8929, 1), (215899, 1)] : List FactorBlock).map factorBlockValue).prod) = 30844194737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_8929
      · exact prime_eightyBZ_215899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30844194737) ^ 15422097368 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 30844194737) ^ 3454384 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 30844194737) ^ 142864 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_32429807437 : Nat.Prime 32429807437 := by
  apply lucas_primality 32429807437 (5 : ZMod 32429807437)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (1877, 1), (110753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (1877, 1), (110753, 1)] : List FactorBlock).map factorBlockValue).prod) = 32429807437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_1877
      · exact prime_eightyBZ_110753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 32429807437) ^ 16214903718 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 32429807437) ^ 10809935812 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 32429807437) ^ 2494600572 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 32429807437) ^ 17277468 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 32429807437) ^ 292812 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_34960016279 : Nat.Prime 34960016279 := by
  apply lucas_primality 34960016279 (11 : ZMod 34960016279)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (6329, 1), (251081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (6329, 1), (251081, 1)] : List FactorBlock).map factorBlockValue).prod) = 34960016279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_6329
      · exact prime_eightyBZ_251081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 34960016279) ^ 17480008139 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 34960016279) ^ 3178183298 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 34960016279) ^ 5523782 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 34960016279) ^ 139238 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_36200983279 : Nat.Prime 36200983279 := by
  apply lucas_primality 36200983279 (6 : ZMod 36200983279)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (941, 1), (6411793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (941, 1), (6411793, 1)] : List FactorBlock).map factorBlockValue).prod) = 36200983279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_941
      · exact prime_eightyBZ_6411793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 36200983279) ^ 18100491639 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 36200983279) ^ 12066994426 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 36200983279) ^ 38470758 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 36200983279) ^ 5646 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_43683304781 : Nat.Prime 43683304781 := by
  apply lucas_primality 43683304781 (2 : ZMod 43683304781)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (5233, 1), (417383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (5233, 1), (417383, 1)] : List FactorBlock).map factorBlockValue).prod) = 43683304781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_5233
      · exact prime_eightyBZ_417383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43683304781) ^ 21841652390 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 43683304781) ^ 8736660956 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 43683304781) ^ 8347660 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 43683304781) ^ 104660 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_44017175651 : Nat.Prime 44017175651 := by
  apply lucas_primality 44017175651 (2 : ZMod 44017175651)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (41, 1), (557, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (41, 1), (557, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) = 44017175651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_41
      · exact prime_eightyBZ_557
      · exact prime_eightyBZ_5507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44017175651) ^ 22008587825 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 44017175651) ^ 8803435130 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 44017175651) ^ 6288167950 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 44017175651) ^ 1073589650 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 44017175651) ^ 79025450 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 44017175651) ^ 7992950 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_47239087541 : Nat.Prime 47239087541 := by
  apply lucas_primality 47239087541 (3 : ZMod 47239087541)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2361954377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2361954377, 1)] : List FactorBlock).map factorBlockValue).prod) = 47239087541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_2361954377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47239087541) ^ 23619543770 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 47239087541) ^ 9447817508 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 47239087541) ^ 20 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_47940828007 : Nat.Prime 47940828007 := by
  apply lucas_primality 47940828007 (13 : ZMod 47940828007)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (420533579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (420533579, 1)] : List FactorBlock).map factorBlockValue).prod) = 47940828007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_420533579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 47940828007) ^ 23970414003 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 47940828007) ^ 15980276002 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 47940828007) ^ 2523201474 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 47940828007) ^ 114 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_54319187927 : Nat.Prime 54319187927 := by
  apply lucas_primality 54319187927 (5 : ZMod 54319187927)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (2887, 1), (41081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (2887, 1), (41081, 1)] : List FactorBlock).map factorBlockValue).prod) = 54319187927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_229
      · exact prime_eightyBZ_2887
      · exact prime_eightyBZ_41081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 54319187927) ^ 27159593963 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 54319187927) ^ 237201694 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 54319187927) ^ 18815098 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 54319187927) ^ 1322246 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_56230438727 : Nat.Prime 56230438727 := by
  apply lucas_primality 56230438727 (7 : ZMod 56230438727)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (113, 1), (461609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (113, 1), (461609, 1)] : List FactorBlock).map factorBlockValue).prod) = 56230438727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_113
      · exact prime_eightyBZ_461609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 56230438727) ^ 28115219363 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 56230438727) ^ 8032919818 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 56230438727) ^ 5111858066 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 56230438727) ^ 497614502 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 56230438727) ^ 121814 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_58580682269 : Nat.Prime 58580682269 := by
  apply lucas_primality 58580682269 (2 : ZMod 58580682269)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (109, 1), (409, 1), (10597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (109, 1), (409, 1), (10597, 1)] : List FactorBlock).map factorBlockValue).prod) = 58580682269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_31
      · exact prime_eightyBZ_109
      · exact prime_eightyBZ_409
      · exact prime_eightyBZ_10597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58580682269) ^ 29290341134 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 58580682269) ^ 1889699428 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 58580682269) ^ 537437452 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 58580682269) ^ 143229052 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 58580682269) ^ 5528044 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_60555515407 : Nat.Prime 60555515407 := by
  apply lucas_primality 60555515407 (3 : ZMod 60555515407)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22679, 1), (445019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22679, 1), (445019, 1)] : List FactorBlock).map factorBlockValue).prod) = 60555515407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_22679
      · exact prime_eightyBZ_445019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 60555515407) ^ 30277757703 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 60555515407) ^ 20185171802 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 60555515407) ^ 2670114 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 60555515407) ^ 136074 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_67026127979 : Nat.Prime 67026127979 := by
  apply lucas_primality 67026127979 (2 : ZMod 67026127979)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (269, 1), (124583881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (269, 1), (124583881, 1)] : List FactorBlock).map factorBlockValue).prod) = 67026127979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_269
      · exact prime_eightyBZ_124583881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 67026127979) ^ 33513063989 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 67026127979) ^ 249167762 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 67026127979) ^ 538 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_76139180393 : Nat.Prime 76139180393 := by
  apply lucas_primality 76139180393 (3 : ZMod 76139180393)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (865217959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (865217959, 1)] : List FactorBlock).map factorBlockValue).prod) = 76139180393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_865217959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 76139180393) ^ 38069590196 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 76139180393) ^ 6921743672 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 76139180393) ^ 88 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_83663498251 : Nat.Prime 83663498251 := by
  apply lucas_primality 83663498251 (7 : ZMod 83663498251)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (17, 1), (43, 1), (50867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (17, 1), (43, 1), (50867, 1)] : List FactorBlock).map factorBlockValue).prod) = 83663498251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_17
      · exact prime_eightyBZ_43
      · exact prime_eightyBZ_50867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 83663498251) ^ 41831749125 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 83663498251) ^ 27887832750 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 83663498251) ^ 16732699650 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 83663498251) ^ 4921382250 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 83663498251) ^ 1945662750 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 83663498251) ^ 1644750 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_87366609563 : Nat.Prime 87366609563 := by
  apply lucas_primality 87366609563 (2 : ZMod 87366609563)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43683304781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43683304781, 1)] : List FactorBlock).map factorBlockValue).prod) = 87366609563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_43683304781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 87366609563) ^ 43683304781 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 87366609563) ^ 2 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_88620975439 : Nat.Prime 88620975439 := by
  apply lucas_primality 88620975439 (3 : ZMod 88620975439)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2311, 1), (6391243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2311, 1), (6391243, 1)] : List FactorBlock).map factorBlockValue).prod) = 88620975439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_2311
      · exact prime_eightyBZ_6391243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 88620975439) ^ 44310487719 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 88620975439) ^ 29540325146 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 88620975439) ^ 38347458 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 88620975439) ^ 13866 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_94478175083 : Nat.Prime 94478175083 := by
  apply lucas_primality 94478175083 (2 : ZMod 94478175083)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47239087541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47239087541, 1)] : List FactorBlock).map factorBlockValue).prod) = 94478175083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_47239087541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 94478175083) ^ 47239087541 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 94478175083) ^ 2 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_98729013679 : Nat.Prime 98729013679 := by
  apply lucas_primality 98729013679 (3 : ZMod 98729013679)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (16454835613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (16454835613, 1)] : List FactorBlock).map factorBlockValue).prod) = 98729013679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_16454835613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 98729013679) ^ 49364506839 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 98729013679) ^ 32909671226 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 98729013679) ^ 6 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_118581073693 : Nat.Prime 118581073693 := by
  apply lucas_primality 118581073693 (19 : ZMod 118581073693)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (257, 1), (2261789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (257, 1), (2261789, 1)] : List FactorBlock).map factorBlockValue).prod) = 118581073693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_17
      · exact prime_eightyBZ_257
      · exact prime_eightyBZ_2261789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 118581073693) ^ 59290536846 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 118581073693) ^ 39527024564 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 118581073693) ^ 6975357276 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 118581073693) ^ 461404956 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 118581073693) ^ 52428 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_144070455349 : Nat.Prime 144070455349 := by
  apply lucas_primality 144070455349 (13 : ZMod 144070455349)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11243, 1), (355951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11243, 1), (355951, 1)] : List FactorBlock).map factorBlockValue).prod) = 144070455349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11243
      · exact prime_eightyBZ_355951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 144070455349) ^ 72035227674 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 144070455349) ^ 48023485116 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 144070455349) ^ 12814236 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 144070455349) ^ 404748 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_159930560753 : Nat.Prime 159930560753 := by
  apply lucas_primality 159930560753 (3 : ZMod 159930560753)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1381, 1), (7237987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1381, 1), (7237987, 1)] : List FactorBlock).map factorBlockValue).prod) = 159930560753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_1381
      · exact prime_eightyBZ_7237987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 159930560753) ^ 79965280376 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 159930560753) ^ 115807792 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 159930560753) ^ 22096 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_175568600093 : Nat.Prime 175568600093 := by
  apply lucas_primality 175568600093 (2 : ZMod 175568600093)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (719543443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (719543443, 1)] : List FactorBlock).map factorBlockValue).prod) = 175568600093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_61
      · exact prime_eightyBZ_719543443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 175568600093) ^ 87784300046 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 175568600093) ^ 2878173772 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 175568600093) ^ 244 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_208029350513 : Nat.Prime 208029350513 := by
  apply lucas_primality 208029350513 (3 : ZMod 208029350513)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (337, 1), (38581111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (337, 1), (38581111, 1)] : List FactorBlock).map factorBlockValue).prod) = 208029350513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_337
      · exact prime_eightyBZ_38581111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 208029350513) ^ 104014675256 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 208029350513) ^ 617297776 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 208029350513) ^ 5392 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_273990374299 : Nat.Prime 273990374299 := by
  apply lucas_primality 273990374299 (2 : ZMod 273990374299)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (97, 1), (156924613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (97, 1), (156924613, 1)] : List FactorBlock).map factorBlockValue).prod) = 273990374299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_97
      · exact prime_eightyBZ_156924613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 273990374299) ^ 136995187149 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 273990374299) ^ 91330124766 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 273990374299) ^ 2824643034 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 273990374299) ^ 1746 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_319861121507 : Nat.Prime 319861121507 := by
  apply lucas_primality 319861121507 (2 : ZMod 319861121507)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (159930560753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (159930560753, 1)] : List FactorBlock).map factorBlockValue).prod) = 319861121507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_159930560753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 319861121507) ^ 159930560753 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 319861121507) ^ 2 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_397279853483 : Nat.Prime 397279853483 := by
  apply lucas_primality 397279853483 (2 : ZMod 397279853483)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (109, 1), (107199097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (109, 1), (107199097, 1)] : List FactorBlock).map factorBlockValue).prod) = 397279853483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_17
      · exact prime_eightyBZ_109
      · exact prime_eightyBZ_107199097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 397279853483) ^ 198639926741 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 397279853483) ^ 23369403146 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 397279853483) ^ 3644769298 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 397279853483) ^ 3706 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_451029527651 : Nat.Prime 451029527651 := by
  apply lucas_primality 451029527651 (2 : ZMod 451029527651)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (693891581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (693891581, 1)] : List FactorBlock).map factorBlockValue).prod) = 451029527651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_693891581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 451029527651) ^ 225514763825 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 451029527651) ^ 90205905530 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 451029527651) ^ 34694579050 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 451029527651) ^ 650 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_907365468469 : Nat.Prime 907365468469 := by
  apply lucas_primality 907365468469 (2 : ZMod 907365468469)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11069, 1), (6831131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11069, 1), (6831131, 1)] : List FactorBlock).map factorBlockValue).prod) = 907365468469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11069
      · exact prime_eightyBZ_6831131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 907365468469) ^ 453682734234 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 907365468469) ^ 302455156156 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 907365468469) ^ 81973572 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 907365468469) ^ 132828 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_923779375711 : Nat.Prime 923779375711 := by
  apply lucas_primality 923779375711 (6 : ZMod 923779375711)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (151, 1), (203924807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (151, 1), (203924807, 1)] : List FactorBlock).map factorBlockValue).prod) = 923779375711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_151
      · exact prime_eightyBZ_203924807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 923779375711) ^ 461889687855 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 923779375711) ^ 307926458570 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 923779375711) ^ 184755875142 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 923779375711) ^ 6117744210 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 923779375711) ^ 4530 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_933203765203 : Nat.Prime 933203765203 := by
  apply lucas_primality 933203765203 (2 : ZMod 933203765203)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (2321402401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (2321402401, 1)] : List FactorBlock).map factorBlockValue).prod) = 933203765203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_67
      · exact prime_eightyBZ_2321402401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 933203765203) ^ 466601882601 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 933203765203) ^ 311067921734 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 933203765203) ^ 13928414406 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 933203765203) ^ 402 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1023429085489 : Nat.Prime 1023429085489 := by
  apply lucas_primality 1023429085489 (19 : ZMod 1023429085489)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (2369048809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (2369048809, 1)] : List FactorBlock).map factorBlockValue).prod) = 1023429085489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_2369048809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 1023429085489) ^ 511714542744 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 1023429085489) ^ 341143028496 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 1023429085489) ^ 432 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1080288773383 : Nat.Prime 1080288773383 := by
  apply lucas_primality 1080288773383 (3 : ZMod 1080288773383)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (1978550867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (1978550867, 1)] : List FactorBlock).map factorBlockValue).prod) = 1080288773383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_1978550867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1080288773383) ^ 540144386691 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1080288773383) ^ 360096257794 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1080288773383) ^ 154326967626 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1080288773383) ^ 83099136414 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1080288773383) ^ 546 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1143280544069 : Nat.Prime 1143280544069 := by
  apply lucas_primality 1143280544069 (2 : ZMod 1143280544069)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (37, 1), (73, 1), (8140009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (37, 1), (73, 1), (8140009, 1)] : List FactorBlock).map factorBlockValue).prod) = 1143280544069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_37
      · exact prime_eightyBZ_73
      · exact prime_eightyBZ_8140009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1143280544069) ^ 571640272034 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1143280544069) ^ 87944657236 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1143280544069) ^ 30899474164 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1143280544069) ^ 15661377316 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1143280544069) ^ 140452 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1165407121201 : Nat.Prime 1165407121201 := by
  apply lucas_primality 1165407121201 (13 : ZMod 1165407121201)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (7, 3), (2831407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (7, 3), (2831407, 1)] : List FactorBlock).map factorBlockValue).prod) = 1165407121201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_2831407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1165407121201) ^ 582703560600 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 1165407121201) ^ 388469040400 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 1165407121201) ^ 233081424240 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 1165407121201) ^ 166486731600 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 1165407121201) ^ 411600 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1190895132983 : Nat.Prime 1190895132983 := by
  apply lucas_primality 1190895132983 (5 : ZMod 1190895132983)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (227, 1), (2623117033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (227, 1), (2623117033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1190895132983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_227
      · exact prime_eightyBZ_2623117033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1190895132983) ^ 595447566491 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1190895132983) ^ 5246234066 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1190895132983) ^ 454 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1269391755367 : Nat.Prime 1269391755367 := by
  apply lucas_primality 1269391755367 (3 : ZMod 1269391755367)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (3358179247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (3358179247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1269391755367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_3358179247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1269391755367) ^ 634695877683 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269391755367) ^ 423130585122 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269391755367) ^ 181341679338 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269391755367) ^ 378 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1367674142543 : Nat.Prime 1367674142543 := by
  apply lucas_primality 1367674142543 (5 : ZMod 1367674142543)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (29732046577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (29732046577, 1)] : List FactorBlock).map factorBlockValue).prod) = 1367674142543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_23
      · exact prime_eightyBZ_29732046577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1367674142543) ^ 683837071271 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1367674142543) ^ 59464093154 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1367674142543) ^ 46 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1549216026067 : Nat.Prime 1549216026067 := by
  apply lucas_primality 1549216026067 (2 : ZMod 1549216026067)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (919, 1), (12611, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (919, 1), (12611, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1549216026067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_919
      · exact prime_eightyBZ_12611
      · exact prime_eightyBZ_22279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1549216026067) ^ 774608013033 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1549216026067) ^ 516405342022 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1549216026067) ^ 1685762814 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1549216026067) ^ 122846406 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1549216026067) ^ 69537054 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1625821997617 : Nat.Prime 1625821997617 := by
  apply lucas_primality 1625821997617 (5 : ZMod 1625821997617)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (29, 1), (389325191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (29, 1), (389325191, 1)] : List FactorBlock).map factorBlockValue).prod) = 1625821997617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_29
      · exact prime_eightyBZ_389325191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1625821997617) ^ 812910998808 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1625821997617) ^ 541940665872 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1625821997617) ^ 56062827504 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1625821997617) ^ 4176 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1663082994697 : Nat.Prime 1663082994697 := by
  apply lucas_primality 1663082994697 (5 : ZMod 1663082994697)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (1474364357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (1474364357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1663082994697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_47
      · exact prime_eightyBZ_1474364357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1663082994697) ^ 831541497348 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663082994697) ^ 554360998232 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663082994697) ^ 35384744568 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663082994697) ^ 1128 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1963490640409 : Nat.Prime 1963490640409 := by
  apply lucas_primality 1963490640409 (23 : ZMod 1963490640409)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (227, 1), (311, 1), (35117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (227, 1), (311, 1), (35117, 1)] : List FactorBlock).map factorBlockValue).prod) = 1963490640409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_227
      · exact prime_eightyBZ_311
      · exact prime_eightyBZ_35117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1963490640409) ^ 981745320204 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1963490640409) ^ 654496880136 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1963490640409) ^ 178499149128 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1963490640409) ^ 8649738504 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1963490640409) ^ 6313474728 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1963490640409) ^ 55912824 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2115243571421 : Nat.Prime 2115243571421 := by
  apply lucas_primality 2115243571421 (2 : ZMod 2115243571421)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (41, 1), (149, 1), (2473217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (41, 1), (149, 1), (2473217, 1)] : List FactorBlock).map factorBlockValue).prod) = 2115243571421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_41
      · exact prime_eightyBZ_149
      · exact prime_eightyBZ_2473217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2115243571421) ^ 1057621785710 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115243571421) ^ 423048714284 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115243571421) ^ 302177653060 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115243571421) ^ 51591306620 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115243571421) ^ 14196265580 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115243571421) ^ 855260 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2931402378973 : Nat.Prime 2931402378973 := by
  apply lucas_primality 2931402378973 (2 : ZMod 2931402378973)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (139, 1), (11699, 1), (150221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (139, 1), (11699, 1), (150221, 1)] : List FactorBlock).map factorBlockValue).prod) = 2931402378973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_139
      · exact prime_eightyBZ_11699
      · exact prime_eightyBZ_150221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2931402378973) ^ 1465701189486 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2931402378973) ^ 977134126324 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2931402378973) ^ 21089225748 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2931402378973) ^ 250568628 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2931402378973) ^ 19513932 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3192365740457 : Nat.Prime 3192365740457 := by
  apply lucas_primality 3192365740457 (3 : ZMod 3192365740457)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (587, 1), (679805311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (587, 1), (679805311, 1)] : List FactorBlock).map factorBlockValue).prod) = 3192365740457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_587
      · exact prime_eightyBZ_679805311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3192365740457) ^ 1596182870228 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3192365740457) ^ 5438442488 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3192365740457) ^ 4696 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3909706194133 : Nat.Prime 3909706194133 := by
  apply lucas_primality 3909706194133 (6 : ZMod 3909706194133)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (36200983279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (36200983279, 1)] : List FactorBlock).map factorBlockValue).prod) = 3909706194133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_36200983279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 3909706194133) ^ 1954853097066 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3909706194133) ^ 1303235398044 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3909706194133) ^ 108 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_4514191586161 : Nat.Prime 4514191586161 := by
  apply lucas_primality 4514191586161 (21 : ZMod 4514191586161)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (18809131609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (18809131609, 1)] : List FactorBlock).map factorBlockValue).prod) = 4514191586161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_18809131609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 4514191586161) ^ 2257095793080 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (21 : ZMod 4514191586161) ^ 1504730528720 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (21 : ZMod 4514191586161) ^ 902838317232 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (21 : ZMod 4514191586161) ^ 240 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_4801316108207 : Nat.Prime 4801316108207 := by
  apply lucas_primality 4801316108207 (5 : ZMod 4801316108207)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20029, 1), (119859107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20029, 1), (119859107, 1)] : List FactorBlock).map factorBlockValue).prod) = 4801316108207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_20029
      · exact prime_eightyBZ_119859107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4801316108207) ^ 2400658054103 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 4801316108207) ^ 239718214 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 4801316108207) ^ 40058 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_5127913575461 : Nat.Prime 5127913575461 := by
  apply lucas_primality 5127913575461 (2 : ZMod 5127913575461)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (1093, 1), (18044597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (1093, 1), (18044597, 1)] : List FactorBlock).map factorBlockValue).prod) = 5127913575461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_1093
      · exact prime_eightyBZ_18044597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5127913575461) ^ 2563956787730 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5127913575461) ^ 1025582715092 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5127913575461) ^ 394454890420 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5127913575461) ^ 4691595220 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5127913575461) ^ 284180 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_5577704653919 : Nat.Prime 5577704653919 := by
  apply lucas_primality 5577704653919 (19 : ZMod 5577704653919)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (41681, 1), (2158369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (41681, 1), (2158369, 1)] : List FactorBlock).map factorBlockValue).prod) = 5577704653919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_31
      · exact prime_eightyBZ_41681
      · exact prime_eightyBZ_2158369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 5577704653919) ^ 2788852326959 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 5577704653919) ^ 179925956578 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 5577704653919) ^ 133818878 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 5577704653919) ^ 2584222 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_5726282793383 : Nat.Prime 5726282793383 := by
  apply lucas_primality 5726282793383 (5 : ZMod 5726282793383)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (98729013679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (98729013679, 1)] : List FactorBlock).map factorBlockValue).prod) = 5726282793383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_29
      · exact prime_eightyBZ_98729013679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5726282793383) ^ 2863141396691 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5726282793383) ^ 197458027358 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5726282793383) ^ 58 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_6277890549923 : Nat.Prime 6277890549923 := by
  apply lucas_primality 6277890549923 (2 : ZMod 6277890549923)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (857, 1), (3662713273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (857, 1), (3662713273, 1)] : List FactorBlock).map factorBlockValue).prod) = 6277890549923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_857
      · exact prime_eightyBZ_3662713273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6277890549923) ^ 3138945274961 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6277890549923) ^ 7325426546 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6277890549923) ^ 1714 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_6910622146559 : Nat.Prime 6910622146559 := by
  apply lucas_primality 6910622146559 (17 : ZMod 6910622146559)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (1013, 1), (13809589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (1013, 1), (13809589, 1)] : List FactorBlock).map factorBlockValue).prod) = 6910622146559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_1013
      · exact prime_eightyBZ_13809589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 6910622146559) ^ 3455311073279 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 6910622146559) ^ 531586318966 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 6910622146559) ^ 363716955082 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 6910622146559) ^ 6821936966 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 6910622146559) ^ 500422 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_7085035279603 : Nat.Prime 7085035279603 := by
  apply lucas_primality 7085035279603 (2 : ZMod 7085035279603)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (56230438727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (56230438727, 1)] : List FactorBlock).map factorBlockValue).prod) = 7085035279603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_56230438727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7085035279603) ^ 3542517639801 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7085035279603) ^ 2361678426534 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7085035279603) ^ 1012147897086 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7085035279603) ^ 126 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_7123776276073 : Nat.Prime 7123776276073 := by
  apply lucas_primality 7123776276073 (10 : ZMod 7123776276073)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (269, 1), (701, 1), (50777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (269, 1), (701, 1), (50777, 1)] : List FactorBlock).map factorBlockValue).prod) = 7123776276073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_31
      · exact prime_eightyBZ_269
      · exact prime_eightyBZ_701
      · exact prime_eightyBZ_50777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 7123776276073) ^ 3561888138036 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 7123776276073) ^ 2374592092024 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 7123776276073) ^ 229799234712 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 7123776276073) ^ 26482439688 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 7123776276073) ^ 10162305672 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 7123776276073) ^ 140295336 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_8080447132403 : Nat.Prime 8080447132403 := by
  apply lucas_primality 8080447132403 (2 : ZMod 8080447132403)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (9787, 1), (1802687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (9787, 1), (1802687, 1)] : List FactorBlock).map factorBlockValue).prod) = 8080447132403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_229
      · exact prime_eightyBZ_9787
      · exact prime_eightyBZ_1802687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8080447132403) ^ 4040223566201 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8080447132403) ^ 35285795338 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8080447132403) ^ 825630646 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8080447132403) ^ 4482446 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_10872492252119 : Nat.Prime 10872492252119 := by
  apply lucas_primality 10872492252119 (7 : ZMod 10872492252119)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (19, 1), (43, 1), (7507, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (19, 1), (43, 1), (7507, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod) = 10872492252119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_43
      · exact prime_eightyBZ_7507
      · exact prime_eightyBZ_18089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10872492252119) ^ 5436246126059 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 10872492252119) ^ 1553213178874 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 10872492252119) ^ 572236434322 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 10872492252119) ^ 252848657026 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 10872492252119) ^ 1448313874 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 10872492252119) ^ 601055462 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_11057960359031 : Nat.Prime 11057960359031 := by
  apply lucas_primality 11057960359031 (17 : ZMod 11057960359031)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (101, 1), (3821, 1), (220411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (101, 1), (3821, 1), (220411, 1)] : List FactorBlock).map factorBlockValue).prod) = 11057960359031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_101
      · exact prime_eightyBZ_3821
      · exact prime_eightyBZ_220411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 11057960359031) ^ 5528980179515 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 11057960359031) ^ 2211592071806 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 11057960359031) ^ 850612335310 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 11057960359031) ^ 109484756030 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 11057960359031) ^ 2893996430 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 11057960359031) ^ 50169730 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_11452565586767 : Nat.Prime 11452565586767 := by
  apply lucas_primality 11452565586767 (5 : ZMod 11452565586767)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5726282793383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5726282793383, 1)] : List FactorBlock).map factorBlockValue).prod) = 11452565586767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5726282793383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 11452565586767) ^ 5726282793383 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11452565586767) ^ 2 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_13362520230043 : Nat.Prime 13362520230043 := by
  apply lucas_primality 13362520230043 (3 : ZMod 13362520230043)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (54319187927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (54319187927, 1)] : List FactorBlock).map factorBlockValue).prod) = 13362520230043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_41
      · exact prime_eightyBZ_54319187927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13362520230043) ^ 6681260115021 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13362520230043) ^ 4454173410014 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13362520230043) ^ 325915127562 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13362520230043) ^ 246 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_13382764233413 : Nat.Prime 13382764233413 := by
  apply lucas_primality 13382764233413 (2 : ZMod 13382764233413)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (73, 1), (6547340623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (73, 1), (6547340623, 1)] : List FactorBlock).map factorBlockValue).prod) = 13382764233413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_73
      · exact prime_eightyBZ_6547340623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13382764233413) ^ 6691382116706 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13382764233413) ^ 1911823461916 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13382764233413) ^ 183325537444 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13382764233413) ^ 2044 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_13741723906081 : Nat.Prime 13741723906081 := by
  apply lucas_primality 13741723906081 (11 : ZMod 13741723906081)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (43, 1), (113, 1), (151, 1), (39019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (43, 1), (113, 1), (151, 1), (39019, 1)] : List FactorBlock).map factorBlockValue).prod) = 13741723906081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_43
      · exact prime_eightyBZ_113
      · exact prime_eightyBZ_151
      · exact prime_eightyBZ_39019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 13741723906081) ^ 6870861953040 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 13741723906081) ^ 4580574635360 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 13741723906081) ^ 2748344781216 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 13741723906081) ^ 319574974560 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 13741723906081) ^ 121608176160 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 13741723906081) ^ 91004794080 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 13741723906081) ^ 352180320 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_14744801315017 : Nat.Prime 14744801315017 := by
  apply lucas_primality 14744801315017 (10 : ZMod 14744801315017)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 6), (179, 1), (659, 1), (21433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 6), (179, 1), (659, 1), (21433, 1)] : List FactorBlock).map factorBlockValue).prod) = 14744801315017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_179
      · exact prime_eightyBZ_659
      · exact prime_eightyBZ_21433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 14744801315017) ^ 7372400657508 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 14744801315017) ^ 4914933771672 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 14744801315017) ^ 82373191704 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 14744801315017) ^ 22374508824 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 14744801315017) ^ 687948552 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_15481717209131 : Nat.Prime 15481717209131 := by
  apply lucas_primality 15481717209131 (10 : ZMod 15481717209131)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (443, 1), (3494744291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (443, 1), (3494744291, 1)] : List FactorBlock).map factorBlockValue).prod) = 15481717209131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_443
      · exact prime_eightyBZ_3494744291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 15481717209131) ^ 7740858604565 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 15481717209131) ^ 3096343441826 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 15481717209131) ^ 34947442910 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 15481717209131) ^ 4430 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_19331034977251 : Nat.Prime 19331034977251 := by
  apply lucas_primality 19331034977251 (2 : ZMod 19331034977251)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (809, 1), (10619989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (809, 1), (10619989, 1)] : List FactorBlock).map factorBlockValue).prod) = 19331034977251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_809
      · exact prime_eightyBZ_10619989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19331034977251) ^ 9665517488625 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 19331034977251) ^ 6443678325750 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 19331034977251) ^ 3866206995450 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 19331034977251) ^ 23894975250 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 19331034977251) ^ 1820250 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_20760849245221 : Nat.Prime 20760849245221 := by
  apply lucas_primality 20760849245221 (10 : ZMod 20760849245221)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (73, 1), (107, 1), (6328331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (73, 1), (107, 1), (6328331, 1)] : List FactorBlock).map factorBlockValue).prod) = 20760849245221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_73
      · exact prime_eightyBZ_107
      · exact prime_eightyBZ_6328331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 20760849245221) ^ 10380424622610 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 20760849245221) ^ 6920283081740 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 20760849245221) ^ 4152169849044 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 20760849245221) ^ 2965835606460 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 20760849245221) ^ 284395195140 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 20760849245221) ^ 194026628460 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 20760849245221) ^ 3280620 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_21445265783719 : Nat.Prime 21445265783719 := by
  apply lucas_primality 21445265783719 (3 : ZMod 21445265783719)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (431, 1), (2081, 1), (27109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (431, 1), (2081, 1), (27109, 1)] : List FactorBlock).map factorBlockValue).prod) = 21445265783719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_431
      · exact prime_eightyBZ_2081
      · exact prime_eightyBZ_27109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21445265783719) ^ 10722632891859 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 21445265783719) ^ 7148421927906 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 21445265783719) ^ 3063609397674 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 21445265783719) ^ 49756997178 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 21445265783719) ^ 10305269478 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 21445265783719) ^ 791075502 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_25647759631649 : Nat.Prime 25647759631649 := by
  apply lucas_primality 25647759631649 (6 : ZMod 25647759631649)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (11, 1), (443, 1), (3356657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (11, 1), (443, 1), (3356657, 1)] : List FactorBlock).map factorBlockValue).prod) = 25647759631649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_443
      · exact prime_eightyBZ_3356657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 25647759631649) ^ 12823879815824 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 25647759631649) ^ 3663965661664 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 25647759631649) ^ 2331614511968 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 25647759631649) ^ 57895619936 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 25647759631649) ^ 7640864 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_32594570625257 : Nat.Prime 32594570625257 := by
  apply lucas_primality 32594570625257 (3 : ZMod 32594570625257)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1831, 1), (9661, 1), (230327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1831, 1), (9661, 1), (230327, 1)] : List FactorBlock).map factorBlockValue).prod) = 32594570625257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_1831
      · exact prime_eightyBZ_9661
      · exact prime_eightyBZ_230327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32594570625257) ^ 16297285312628 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 32594570625257) ^ 17801513176 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 32594570625257) ^ 3373829896 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 32594570625257) ^ 141514328 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_48576147748091 : Nat.Prime 48576147748091 := by
  apply lucas_primality 48576147748091 (6 : ZMod 48576147748091)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (23, 1), (47, 1), (3847, 1), (68711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (23, 1), (47, 1), (3847, 1), (68711, 1)] : List FactorBlock).map factorBlockValue).prod) = 48576147748091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_17
      · exact prime_eightyBZ_23
      · exact prime_eightyBZ_47
      · exact prime_eightyBZ_3847
      · exact prime_eightyBZ_68711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 48576147748091) ^ 24288073874045 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 48576147748091) ^ 9715229549618 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 48576147748091) ^ 2857420455770 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 48576147748091) ^ 2112006423830 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 48576147748091) ^ 1033535058470 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 48576147748091) ^ 12627020470 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 48576147748091) ^ 706963190 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_51020589042571 : Nat.Prime 51020589042571 := by
  apply lucas_primality 51020589042571 (2 : ZMod 51020589042571)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (71, 1), (12479, 1), (274213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (71, 1), (12479, 1), (274213, 1)] : List FactorBlock).map factorBlockValue).prod) = 51020589042571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_71
      · exact prime_eightyBZ_12479
      · exact prime_eightyBZ_274213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51020589042571) ^ 25510294521285 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51020589042571) ^ 17006863014190 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51020589042571) ^ 10204117808514 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51020589042571) ^ 7288655577510 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51020589042571) ^ 718599845670 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51020589042571) ^ 4088515830 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51020589042571) ^ 186061890 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_54996332856947 : Nat.Prime 54996332856947 := by
  apply lucas_primality 54996332856947 (2 : ZMod 54996332856947)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2115243571421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2115243571421, 1)] : List FactorBlock).map factorBlockValue).prod) = 54996332856947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_2115243571421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 54996332856947) ^ 27498166428473 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 54996332856947) ^ 4230487142842 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 54996332856947) ^ 26 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_61261880972807 : Nat.Prime 61261880972807 := by
  apply lucas_primality 61261880972807 (5 : ZMod 61261880972807)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (457, 1), (67026127979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (457, 1), (67026127979, 1)] : List FactorBlock).map factorBlockValue).prod) = 61261880972807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_457
      · exact prime_eightyBZ_67026127979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 61261880972807) ^ 30630940486403 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 61261880972807) ^ 134052255958 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 61261880972807) ^ 914 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_81112115744641 : Nat.Prime 81112115744641 := by
  apply lucas_primality 81112115744641 (19 : ZMod 81112115744641)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 1), (17431, 1), (807869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 1), (17431, 1), (807869, 1)] : List FactorBlock).map factorBlockValue).prod) = 81112115744641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_17431
      · exact prime_eightyBZ_807869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 81112115744641) ^ 40556057872320 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 81112115744641) ^ 27037371914880 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 81112115744641) ^ 16222423148928 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 81112115744641) ^ 4653325440 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 81112115744641) ^ 100402560 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_95577941275199 : Nat.Prime 95577941275199 := by
  apply lucas_primality 95577941275199 (11 : ZMod 95577941275199)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (85259, 1), (560515261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (85259, 1), (560515261, 1)] : List FactorBlock).map factorBlockValue).prod) = 95577941275199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_85259
      · exact prime_eightyBZ_560515261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 95577941275199) ^ 47788970637599 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 95577941275199) ^ 1121030522 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 95577941275199) ^ 170518 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_112956292012163 : Nat.Prime 112956292012163 := by
  apply lucas_primality 112956292012163 (2 : ZMod 112956292012163)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (84521, 1), (668214361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (84521, 1), (668214361, 1)] : List FactorBlock).map factorBlockValue).prod) = 112956292012163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_84521
      · exact prime_eightyBZ_668214361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 112956292012163) ^ 56478146006081 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 112956292012163) ^ 1336428722 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 112956292012163) ^ 169042 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_143713379841263 : Nat.Prime 143713379841263 := by
  apply lucas_primality 143713379841263 (5 : ZMod 143713379841263)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (933203765203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (933203765203, 1)] : List FactorBlock).map factorBlockValue).prod) = 143713379841263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_933203765203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 143713379841263) ^ 71856689920631 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 143713379841263) ^ 20530482834466 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 143713379841263) ^ 13064852712842 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 143713379841263) ^ 154 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_150669373198153 : Nat.Prime 150669373198153 := by
  apply lucas_primality 150669373198153 (5 : ZMod 150669373198153)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6277890549923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6277890549923, 1)] : List FactorBlock).map factorBlockValue).prod) = 150669373198153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_6277890549923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 150669373198153) ^ 75334686599076 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 150669373198153) ^ 50223124399384 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 150669373198153) ^ 24 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_151616772713069 : Nat.Prime 151616772713069 := by
  apply lucas_primality 151616772713069 (2 : ZMod 151616772713069)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (653, 1), (1291, 1), (203449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (653, 1), (1291, 1), (203449, 1)] : List FactorBlock).map factorBlockValue).prod) = 151616772713069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_17
      · exact prime_eightyBZ_653
      · exact prime_eightyBZ_1291
      · exact prime_eightyBZ_203449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 151616772713069) ^ 75808386356534 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 151616772713069) ^ 11662828670236 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 151616772713069) ^ 8918633689004 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 151616772713069) ^ 232184950556 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 151616772713069) ^ 117441342148 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 151616772713069) ^ 745232332 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_157919462118773 : Nat.Prime 157919462118773 := by
  apply lucas_primality 157919462118773 (2 : ZMod 157919462118773)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (938263, 1), (42077611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (938263, 1), (42077611, 1)] : List FactorBlock).map factorBlockValue).prod) = 157919462118773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_938263
      · exact prime_eightyBZ_42077611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 157919462118773) ^ 78959731059386 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 157919462118773) ^ 168310444 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 157919462118773) ^ 3753052 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_236456579933279 : Nat.Prime 236456579933279 := by
  apply lucas_primality 236456579933279 (29 : ZMod 236456579933279)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (529723, 1), (223188893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (529723, 1), (223188893, 1)] : List FactorBlock).map factorBlockValue).prod) = 236456579933279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_529723
      · exact prime_eightyBZ_223188893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (29 : ZMod 236456579933279) ^ 118228289966639 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (29 : ZMod 236456579933279) ^ 446377786 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (29 : ZMod 236456579933279) ^ 1059446 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_247047590392511 : Nat.Prime 247047590392511 := by
  apply lucas_primality 247047590392511 (19 : ZMod 247047590392511)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (359, 1), (1117, 1), (61607417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (359, 1), (1117, 1), (61607417, 1)] : List FactorBlock).map factorBlockValue).prod) = 247047590392511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_359
      · exact prime_eightyBZ_1117
      · exact prime_eightyBZ_61607417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 247047590392511) ^ 123523795196255 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 247047590392511) ^ 49409518078502 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 247047590392511) ^ 688154847890 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 247047590392511) ^ 221170627030 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 247047590392511) ^ 4010030 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_278440972751141 : Nat.Prime 278440972751141 := by
  apply lucas_primality 278440972751141 (2 : ZMod 278440972751141)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (773, 1), (580981039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (773, 1), (580981039, 1)] : List FactorBlock).map factorBlockValue).prod) = 278440972751141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_31
      · exact prime_eightyBZ_773
      · exact prime_eightyBZ_580981039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 278440972751141) ^ 139220486375570 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 278440972751141) ^ 55688194550228 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 278440972751141) ^ 8981966862940 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 278440972751141) ^ 360208244180 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 278440972751141) ^ 479260 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_328112736155747 : Nat.Prime 328112736155747 := by
  apply lucas_primality 328112736155747 (2 : ZMod 328112736155747)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4862519, 1), (33738967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4862519, 1), (33738967, 1)] : List FactorBlock).map factorBlockValue).prod) = 328112736155747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_4862519
      · exact prime_eightyBZ_33738967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 328112736155747) ^ 164056368077873 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 328112736155747) ^ 67477934 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 328112736155747) ^ 9725038 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_455529828574889 : Nat.Prime 455529828574889 := by
  apply lucas_primality 455529828574889 (3 : ZMod 455529828574889)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (1963490640409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (1963490640409, 1)] : List FactorBlock).map factorBlockValue).prod) = 455529828574889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_29
      · exact prime_eightyBZ_1963490640409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 455529828574889) ^ 227764914287444 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 455529828574889) ^ 15707925123272 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 455529828574889) ^ 232 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_938024927029297 : Nat.Prime 938024927029297 := by
  apply lucas_primality 938024927029297 (5 : ZMod 938024927029297)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (566549, 1), (3832597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (566549, 1), (3832597, 1)] : List FactorBlock).map factorBlockValue).prod) = 938024927029297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_566549
      · exact prime_eightyBZ_3832597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 938024927029297) ^ 469012463514648 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 938024927029297) ^ 312674975676432 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 938024927029297) ^ 1655681904 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 938024927029297) ^ 244749168 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_974174173270847 : Nat.Prime 974174173270847 := by
  apply lucas_primality 974174173270847 (5 : ZMod 974174173270847)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (743167, 1), (655420769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (743167, 1), (655420769, 1)] : List FactorBlock).map factorBlockValue).prod) = 974174173270847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_743167
      · exact prime_eightyBZ_655420769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 974174173270847) ^ 487087086635423 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 974174173270847) ^ 1310841538 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 974174173270847) ^ 1486334 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1005247782883121 : Nat.Prime 1005247782883121 := by
  apply lucas_primality 1005247782883121 (6 : ZMod 1005247782883121)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (19, 1), (94478175083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (19, 1), (94478175083, 1)] : List FactorBlock).map factorBlockValue).prod) = 1005247782883121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_94478175083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1005247782883121) ^ 502623891441560 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1005247782883121) ^ 201049556576624 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1005247782883121) ^ 143606826126160 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1005247782883121) ^ 52907778046480 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1005247782883121) ^ 10640 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1270435046702981 : Nat.Prime 1270435046702981 := by
  apply lucas_primality 1270435046702981 (2 : ZMod 1270435046702981)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (181, 1), (583021, 1), (601949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (181, 1), (583021, 1), (601949, 1)] : List FactorBlock).map factorBlockValue).prod) = 1270435046702981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_181
      · exact prime_eightyBZ_583021
      · exact prime_eightyBZ_601949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1270435046702981) ^ 635217523351490 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270435046702981) ^ 254087009340596 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270435046702981) ^ 7018978158580 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270435046702981) ^ 2179055380 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270435046702981) ^ 2110536020 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1741778243148589 : Nat.Prime 1741778243148589 := by
  apply lucas_primality 1741778243148589 (2 : ZMod 1741778243148589)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5059, 1), (28691082611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5059, 1), (28691082611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1741778243148589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5059
      · exact prime_eightyBZ_28691082611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1741778243148589) ^ 870889121574294 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1741778243148589) ^ 580592747716196 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1741778243148589) ^ 344292991332 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1741778243148589) ^ 60708 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1825295955014393 : Nat.Prime 1825295955014393 := by
  apply lucas_primality 1825295955014393 (3 : ZMod 1825295955014393)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (32594570625257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (32594570625257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1825295955014393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_32594570625257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1825295955014393) ^ 912647977507196 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1825295955014393) ^ 260756565002056 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1825295955014393) ^ 56 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2366698070428277 : Nat.Prime 2366698070428277 := by
  apply lucas_primality 2366698070428277 (2 : ZMod 2366698070428277)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (127, 1), (3433, 1), (104390743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (127, 1), (3433, 1), (104390743, 1)] : List FactorBlock).map factorBlockValue).prod) = 2366698070428277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_127
      · exact prime_eightyBZ_3433
      · exact prime_eightyBZ_104390743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2366698070428277) ^ 1183349035214138 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2366698070428277) ^ 182053697725252 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2366698070428277) ^ 18635417877388 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2366698070428277) ^ 689396466772 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2366698070428277) ^ 22671532 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2440295033985707 : Nat.Prime 2440295033985707 := by
  apply lucas_primality 2440295033985707 (2 : ZMod 2440295033985707)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (8080447132403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (8080447132403, 1)] : List FactorBlock).map factorBlockValue).prod) = 2440295033985707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_151
      · exact prime_eightyBZ_8080447132403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2440295033985707) ^ 1220147516992853 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2440295033985707) ^ 16160894264806 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2440295033985707) ^ 302 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2627322562457377 : Nat.Prime 2627322562457377 := by
  apply lucas_primality 2627322562457377 (5 : ZMod 2627322562457377)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (3909706194133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (3909706194133, 1)] : List FactorBlock).map factorBlockValue).prod) = 2627322562457377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_3909706194133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2627322562457377) ^ 1313661281228688 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2627322562457377) ^ 875774187485792 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2627322562457377) ^ 375331794636768 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2627322562457377) ^ 672 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3241146259241857 : Nat.Prime 3241146259241857 := by
  apply lucas_primality 3241146259241857 (13 : ZMod 3241146259241857)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (7, 2), (181, 1), (317227987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (7, 2), (181, 1), (317227987, 1)] : List FactorBlock).map factorBlockValue).prod) = 3241146259241857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_181
      · exact prime_eightyBZ_317227987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3241146259241857) ^ 1620573129620928 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3241146259241857) ^ 1080382086413952 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3241146259241857) ^ 463020894177408 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3241146259241857) ^ 17906885410176 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3241146259241857) ^ 10217088 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3271005862038721 : Nat.Prime 3271005862038721 := by
  apply lucas_primality 3271005862038721 (53 : ZMod 3271005862038721)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (13, 1), (87366609563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (13, 1), (87366609563, 1)] : List FactorBlock).map factorBlockValue).prod) = 3271005862038721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_87366609563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (53 : ZMod 3271005862038721) ^ 1635502931019360 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (53 : ZMod 3271005862038721) ^ 1090335287346240 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (53 : ZMod 3271005862038721) ^ 654201172407744 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (53 : ZMod 3271005862038721) ^ 251615835541440 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (53 : ZMod 3271005862038721) ^ 37440 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3905786064605429 : Nat.Prime 3905786064605429 := by
  apply lucas_primality 3905786064605429 (3 : ZMod 3905786064605429)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (947, 1), (19219, 1), (2823671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (947, 1), (19219, 1), (2823671, 1)] : List FactorBlock).map factorBlockValue).prod) = 3905786064605429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_947
      · exact prime_eightyBZ_19219
      · exact prime_eightyBZ_2823671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3905786064605429) ^ 1952893032302714 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3905786064605429) ^ 205567687610812 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3905786064605429) ^ 4124378104124 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3905786064605429) ^ 203225249212 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3905786064605429) ^ 1383229868 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_4729131598665581 : Nat.Prime 4729131598665581 := by
  apply lucas_primality 4729131598665581 (2 : ZMod 4729131598665581)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (236456579933279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (236456579933279, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729131598665581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_236456579933279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4729131598665581) ^ 2364565799332790 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4729131598665581) ^ 945826319733116 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4729131598665581) ^ 20 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_4892720479763773 : Nat.Prime 4892720479763773 := by
  apply lucas_primality 4892720479763773 (2 : ZMod 4892720479763773)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (6910622146559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (6910622146559, 1)] : List FactorBlock).map factorBlockValue).prod) = 4892720479763773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_59
      · exact prime_eightyBZ_6910622146559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4892720479763773) ^ 2446360239881886 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4892720479763773) ^ 1630906826587924 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4892720479763773) ^ 82927465758708 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4892720479763773) ^ 708 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_5293643409732911 : Nat.Prime 5293643409732911 := by
  apply lucas_primality 5293643409732911 (14 : ZMod 5293643409732911)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (46511, 1), (192906559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (46511, 1), (192906559, 1)] : List FactorBlock).map factorBlockValue).prod) = 5293643409732911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_59
      · exact prime_eightyBZ_46511
      · exact prime_eightyBZ_192906559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 5293643409732911) ^ 2646821704866455 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (14 : ZMod 5293643409732911) ^ 1058728681946582 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (14 : ZMod 5293643409732911) ^ 89722769656490 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (14 : ZMod 5293643409732911) ^ 113814869810 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (14 : ZMod 5293643409732911) ^ 27441490 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_5376221896291963 : Nat.Prime 5376221896291963 := by
  apply lucas_primality 5376221896291963 (5 : ZMod 5376221896291963)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (619, 1), (1181, 1), (1225703393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (619, 1), (1181, 1), (1225703393, 1)] : List FactorBlock).map factorBlockValue).prod) = 5376221896291963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_619
      · exact prime_eightyBZ_1181
      · exact prime_eightyBZ_1225703393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5376221896291963) ^ 2688110948145981 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5376221896291963) ^ 1792073965430654 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5376221896291963) ^ 8685334242798 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5376221896291963) ^ 4552262401602 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5376221896291963) ^ 4386234 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_6211241815108723 : Nat.Prime 6211241815108723 := by
  apply lucas_primality 6211241815108723 (5 : ZMod 6211241815108723)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (47, 1), (16319, 1), (192813637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (47, 1), (16319, 1), (192813637, 1)] : List FactorBlock).map factorBlockValue).prod) = 6211241815108723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_47
      · exact prime_eightyBZ_16319
      · exact prime_eightyBZ_192813637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6211241815108723) ^ 3105620907554361 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6211241815108723) ^ 2070413938369574 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6211241815108723) ^ 887320259301246 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6211241815108723) ^ 132154081172526 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6211241815108723) ^ 380614119438 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6211241815108723) ^ 32213706 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_11525814493644043 : Nat.Prime 11525814493644043 := by
  apply lucas_primality 11525814493644043 (2 : ZMod 11525814493644043)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (241, 1), (337, 1), (7884100957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (241, 1), (337, 1), (7884100957, 1)] : List FactorBlock).map factorBlockValue).prod) = 11525814493644043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_241
      · exact prime_eightyBZ_337
      · exact prime_eightyBZ_7884100957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11525814493644043) ^ 5762907246822021 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11525814493644043) ^ 3841938164548014 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11525814493644043) ^ 47824956405162 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11525814493644043) ^ 34201229951466 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11525814493644043) ^ 1461906 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_14631710831911081 : Nat.Prime 14631710831911081 := by
  apply lucas_primality 14631710831911081 (7 : ZMod 14631710831911081)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (29, 1), (47, 1), (191, 1), (156121741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (29, 1), (47, 1), (191, 1), (156121741, 1)] : List FactorBlock).map factorBlockValue).prod) = 14631710831911081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_29
      · exact prime_eightyBZ_47
      · exact prime_eightyBZ_191
      · exact prime_eightyBZ_156121741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14631710831911081) ^ 7315855415955540 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14631710831911081) ^ 4877236943970360 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14631710831911081) ^ 2926342166382216 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14631710831911081) ^ 504541752824520 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14631710831911081) ^ 311312996423640 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14631710831911081) ^ 76605815873880 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14631710831911081) ^ 93719880 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_17068022214899723 : Nat.Prime 17068022214899723 := by
  apply lucas_primality 17068022214899723 (2 : ZMod 17068022214899723)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (3169, 1), (28843, 1), (771623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (3169, 1), (28843, 1), (771623, 1)] : List FactorBlock).map factorBlockValue).prod) = 17068022214899723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_3169
      · exact prime_eightyBZ_28843
      · exact prime_eightyBZ_771623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17068022214899723) ^ 8534011107449861 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17068022214899723) ^ 1551638383172702 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17068022214899723) ^ 5385933169738 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17068022214899723) ^ 591756135454 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17068022214899723) ^ 22119639014 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_52605405356625739 : Nat.Prime 52605405356625739 := by
  apply lucas_primality 52605405356625739 (2 : ZMod 52605405356625739)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (974174173270847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (974174173270847, 1)] : List FactorBlock).map factorBlockValue).prod) = 52605405356625739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_974174173270847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52605405356625739) ^ 26302702678312869 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 52605405356625739) ^ 17535135118875246 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 52605405356625739) ^ 54 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_56171417693634097 : Nat.Prime 56171417693634097 := by
  apply lucas_primality 56171417693634097 (11 : ZMod 56171417693634097)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (1559, 1), (6287, 1), (17056367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (1559, 1), (6287, 1), (17056367, 1)] : List FactorBlock).map factorBlockValue).prod) = 56171417693634097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_1559
      · exact prime_eightyBZ_6287
      · exact prime_eightyBZ_17056367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 56171417693634097) ^ 28085708846817048 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 56171417693634097) ^ 18723805897878032 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 56171417693634097) ^ 8024488241947728 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 56171417693634097) ^ 36030415454544 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 56171417693634097) ^ 8934534387408 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 56171417693634097) ^ 3293281488 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_64392965163310967 : Nat.Prime 64392965163310967 := by
  apply lucas_primality 64392965163310967 (5 : ZMod 64392965163310967)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (383, 1), (923779375711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (383, 1), (923779375711, 1)] : List FactorBlock).map factorBlockValue).prod) = 64392965163310967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_383
      · exact prime_eightyBZ_923779375711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 64392965163310967) ^ 32196482581655483 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 64392965163310967) ^ 9198995023330138 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 64392965163310967) ^ 4953305012562382 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 64392965163310967) ^ 168127846379402 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 64392965163310967) ^ 69706 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_65226920572665541 : Nat.Prime 65226920572665541 := by
  apply lucas_primality 65226920572665541 (2 : ZMod 65226920572665541)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (9973, 1), (2795021797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (9973, 1), (2795021797, 1)] : List FactorBlock).map factorBlockValue).prod) = 65226920572665541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_9973
      · exact prime_eightyBZ_2795021797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65226920572665541) ^ 32613460286332770 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 65226920572665541) ^ 21742306857555180 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 65226920572665541) ^ 13045384114533108 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 65226920572665541) ^ 5017455428666580 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 65226920572665541) ^ 6540351004980 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 65226920572665541) ^ 23336820 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_98212942454539337 : Nat.Prime 98212942454539337 := by
  apply lucas_primality 98212942454539337 (3 : ZMod 98212942454539337)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (773, 1), (2347, 1), (6766843807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (773, 1), (2347, 1), (6766843807, 1)] : List FactorBlock).map factorBlockValue).prod) = 98212942454539337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_773
      · exact prime_eightyBZ_2347
      · exact prime_eightyBZ_6766843807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 98212942454539337) ^ 49106471227269668 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 98212942454539337) ^ 127054259320232 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 98212942454539337) ^ 41846162102488 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 98212942454539337) ^ 14513848 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_122291191827167291 : Nat.Prime 122291191827167291 := by
  apply lucas_primality 122291191827167291 (2 : ZMod 122291191827167291)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2753237, 1), (4441724117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2753237, 1), (4441724117, 1)] : List FactorBlock).map factorBlockValue).prod) = 122291191827167291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_2753237
      · exact prime_eightyBZ_4441724117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 122291191827167291) ^ 61145595913583645 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 122291191827167291) ^ 24458238365433458 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 122291191827167291) ^ 44417241170 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 122291191827167291) ^ 27532370 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_261514787356833193 : Nat.Prime 261514787356833193 := by
  apply lucas_primality 261514787356833193 (5 : ZMod 261514787356833193)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (13, 2), (1023429085489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (13, 2), (1023429085489, 1)] : List FactorBlock).map factorBlockValue).prod) = 261514787356833193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_1023429085489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 261514787356833193) ^ 130757393678416596 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 261514787356833193) ^ 87171595785611064 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 261514787356833193) ^ 37359255336690456 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 261514787356833193) ^ 20116522104371784 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 261514787356833193) ^ 255528 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_277884090805638719 : Nat.Prime 277884090805638719 := by
  apply lucas_primality 277884090805638719 (23 : ZMod 277884090805638719)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (499, 1), (278440972751141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (499, 1), (278440972751141, 1)] : List FactorBlock).map factorBlockValue).prod) = 277884090805638719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_499
      · exact prime_eightyBZ_278440972751141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 277884090805638719) ^ 138942045402819359 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (23 : ZMod 277884090805638719) ^ 556881945502282 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (23 : ZMod 277884090805638719) ^ 998 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_403426740935475233 : Nat.Prime 403426740935475233 := by
  apply lucas_primality 403426740935475233 (3 : ZMod 403426740935475233)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (53, 2), (331, 1), (13559228219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (53, 2), (331, 1), (13559228219, 1)] : List FactorBlock).map factorBlockValue).prod) = 403426740935475233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_53
      · exact prime_eightyBZ_331
      · exact prime_eightyBZ_13559228219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 403426740935475233) ^ 201713370467737616 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 403426740935475233) ^ 7611825300669344 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 403426740935475233) ^ 1218811906149472 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 403426740935475233) ^ 29752928 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_430997482444348249 : Nat.Prime 430997482444348249 := by
  apply lucas_primality 430997482444348249 (7 : ZMod 430997482444348249)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 1), (2991871, 1), (41974409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 1), (2991871, 1), (41974409, 1)] : List FactorBlock).map factorBlockValue).prod) = 430997482444348249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_2991871
      · exact prime_eightyBZ_41974409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 430997482444348249) ^ 215498741222174124 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 430997482444348249) ^ 143665827481449416 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 430997482444348249) ^ 39181589313122568 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 430997482444348249) ^ 33153652495719096 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 430997482444348249) ^ 144056171688 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 430997482444348249) ^ 10268101272 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_578143659561816571 : Nat.Prime 578143659561816571 := by
  apply lucas_primality 578143659561816571 (2 : ZMod 578143659561816571)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1307, 1), (14744801315017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1307, 1), (14744801315017, 1)] : List FactorBlock).map factorBlockValue).prod) = 578143659561816571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_1307
      · exact prime_eightyBZ_14744801315017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 578143659561816571) ^ 289071829780908285 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 578143659561816571) ^ 192714553187272190 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 578143659561816571) ^ 115628731912363314 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 578143659561816571) ^ 442344039450510 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 578143659561816571) ^ 39210 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_614502998939847463 : Nat.Prime 614502998939847463 := by
  apply lucas_primality 614502998939847463 (3 : ZMod 614502998939847463)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1723, 1), (4903, 1), (12123432133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1723, 1), (4903, 1), (12123432133, 1)] : List FactorBlock).map factorBlockValue).prod) = 614502998939847463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_1723
      · exact prime_eightyBZ_4903
      · exact prime_eightyBZ_12123432133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 614502998939847463) ^ 307251499469923731 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 614502998939847463) ^ 204834332979949154 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 614502998939847463) ^ 356647126488594 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 614502998939847463) ^ 125332041390954 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 614502998939847463) ^ 50687214 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_806433284443794451 : Nat.Prime 806433284443794451 := by
  apply lucas_primality 806433284443794451 (3 : ZMod 806433284443794451)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (5376221896291963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (5376221896291963, 1)] : List FactorBlock).map factorBlockValue).prod) = 806433284443794451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_5376221896291963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 806433284443794451) ^ 403216642221897225 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 806433284443794451) ^ 268811094814598150 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 806433284443794451) ^ 161286656888758890 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 806433284443794451) ^ 150 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1400992852343860861 : Nat.Prime 1400992852343860861 := by
  apply lucas_primality 1400992852343860861 (6 : ZMod 1400992852343860861)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (2801, 1), (1190895132983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (2801, 1), (1190895132983, 1)] : List FactorBlock).map factorBlockValue).prod) = 1400992852343860861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_2801
      · exact prime_eightyBZ_1190895132983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1400992852343860861) ^ 700496426171930430 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1400992852343860861) ^ 466997617447953620 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1400992852343860861) ^ 280198570468772172 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1400992852343860861) ^ 200141836049122980 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1400992852343860861) ^ 500175955852860 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1400992852343860861) ^ 1176420 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2610262677906899359 : Nat.Prime 2610262677906899359 := by
  apply lucas_primality 2610262677906899359 (11 : ZMod 2610262677906899359)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (3271005862038721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (3271005862038721, 1)] : List FactorBlock).map factorBlockValue).prod) = 2610262677906899359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_3271005862038721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2610262677906899359) ^ 1305131338953449679 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2610262677906899359) ^ 870087559302299786 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2610262677906899359) ^ 372894668272414194 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2610262677906899359) ^ 137382246205626282 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2610262677906899359) ^ 798 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3146443761010750483 : Nat.Prime 3146443761010750483 := by
  apply lucas_primality 3146443761010750483 (5 : ZMod 3146443761010750483)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (61729, 1), (44017175651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (61729, 1), (44017175651, 1)] : List FactorBlock).map factorBlockValue).prod) = 3146443761010750483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_193
      · exact prime_eightyBZ_61729
      · exact prime_eightyBZ_44017175651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3146443761010750483) ^ 1573221880505375241 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3146443761010750483) ^ 1048814587003583494 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3146443761010750483) ^ 16302817414563474 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3146443761010750483) ^ 50971889403858 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3146443761010750483) ^ 71482182 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_3841442190193255733 : Nat.Prime 3841442190193255733 := by
  apply lucas_primality 3841442190193255733 (2 : ZMod 3841442190193255733)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2689, 1), (51020589042571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2689, 1), (51020589042571, 1)] : List FactorBlock).map factorBlockValue).prod) = 3841442190193255733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_2689
      · exact prime_eightyBZ_51020589042571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3841442190193255733) ^ 1920721095096627866 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3841442190193255733) ^ 548777455741893676 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3841442190193255733) ^ 1428576493191988 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3841442190193255733) ^ 75292 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_4454145273740651387 : Nat.Prime 4454145273740651387 := by
  apply lucas_primality 4454145273740651387 (2 : ZMod 4454145273740651387)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1753, 1), (1270435046702981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1753, 1), (1270435046702981, 1)] : List FactorBlock).map factorBlockValue).prod) = 4454145273740651387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_1753
      · exact prime_eightyBZ_1270435046702981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4454145273740651387) ^ 2227072636870325693 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4454145273740651387) ^ 2540870093405962 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4454145273740651387) ^ 3506 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_5022651282738255427 : Nat.Prime 5022651282738255427 := by
  apply lucas_primality 5022651282738255427 (5 : ZMod 5022651282738255427)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (64392965163310967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (64392965163310967, 1)] : List FactorBlock).map factorBlockValue).prod) = 5022651282738255427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_64392965163310967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5022651282738255427) ^ 2511325641369127713 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5022651282738255427) ^ 1674217094246085142 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5022651282738255427) ^ 386357790979865802 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5022651282738255427) ^ 78 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_5081274839193166249 : Nat.Prime 5081274839193166249 := by
  apply lucas_primality 5081274839193166249 (14 : ZMod 5081274839193166249)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (857, 1), (247047590392511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (857, 1), (247047590392511, 1)] : List FactorBlock).map factorBlockValue).prod) = 5081274839193166249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_857
      · exact prime_eightyBZ_247047590392511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 5081274839193166249) ^ 2540637419596583124 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (14 : ZMod 5081274839193166249) ^ 1693758279731055416 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (14 : ZMod 5081274839193166249) ^ 5929142169420264 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (14 : ZMod 5081274839193166249) ^ 20568 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_5344877165671129231 : Nat.Prime 5344877165671129231 := by
  apply lucas_primality 5344877165671129231 (6 : ZMod 5344877165671129231)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (233, 1), (940127, 1), (271114517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (233, 1), (940127, 1), (271114517, 1)] : List FactorBlock).map factorBlockValue).prod) = 5344877165671129231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_233
      · exact prime_eightyBZ_940127
      · exact prime_eightyBZ_271114517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5344877165671129231) ^ 2672438582835564615 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 5344877165671129231) ^ 1781625721890376410 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 5344877165671129231) ^ 1068975433134225846 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 5344877165671129231) ^ 22939386977129310 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 5344877165671129231) ^ 5685271421490 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 5344877165671129231) ^ 19714463190 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_5412827893040110093 : Nat.Prime 5412827893040110093 := by
  apply lucas_primality 5412827893040110093 (2 : ZMod 5412827893040110093)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (401, 1), (270899, 1), (377483969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (401, 1), (270899, 1), (377483969, 1)] : List FactorBlock).map factorBlockValue).prod) = 5412827893040110093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_401
      · exact prime_eightyBZ_270899
      · exact prime_eightyBZ_377483969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5412827893040110093) ^ 2706413946520055046 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5412827893040110093) ^ 1804275964346703364 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5412827893040110093) ^ 492075263003646372 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5412827893040110093) ^ 13498323922793292 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5412827893040110093) ^ 19980981447108 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5412827893040110093) ^ 14339225868 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_11832919489147351093 : Nat.Prime 11832919489147351093 := by
  apply lucas_primality 11832919489147351093 (2 : ZMod 11832919489147351093)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5813, 1), (108881, 1), (1557966947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5813, 1), (108881, 1), (1557966947, 1)] : List FactorBlock).map factorBlockValue).prod) = 11832919489147351093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5813
      · exact prime_eightyBZ_108881
      · exact prime_eightyBZ_1557966947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11832919489147351093) ^ 5916459744573675546 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11832919489147351093) ^ 3944306496382450364 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11832919489147351093) ^ 2035595989875684 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11832919489147351093) ^ 108677542354932 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11832919489147351093) ^ 7595103036 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_13271861047529247743 : Nat.Prime 13271861047529247743 := by
  apply lucas_primality 13271861047529247743 (5 : ZMod 13271861047529247743)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1699, 1), (3905786064605429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1699, 1), (3905786064605429, 1)] : List FactorBlock).map factorBlockValue).prod) = 13271861047529247743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_1699
      · exact prime_eightyBZ_3905786064605429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 13271861047529247743) ^ 6635930523764623871 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 13271861047529247743) ^ 7811572129210858 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 13271861047529247743) ^ 3398 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_13941611022018854227 : Nat.Prime 13941611022018854227 := by
  apply lucas_primality 13941611022018854227 (2 : ZMod 13941611022018854227)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (13007, 1), (13741723906081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (13007, 1), (13741723906081, 1)] : List FactorBlock).map factorBlockValue).prod) = 13941611022018854227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_13007
      · exact prime_eightyBZ_13741723906081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13941611022018854227) ^ 6970805511009427113 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13941611022018854227) ^ 4647203674006284742 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13941611022018854227) ^ 1072431617078373402 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13941611022018854227) ^ 1071854464674318 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13941611022018854227) ^ 1014546 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_14820852292155091991 : Nat.Prime 14820852292155091991 := by
  apply lucas_primality 14820852292155091991 (7 : ZMod 14820852292155091991)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4517, 1), (328112736155747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4517, 1), (328112736155747, 1)] : List FactorBlock).map factorBlockValue).prod) = 14820852292155091991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_4517
      · exact prime_eightyBZ_328112736155747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 14820852292155091991) ^ 7410426146077545995 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14820852292155091991) ^ 2964170458431018398 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14820852292155091991) ^ 3281127361557470 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14820852292155091991) ^ 45170 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_19600209576387532409 : Nat.Prime 19600209576387532409 := by
  apply lucas_primality 19600209576387532409 (3 : ZMod 19600209576387532409)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 2), (4051, 1), (1143280544069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 2), (4051, 1), (1143280544069, 1)] : List FactorBlock).map factorBlockValue).prod) = 19600209576387532409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_23
      · exact prime_eightyBZ_4051
      · exact prime_eightyBZ_1143280544069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 19600209576387532409) ^ 9800104788193766204 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 19600209576387532409) ^ 852183025060327496 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 19600209576387532409) ^ 4838363262500008 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 19600209576387532409) ^ 17143832 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_24303697274761091419 : Nat.Prime 24303697274761091419 := by
  apply lucas_primality 24303697274761091419 (3 : ZMod 24303697274761091419)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (52605405356625739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (52605405356625739, 1)] : List FactorBlock).map factorBlockValue).prod) = 24303697274761091419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_52605405356625739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24303697274761091419) ^ 12151848637380545709 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 24303697274761091419) ^ 8101232424920363806 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 24303697274761091419) ^ 3471956753537298774 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 24303697274761091419) ^ 2209427024978281038 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 24303697274761091419) ^ 462 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_27311859462347212741 : Nat.Prime 27311859462347212741 := by
  apply lucas_primality 27311859462347212741 (2 : ZMod 27311859462347212741)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (6257, 1), (420769, 1), (13299851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (6257, 1), (420769, 1), (13299851, 1)] : List FactorBlock).map factorBlockValue).prod) = 27311859462347212741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_6257
      · exact prime_eightyBZ_420769
      · exact prime_eightyBZ_13299851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27311859462347212741) ^ 13655929731173606370 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 27311859462347212741) ^ 9103953154115737580 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 27311859462347212741) ^ 5462371892469442548 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 27311859462347212741) ^ 2100912266334400980 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 27311859462347212741) ^ 4365008704226820 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 27311859462347212741) ^ 64909390811460 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 27311859462347212741) ^ 2053546273740 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_29641704584310183983 : Nat.Prime 29641704584310183983 := by
  apply lucas_primality 29641704584310183983 (5 : ZMod 29641704584310183983)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14820852292155091991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14820852292155091991, 1)] : List FactorBlock).map factorBlockValue).prod) = 29641704584310183983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_14820852292155091991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 29641704584310183983) ^ 14820852292155091991 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 29641704584310183983) ^ 2 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_38686335965400572923 : Nat.Prime 38686335965400572923 := by
  apply lucas_primality 38686335965400572923 (2 : ZMod 38686335965400572923)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (59, 1), (540121, 1), (18393763103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (59, 1), (540121, 1), (18393763103, 1)] : List FactorBlock).map factorBlockValue).prod) = 38686335965400572923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_59
      · exact prime_eightyBZ_540121
      · exact prime_eightyBZ_18393763103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38686335965400572923) ^ 19343167982700286461 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38686335965400572923) ^ 12895445321800190974 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38686335965400572923) ^ 3516939633218233902 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38686335965400572923) ^ 655700609583060558 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38686335965400572923) ^ 71625313523082 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38686335965400572923) ^ 2103231174 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_50812748391931662491 : Nat.Prime 50812748391931662491 := by
  apply lucas_primality 50812748391931662491 (2 : ZMod 50812748391931662491)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5081274839193166249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5081274839193166249, 1)] : List FactorBlock).map factorBlockValue).prod) = 50812748391931662491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_5081274839193166249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50812748391931662491) ^ 25406374195965831245 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 50812748391931662491) ^ 10162549678386332498 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 50812748391931662491) ^ 10 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_71377313242425837107 : Nat.Prime 71377313242425837107 := by
  apply lucas_primality 71377313242425837107 (2 : ZMod 71377313242425837107)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (101, 1), (98221, 1), (83663498251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (101, 1), (98221, 1), (83663498251, 1)] : List FactorBlock).map factorBlockValue).prod) = 71377313242425837107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_43
      · exact prime_eightyBZ_101
      · exact prime_eightyBZ_98221
      · exact prime_eightyBZ_83663498251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 71377313242425837107) ^ 35688656621212918553 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 71377313242425837107) ^ 1659937517265717142 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 71377313242425837107) ^ 706706071707186506 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 71377313242425837107) ^ 726701145808186 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 71377313242425837107) ^ 853147606 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_88015361541674364823 : Nat.Prime 88015361541674364823 := by
  apply lucas_primality 88015361541674364823 (3 : ZMod 88015361541674364823)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (139, 1), (34383149, 1), (180550151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (139, 1), (34383149, 1), (180550151, 1)] : List FactorBlock).map factorBlockValue).prod) = 88015361541674364823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_17
      · exact prime_eightyBZ_139
      · exact prime_eightyBZ_34383149
      · exact prime_eightyBZ_180550151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88015361541674364823) ^ 44007680770837182411 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 88015361541674364823) ^ 29338453847224788274 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 88015361541674364823) ^ 5177374208333786166 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 88015361541674364823) ^ 633204039868160898 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 88015361541674364823) ^ 2559840040878 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 88015361541674364823) ^ 487484286522 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_244164136406017891913 : Nat.Prime 244164136406017891913 := by
  apply lucas_primality 244164136406017891913 (3 : ZMod 244164136406017891913)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (32537, 1), (938024927029297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (32537, 1), (938024927029297, 1)] : List FactorBlock).map factorBlockValue).prod) = 244164136406017891913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_32537
      · exact prime_eightyBZ_938024927029297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 244164136406017891913) ^ 122082068203008945956 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 244164136406017891913) ^ 7504199416234376 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 244164136406017891913) ^ 260296 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_250948998396339376087 : Nat.Prime 250948998396339376087 := by
  apply lucas_primality 250948998396339376087 (3 : ZMod 250948998396339376087)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13941611022018854227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13941611022018854227, 1)] : List FactorBlock).map factorBlockValue).prod) = 250948998396339376087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_13941611022018854227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 250948998396339376087) ^ 125474499198169688043 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 250948998396339376087) ^ 83649666132113125362 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 250948998396339376087) ^ 18 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_294544530006962803079 : Nat.Prime 294544530006962803079 := by
  apply lucas_primality 294544530006962803079 (7 : ZMod 294544530006962803079)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41, 1), (79, 1), (2341, 1), (475051, 1), (5840773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41, 1), (79, 1), (2341, 1), (475051, 1), (5840773, 1)] : List FactorBlock).map factorBlockValue).prod) = 294544530006962803079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_41
      · exact prime_eightyBZ_79
      · exact prime_eightyBZ_2341
      · exact prime_eightyBZ_475051
      · exact prime_eightyBZ_5840773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 294544530006962803079) ^ 147272265003481401539 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 294544530006962803079) ^ 42077790000994686154 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 294544530006962803079) ^ 7184012926999092758 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 294544530006962803079) ^ 3728411772240035482 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 294544530006962803079) ^ 125819961557865358 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 294544530006962803079) ^ 620027176044178 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 294544530006962803079) ^ 50429032254286 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_355034453965899459233 : Nat.Prime 355034453965899459233 := by
  apply lucas_primality 355034453965899459233 (5 : ZMod 355034453965899459233)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (149, 1), (673, 1), (1315019, 1), (6472079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (149, 1), (673, 1), (1315019, 1), (6472079, 1)] : List FactorBlock).map factorBlockValue).prod) = 355034453965899459233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_149
      · exact prime_eightyBZ_673
      · exact prime_eightyBZ_1315019
      · exact prime_eightyBZ_6472079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 355034453965899459233) ^ 177517226982949729616 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 355034453965899459233) ^ 27310342612761496864 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 355034453965899459233) ^ 2382781570240935968 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 355034453965899459233) ^ 527540050469389984 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 355034453965899459233) ^ 269984277007328 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 355034453965899459233) ^ 54856322669408 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_529403042215107284647 : Nat.Prime 529403042215107284647 := by
  apply lucas_primality 529403042215107284647 (3 : ZMod 529403042215107284647)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (317, 1), (28856273, 1), (507670679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (317, 1), (28856273, 1), (507670679, 1)] : List FactorBlock).map factorBlockValue).prod) = 529403042215107284647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_317
      · exact prime_eightyBZ_28856273
      · exact prime_eightyBZ_507670679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 529403042215107284647) ^ 264701521107553642323 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 529403042215107284647) ^ 176467680738369094882 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 529403042215107284647) ^ 27863318011321436034 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 529403042215107284647) ^ 1670041142634407838 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 529403042215107284647) ^ 18346202997702 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 529403042215107284647) ^ 1042807993674 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_783756198856822717807 : Nat.Prime 783756198856822717807 := by
  apply lucas_primality 783756198856822717807 (5 : ZMod 783756198856822717807)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2927, 1), (36313, 1), (175568600093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2927, 1), (36313, 1), (175568600093, 1)] : List FactorBlock).map factorBlockValue).prod) = 783756198856822717807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_2927
      · exact prime_eightyBZ_36313
      · exact prime_eightyBZ_175568600093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 783756198856822717807) ^ 391878099428411358903 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 783756198856822717807) ^ 261252066285607572602 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 783756198856822717807) ^ 111965171265260388258 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 783756198856822717807) ^ 267767748157438578 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 783756198856822717807) ^ 21583350283832862 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 783756198856822717807) ^ 4464102342 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_830661152906838127513 : Nat.Prime 830661152906838127513 := by
  apply lucas_primality 830661152906838127513 (5 : ZMod 830661152906838127513)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (3146443761010750483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (3146443761010750483, 1)] : List FactorBlock).map factorBlockValue).prod) = 830661152906838127513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_3146443761010750483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 830661152906838127513) ^ 415330576453419063756 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 830661152906838127513) ^ 276887050968946042504 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 830661152906838127513) ^ 75514650264258011592 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 830661152906838127513) ^ 264 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2016711100521010861489 : Nat.Prime 2016711100521010861489 := by
  apply lucas_primality 2016711100521010861489 (13 : ZMod 2016711100521010861489)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (12964069, 1), (1080288773383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (12964069, 1), (1080288773383, 1)] : List FactorBlock).map factorBlockValue).prod) = 2016711100521010861489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_12964069
      · exact prime_eightyBZ_1080288773383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2016711100521010861489) ^ 1008355550260505430744 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 2016711100521010861489) ^ 672237033507003620496 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 2016711100521010861489) ^ 155561583367152 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (13 : ZMod 2016711100521010861489) ^ 1866825936 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2116798869474239910433 : Nat.Prime 2116798869474239910433 := by
  apply lucas_primality 2116798869474239910433 (10 : ZMod 2116798869474239910433)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (137, 1), (14631710831911081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (137, 1), (14631710831911081, 1)] : List FactorBlock).map factorBlockValue).prod) = 2116798869474239910433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_137
      · exact prime_eightyBZ_14631710831911081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2116798869474239910433) ^ 1058399434737119955216 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2116798869474239910433) ^ 705599623158079970144 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2116798869474239910433) ^ 192436260861294537312 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2116798869474239910433) ^ 15451086638498101536 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2116798869474239910433) ^ 144672 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2325733784059557542497 : Nat.Prime 2325733784059557542497 := by
  apply lucas_primality 2325733784059557542497 (17 : ZMod 2325733784059557542497)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (1987, 1), (1741778243148589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (1987, 1), (1741778243148589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2325733784059557542497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_1987
      · exact prime_eightyBZ_1741778243148589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2325733784059557542497) ^ 1162866892029778771248 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 2325733784059557542497) ^ 775244594686519180832 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 2325733784059557542497) ^ 332247683437079648928 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 2325733784059557542497) ^ 1170474979395851808 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 2325733784059557542497) ^ 1335264 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_10855915629486140701459 : Nat.Prime 10855915629486140701459 := by
  apply lucas_primality 10855915629486140701459 (3 : ZMod 10855915629486140701459)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (157, 1), (3841442190193255733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (157, 1), (3841442190193255733, 1)] : List FactorBlock).map factorBlockValue).prod) = 10855915629486140701459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_157
      · exact prime_eightyBZ_3841442190193255733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10855915629486140701459) ^ 5427957814743070350729 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 10855915629486140701459) ^ 3618638543162046900486 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 10855915629486140701459) ^ 69145959423478603194 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 10855915629486140701459) ^ 2826 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_11406058284900380441833 : Nat.Prime 11406058284900380441833 := by
  apply lucas_primality 11406058284900380441833 (5 : ZMod 11406058284900380441833)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1613, 1), (98212942454539337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1613, 1), (98212942454539337, 1)] : List FactorBlock).map factorBlockValue).prod) = 11406058284900380441833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_1613
      · exact prime_eightyBZ_98212942454539337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11406058284900380441833) ^ 5703029142450190220916 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11406058284900380441833) ^ 3802019428300126813944 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11406058284900380441833) ^ 7071331856726832264 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11406058284900380441833) ^ 116136 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_12954956313358877079781 : Nat.Prime 12954956313358877079781 := by
  apply lucas_primality 12954956313358877079781 (2 : ZMod 12954956313358877079781)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (37, 1), (277884090805638719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (37, 1), (277884090805638719, 1)] : List FactorBlock).map factorBlockValue).prod) = 12954956313358877079781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_37
      · exact prime_eightyBZ_277884090805638719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12954956313358877079781) ^ 6477478156679438539890 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12954956313358877079781) ^ 4318318771119625693260 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12954956313358877079781) ^ 2590991262671775415956 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12954956313358877079781) ^ 1850708044765553868540 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12954956313358877079781) ^ 350133954415104785940 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12954956313358877079781) ^ 46620 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_14672237434338221330893 : Nat.Prime 14672237434338221330893 := by
  apply lucas_primality 14672237434338221330893 (2 : ZMod 14672237434338221330893)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (101, 1), (9743, 1), (95577941275199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (101, 1), (9743, 1), (95577941275199, 1)] : List FactorBlock).map factorBlockValue).prod) = 14672237434338221330893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_101
      · exact prime_eightyBZ_9743
      · exact prime_eightyBZ_95577941275199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14672237434338221330893) ^ 7336118717169110665446 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14672237434338221330893) ^ 4890745811446073776964 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14672237434338221330893) ^ 1128633648795247794684 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14672237434338221330893) ^ 145269677567705161692 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14672237434338221330893) ^ 1505926042732035444 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14672237434338221330893) ^ 153510708 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_33425046773626392405049 : Nat.Prime 33425046773626392405049 := by
  apply lucas_primality 33425046773626392405049 (19 : ZMod 33425046773626392405049)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (157, 1), (806433284443794451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (157, 1), (806433284443794451, 1)] : List FactorBlock).map factorBlockValue).prod) = 33425046773626392405049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_157
      · exact prime_eightyBZ_806433284443794451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 33425046773626392405049) ^ 16712523386813196202524 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 33425046773626392405049) ^ 11141682257875464135016 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 33425046773626392405049) ^ 3038640615784217491368 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 33425046773626392405049) ^ 212898387093161735064 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 33425046773626392405049) ^ 41448 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_36810303440622843156763 : Nat.Prime 36810303440622843156763 := by
  apply lucas_primality 36810303440622843156763 (2 : ZMod 36810303440622843156763)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (23, 1), (523, 1), (2440295033985707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (23, 1), (523, 1), (2440295033985707, 1)] : List FactorBlock).map factorBlockValue).prod) = 36810303440622843156763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_23
      · exact prime_eightyBZ_523
      · exact prime_eightyBZ_2440295033985707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36810303440622843156763) ^ 18405151720311421578381 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36810303440622843156763) ^ 12270101146874281052254 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36810303440622843156763) ^ 3346391221874803923342 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36810303440622843156763) ^ 1937384391611728587198 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36810303440622843156763) ^ 1600447975679254050294 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36810303440622843156763) ^ 70382989370215761294 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36810303440622843156763) ^ 15084366 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_43672819035234101714431 : Nat.Prime 43672819035234101714431 := by
  apply lucas_primality 43672819035234101714431 (11 : ZMod 43672819035234101714431)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (13, 2), (19, 1), (41, 1), (1005247782883121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (13, 2), (19, 1), (41, 1), (1005247782883121, 1)] : List FactorBlock).map factorBlockValue).prod) = 43672819035234101714431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_13
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_41
      · exact prime_eightyBZ_1005247782883121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 43672819035234101714431) ^ 21836409517617050857215 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 43672819035234101714431) ^ 14557606345078033904810 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 43672819035234101714431) ^ 8734563807046820342886 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 43672819035234101714431) ^ 3970256275930372883130 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 43672819035234101714431) ^ 3359447618094930901110 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 43672819035234101714431) ^ 2298569422907057984970 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 43672819035234101714431) ^ 1065190708176441505230 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 43672819035234101714431) ^ 43444830 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_58892754033315082569419 : Nat.Prime 58892754033315082569419 := by
  apply lucas_primality 58892754033315082569419 (2 : ZMod 58892754033315082569419)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103651, 1), (120511, 1), (668527, 1), (3526247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103651, 1), (120511, 1), (668527, 1), (3526247, 1)] : List FactorBlock).map factorBlockValue).prod) = 58892754033315082569419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_103651
      · exact prime_eightyBZ_120511
      · exact prime_eightyBZ_668527
      · exact prime_eightyBZ_3526247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58892754033315082569419) ^ 29446377016657541284709 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 58892754033315082569419) ^ 568183172697948718 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 58892754033315082569419) ^ 488691937112090038 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 58892754033315082569419) ^ 88093306677688534 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 58892754033315082569419) ^ 16701256047382694 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_63821409711151710596449 : Nat.Prime 63821409711151710596449 := by
  apply lucas_primality 63821409711151710596449 (17 : ZMod 63821409711151710596449)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (101, 1), (41681, 1), (157919462118773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (101, 1), (41681, 1), (157919462118773, 1)] : List FactorBlock).map factorBlockValue).prod) = 63821409711151710596449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_101
      · exact prime_eightyBZ_41681
      · exact prime_eightyBZ_157919462118773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 63821409711151710596449) ^ 31910704855575855298224 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 63821409711151710596449) ^ 21273803237050570198816 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 63821409711151710596449) ^ 631895145654967431648 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 63821409711151710596449) ^ 1531187104703623008 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (17 : ZMod 63821409711151710596449) ^ 404138976 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_91100141038713432986207 : Nat.Prime 91100141038713432986207 := by
  apply lucas_primality 91100141038713432986207 (5 : ZMod 91100141038713432986207)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (10159, 1), (5293643409732911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (10159, 1), (5293643409732911, 1)] : List FactorBlock).map factorBlockValue).prod) = 91100141038713432986207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_10159
      · exact prime_eightyBZ_5293643409732911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 91100141038713432986207) ^ 45550070519356716493103 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 91100141038713432986207) ^ 13014305862673347569458 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 91100141038713432986207) ^ 8281831003519402998746 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 91100141038713432986207) ^ 8967431936087551234 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 91100141038713432986207) ^ 17209346 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_91779416909398754815157 : Nat.Prime 91779416909398754815157 := by
  apply lucas_primality 91779416909398754815157 (2 : ZMod 91779416909398754815157)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1861, 1), (796379, 1), (15481717209131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1861, 1), (796379, 1), (15481717209131, 1)] : List FactorBlock).map factorBlockValue).prod) = 91779416909398754815157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_1861
      · exact prime_eightyBZ_796379
      · exact prime_eightyBZ_15481717209131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 91779416909398754815157) ^ 45889708454699377407578 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 91779416909398754815157) ^ 49317257877162146596 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 91779416909398754815157) ^ 115245902904771164 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 91779416909398754815157) ^ 5928245276 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_180183096651716628884719 : Nat.Prime 180183096651716628884719 := by
  apply lucas_primality 180183096651716628884719 (6 : ZMod 180183096651716628884719)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (409, 1), (578143659561816571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (409, 1), (578143659561816571, 1)] : List FactorBlock).map factorBlockValue).prod) = 180183096651716628884719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_127
      · exact prime_eightyBZ_409
      · exact prime_eightyBZ_578143659561816571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 180183096651716628884719) ^ 90091548325858314442359 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 180183096651716628884719) ^ 60061032217238876294906 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 180183096651716628884719) ^ 1418764540564697865234 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 180183096651716628884719) ^ 440545468586104227102 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 180183096651716628884719) ^ 311658 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_404891119013625129607439 : Nat.Prime 404891119013625129607439 := by
  apply lucas_primality 404891119013625129607439 (7 : ZMod 404891119013625129607439)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1039816121, 1), (11452565586767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1039816121, 1), (11452565586767, 1)] : List FactorBlock).map factorBlockValue).prod) = 404891119013625129607439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_17
      · exact prime_eightyBZ_1039816121
      · exact prime_eightyBZ_11452565586767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 404891119013625129607439) ^ 202445559506812564803719 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 404891119013625129607439) ^ 23817124647860301741614 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 404891119013625129607439) ^ 389387229950078 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (7 : ZMod 404891119013625129607439) ^ 35353748114 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_527326888538279378907833 : Nat.Prime 527326888538279378907833 := by
  apply lucas_primality 527326888538279378907833 (3 : ZMod 527326888538279378907833)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (389, 1), (35831, 1), (4729131598665581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (389, 1), (35831, 1), (4729131598665581, 1)] : List FactorBlock).map factorBlockValue).prod) = 527326888538279378907833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_389
      · exact prime_eightyBZ_35831
      · exact prime_eightyBZ_4729131598665581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 527326888538279378907833) ^ 263663444269139689453916 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 527326888538279378907833) ^ 1355596114494291462488 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 527326888538279378907833) ^ 14717057535047288072 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 527326888538279378907833) ^ 111506072 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_867241433414870616182917 : Nat.Prime 867241433414870616182917 := by
  apply lucas_primality 867241433414870616182917 (5 : ZMod 867241433414870616182917)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (22643, 1), (17068022214899723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (22643, 1), (17068022214899723, 1)] : List FactorBlock).map factorBlockValue).prod) = 867241433414870616182917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_11
      · exact prime_eightyBZ_17
      · exact prime_eightyBZ_22643
      · exact prime_eightyBZ_17068022214899723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 867241433414870616182917) ^ 433620716707435308091458 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 867241433414870616182917) ^ 289080477804956872060972 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 867241433414870616182917) ^ 78840130310442783289356 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 867241433414870616182917) ^ 51014201965580624481348 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 867241433414870616182917) ^ 38300641850234978412 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (5 : ZMod 867241433414870616182917) ^ 50810892 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_1034297673226811628857881 : Nat.Prime 1034297673226811628857881 := by
  apply lucas_primality 1034297673226811628857881 (11 : ZMod 1034297673226811628857881)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (8546559743, 1), (144070455349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (8546559743, 1), (144070455349, 1)] : List FactorBlock).map factorBlockValue).prod) = 1034297673226811628857881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_8546559743
      · exact prime_eightyBZ_144070455349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1034297673226811628857881) ^ 517148836613405814428940 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1034297673226811628857881) ^ 344765891075603876285960 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1034297673226811628857881) ^ 206859534645362325771576 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1034297673226811628857881) ^ 147756810460973089836840 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1034297673226811628857881) ^ 121019182493160 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1034297673226811628857881) ^ 7179110184120 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_2998964764037852412990961 : Nat.Prime 2998964764037852412990961 := by
  apply lucas_primality 2998964764037852412990961 (26 : ZMod 2998964764037852412990961)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (17, 1), (19, 1), (38686335965400572923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (17, 1), (19, 1), (38686335965400572923, 1)] : List FactorBlock).map factorBlockValue).prod) = 2998964764037852412990961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_17
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_38686335965400572923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 2998964764037852412990961) ^ 1499482382018926206495480 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (26 : ZMod 2998964764037852412990961) ^ 999654921345950804330320 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (26 : ZMod 2998964764037852412990961) ^ 599792952807570482598192 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (26 : ZMod 2998964764037852412990961) ^ 176409692002226612528880 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (26 : ZMod 2998964764037852412990961) ^ 157840250738834337525840 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (26 : ZMod 2998964764037852412990961) ^ 77520 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_80153687057818465593990617 : Nat.Prime 80153687057818465593990617 := by
  apply lucas_primality 80153687057818465593990617 (3 : ZMod 80153687057818465593990617)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (527326888538279378907833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (527326888538279378907833, 1)] : List FactorBlock).map factorBlockValue).prod) = 80153687057818465593990617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_19
      · exact prime_eightyBZ_527326888538279378907833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 80153687057818465593990617) ^ 40076843528909232796995308 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 80153687057818465593990617) ^ 4218615108306235031262664 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 80153687057818465593990617) ^ 152 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_242516283918527665130535713 : Nat.Prime 242516283918527665130535713 := by
  apply lucas_primality 242516283918527665130535713 (3 : ZMod 242516283918527665130535713)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (4231, 1), (161984281, 1), (11057960359031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (4231, 1), (161984281, 1), (11057960359031, 1)] : List FactorBlock).map factorBlockValue).prod) = 242516283918527665130535713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_4231
      · exact prime_eightyBZ_161984281
      · exact prime_eightyBZ_11057960359031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 242516283918527665130535713) ^ 121258141959263832565267856 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 242516283918527665130535713) ^ 57318904258692428534752 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 242516283918527665130535713) ^ 1497159368929925152 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 242516283918527665130535713) ^ 21931375773152 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_271006735610962147280541341 : Nat.Prime 271006735610962147280541341 := by
  apply lucas_primality 271006735610962147280541341 (2 : ZMod 271006735610962147280541341)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (53, 1), (2647, 1), (4931, 1), (455529828574889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (53, 1), (2647, 1), (4931, 1), (455529828574889, 1)] : List FactorBlock).map factorBlockValue).prod) = 271006735610962147280541341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_5
      · exact prime_eightyBZ_43
      · exact prime_eightyBZ_53
      · exact prime_eightyBZ_2647
      · exact prime_eightyBZ_4931
      · exact prime_eightyBZ_455529828574889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 271006735610962147280541341) ^ 135503367805481073640270670 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271006735610962147280541341) ^ 54201347122192429456108268 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271006735610962147280541341) ^ 6302482223510747611175380 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271006735610962147280541341) ^ 5113334634169097118500780 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271006735610962147280541341) ^ 102382597510752605697220 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271006735610962147280541341) ^ 54959792255315787321140 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271006735610962147280541341) ^ 594926432060 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_305101131381373514196480413 : Nat.Prime 305101131381373514196480413 := by
  apply lucas_primality 305101131381373514196480413 (2 : ZMod 305101131381373514196480413)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (521, 1), (3593, 1), (695559779, 1), (58580682269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (521, 1), (3593, 1), (695559779, 1), (58580682269, 1)] : List FactorBlock).map factorBlockValue).prod) = 305101131381373514196480413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_521
      · exact prime_eightyBZ_3593
      · exact prime_eightyBZ_695559779
      · exact prime_eightyBZ_58580682269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 305101131381373514196480413) ^ 152550565690686757098240206 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 305101131381373514196480413) ^ 585606778083250507094972 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 305101131381373514196480413) ^ 84915427604056085220284 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 305101131381373514196480413) ^ 438641135662005428 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 305101131381373514196480413) ^ 5208220859913548 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_446138446831253723589193057 : Nat.Prime 446138446831253723589193057 := by
  apply lucas_primality 446138446831253723589193057 (19 : ZMod 446138446831253723589193057)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (30844194737, 1), (150669373198153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (30844194737, 1), (150669373198153, 1)] : List FactorBlock).map factorBlockValue).prod) = 446138446831253723589193057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_30844194737
      · exact prime_eightyBZ_150669373198153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 446138446831253723589193057) ^ 223069223415626861794596528 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 446138446831253723589193057) ^ 148712815610417907863064352 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 446138446831253723589193057) ^ 14464259827022688 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (19 : ZMod 446138446831253723589193057) ^ 2961042694752 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_583835498322381416054993383 : Nat.Prime 583835498322381416054993383 := by
  apply lucas_primality 583835498322381416054993383 (3 : ZMod 583835498322381416054993383)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (283, 1), (18452411, 1), (6211241815108723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (283, 1), (18452411, 1), (6211241815108723, 1)] : List FactorBlock).map factorBlockValue).prod) = 583835498322381416054993383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_283
      · exact prime_eightyBZ_18452411
      · exact prime_eightyBZ_6211241815108723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 583835498322381416054993383) ^ 291917749161190708027496691 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 583835498322381416054993383) ^ 194611832774127138684997794 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 583835498322381416054993383) ^ 2063022962269898996660754 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 583835498322381416054993383) ^ 31640065806163834962 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 583835498322381416054993383) ^ 93996581634 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_13511621532603684200129846863 : Nat.Prime 13511621532603684200129846863 := by
  apply lucas_primality 13511621532603684200129846863 (6 : ZMod 13511621532603684200129846863)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (940097, 1), (67227001, 1), (1549216026067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (940097, 1), (67227001, 1), (1549216026067, 1)] : List FactorBlock).map factorBlockValue).prod) = 13511621532603684200129846863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_23
      · exact prime_eightyBZ_940097
      · exact prime_eightyBZ_67227001
      · exact prime_eightyBZ_1549216026067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 13511621532603684200129846863) ^ 6755810766301842100064923431 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 13511621532603684200129846863) ^ 4503873844201228066709948954 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 13511621532603684200129846863) ^ 587461805765377573918688994 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 13511621532603684200129846863) ^ 14372582332039868439246 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 13511621532603684200129846863) ^ 200985040707136172862 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (6 : ZMod 13511621532603684200129846863) ^ 8721586470355386 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_15763558454704298233484821337 : Nat.Prime 15763558454704298233484821337 := by
  apply lucas_primality 15763558454704298233484821337 (3 : ZMod 15763558454704298233484821337)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (389, 1), (449, 1), (275698603, 1), (397279853483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (389, 1), (449, 1), (275698603, 1), (397279853483, 1)] : List FactorBlock).map factorBlockValue).prod) = 15763558454704298233484821337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_103
      · exact prime_eightyBZ_389
      · exact prime_eightyBZ_449
      · exact prime_eightyBZ_275698603
      · exact prime_eightyBZ_397279853483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15763558454704298233484821337) ^ 7881779227352149116742410668 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15763558454704298233484821337) ^ 153044256841789303237716712 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15763558454704298233484821337) ^ 40523286515949352785308024 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15763558454704298233484821337) ^ 35108148006022935932037464 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15763558454704298233484821337) ^ 57176780307096072712 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15763558454704298233484821337) ^ 39678726007632392 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_31527116909408596466969642693 : Nat.Prime 31527116909408596466969642693 := by
  apply lucas_primality 31527116909408596466969642693 (2 : ZMod 31527116909408596466969642693)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (2437, 1), (22817, 1), (249677, 1), (434407, 1), (26670967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (2437, 1), (22817, 1), (249677, 1), (434407, 1), (26670967, 1)] : List FactorBlock).map factorBlockValue).prod) = 31527116909408596466969642693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_2437
      · exact prime_eightyBZ_22817
      · exact prime_eightyBZ_249677
      · exact prime_eightyBZ_434407
      · exact prime_eightyBZ_26670967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31527116909408596466969642693) ^ 15763558454704298233484821346 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31527116909408596466969642693) ^ 4503873844201228066709948956 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31527116909408596466969642693) ^ 12936855522941566051280116 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31527116909408596466969642693) ^ 1381738042223280732215876 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31527116909408596466969642693) ^ 126271610558475936778196 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31527116909408596466969642693) ^ 72575066491581849433756 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31527116909408596466969642693) ^ 1182076259530019907676 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide

private theorem prime_eightyBZ_47290675364112894700454464039 : Nat.Prime 47290675364112894700454464039 := by
  apply lucas_primality 47290675364112894700454464039 (3 : ZMod 47290675364112894700454464039)
  · rw [← eightyBZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (2437, 1), (22817, 1), (249677, 1), (434407, 1), (26670967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (2437, 1), (22817, 1), (249677, 1), (434407, 1), (26670967, 1)] : List FactorBlock).map factorBlockValue).prod) = 47290675364112894700454464039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyBZ_2
      · exact prime_eightyBZ_3
      · exact prime_eightyBZ_7
      · exact prime_eightyBZ_2437
      · exact prime_eightyBZ_22817
      · exact prime_eightyBZ_249677
      · exact prime_eightyBZ_434407
      · exact prime_eightyBZ_26670967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47290675364112894700454464039) ^ 23645337682056447350227232019 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 47290675364112894700454464039) ^ 15763558454704298233484821346 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 47290675364112894700454464039) ^ 6755810766301842100064923434 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 47290675364112894700454464039) ^ 19405283284412349076920174 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 47290675364112894700454464039) ^ 2072607063334921098323814 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 47290675364112894700454464039) ^ 189407415837713905167294 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 47290675364112894700454464039) ^ 108862599737372774150634 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide
    · change (3 : ZMod 47290675364112894700454464039) ^ 1773114389295029861514 ≠ 1
      rw [← eightyBZFastPow_eq_pow]
      decide


private theorem phi_eightyBZ_94581350728225789400908928000 : Nat.totient 94581350728225789400908928000 = 37497739022233995279581184000 := by
  rw [← show ((([(2, 10), (5, 3), (113, 1), (1361936311, 1), (4801316108207, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_5, prime_eightyBZ_113, prime_eightyBZ_1361936311, prime_eightyBZ_4801316108207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928001 : Nat.totient 94581350728225789400908928001 = 58616294260171523083750563840 := by
  rw [← show ((([(3, 2), (19, 1), (59, 1), (577, 1), (11597, 1), (1400992852343860861, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_19, prime_eightyBZ_59, prime_eightyBZ_577, prime_eightyBZ_11597, prime_eightyBZ_1400992852343860861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928002 : Nat.totient 94581350728225789400908928002 = 47261283369620151408469972992 := by
  rw [← show ((([(2, 1), (1609, 1), (72854233, 1), (403426740935475233, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_1609, prime_eightyBZ_72854233, prime_eightyBZ_403426740935475233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928003 : Nat.totient 94581350728225789400908928003 = 85871625573375784480617158880 := by
  rw [← show ((([(11, 1), (773, 1), (457679, 1), (24303697274761091419, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_11, prime_eightyBZ_773, prime_eightyBZ_457679, prime_eightyBZ_24303697274761091419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928004 : Nat.totient 94581350728225789400908928004 = 30793887124498596617070945792 := by
  rw [← show ((([(2, 2), (3, 1), (43, 1), (750713, 1), (244164136406017891913, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_43, prime_eightyBZ_750713, prime_eightyBZ_244164136406017891913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928005 : Nat.totient 94581350728225789400908928005 = 69844672726882177194223515648 := by
  rw [← show ((([(5, 1), (13, 1), (4098469, 1), (355034453965899459233, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_5, prime_eightyBZ_13, prime_eightyBZ_4098469, prime_eightyBZ_355034453965899459233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928006 : Nat.totient 94581350728225789400908928006 = 40021759508133705693763578336 := by
  rw [← show ((([(2, 1), (7, 1), (79, 1), (7227007, 1), (11832919489147351093, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_7, prime_eightyBZ_79, prime_eightyBZ_7227007, prime_eightyBZ_11832919489147351093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928007 : Nat.totient 94581350728225789400908928007 = 63054232832458445092879096832 := by
  rw [← show ((([(3, 1), (65771177, 1), (2304220469, 1), (208029350513, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_65771177, prime_eightyBZ_2304220469, prime_eightyBZ_208029350513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928008 : Nat.totient 94581350728225789400908928008 = 47289601226627433296414496000 := by
  rw [← show ((([(2, 3), (44501, 1), (4427623, 1), (65955503, 1), (909754229, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_44501, prime_eightyBZ_4427623, prime_eightyBZ_65955503, prime_eightyBZ_909754229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928009 : Nat.totient 94581350728225789400908928009 = 94310343992614827253628386320 := by
  rw [← show ((([(349, 1), (271006735610962147280541341, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_349, prime_eightyBZ_271006735610962147280541341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928010 : Nat.totient 94581350728225789400908928010 = 25220075642448380858607206400 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (15601, 1), (20783177, 1), (3241146259241857, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_5, prime_eightyBZ_15601, prime_eightyBZ_20783177, prime_eightyBZ_3241146259241857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928011 : Nat.totient 94581350728225789400908928011 = 90405698258865036359228775936 := by
  rw [← show ((([(23, 1), (1427, 1), (4459577, 1), (63341087, 1), (10201746409, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_23, prime_eightyBZ_1427, prime_eightyBZ_4459577, prime_eightyBZ_63341087, prime_eightyBZ_10201746409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928012 : Nat.totient 94581350728225789400908928012 = 47124069579385142383196344320 := by
  rw [← show ((([(2, 2), (293, 1), (10597, 1), (62273, 1), (122291191827167291, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_293, prime_eightyBZ_10597, prime_eightyBZ_62273, prime_eightyBZ_122291191827167291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928013 : Nat.totient 94581350728225789400908928013 = 54022645596709903358862631872 := by
  rw [← show ((([(3, 1), (7, 1), (2267, 1), (32429807437, 1), (61261880972807, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_7, prime_eightyBZ_2267, prime_eightyBZ_32429807437, prime_eightyBZ_61261880972807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928014 : Nat.totient 94581350728225789400908928014 = 41506602445271295349431321600 := by
  rw [← show ((([(2, 1), (11, 1), (29, 1), (17383, 1), (815653, 1), (2679337, 1), (3902359931, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_11, prime_eightyBZ_29, prime_eightyBZ_17383, prime_eightyBZ_815653, prime_eightyBZ_2679337, prime_eightyBZ_3902359931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928015 : Nat.totient 94581350728225789400908928015 = 70649289604981573354999259136 := by
  rw [← show ((([(5, 1), (17, 1), (127, 1), (16987, 1), (24051089, 1), (21445265783719, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_5, prime_eightyBZ_17, prime_eightyBZ_127, prime_eightyBZ_16987, prime_eightyBZ_24051089, prime_eightyBZ_21445265783719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928016 : Nat.totient 94581350728225789400908928016 = 31071412737591312773997821952 := by
  rw [← show ((([(2, 4), (3, 1), (103, 1), (389, 1), (449, 1), (275698603, 1), (397279853483, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_103, prime_eightyBZ_389, prime_eightyBZ_449, prime_eightyBZ_275698603, prime_eightyBZ_397279853483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928017 : Nat.totient 94581350728225789400908928017 = 94580622567366668484285006000 := by
  rw [← show ((([(148501, 1), (1036459, 1), (614502998939847463, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_148501, prime_eightyBZ_1036459, prime_eightyBZ_614502998939847463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928018 : Nat.totient 94581350728225789400908928018 = 43616943528166525494540522240 := by
  rw [← show ((([(2, 1), (13, 1), (1213, 1), (2998964764037852412990961, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_13, prime_eightyBZ_1213, prime_eightyBZ_2998964764037852412990961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928019 : Nat.totient 94581350728225789400908928019 = 63052652491900008784583922432 := by
  rw [← show ((([(3, 3), (39877, 1), (579391369, 1), (151616772713069, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_39877, prime_eightyBZ_579391369, prime_eightyBZ_151616772713069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928020 : Nat.totient 94581350728225789400908928020 = 29971863938817928495281576960 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (19, 1), (41, 1), (867241433414870616182917, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_5, prime_eightyBZ_7, prime_eightyBZ_19, prime_eightyBZ_41, prime_eightyBZ_867241433414870616182917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928021 : Nat.totient 94581350728225789400908928021 = 94579078400455979519077794048 := by
  rw [← show ((([(41957, 1), (5230297, 1), (430997482444348249, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_41957, prime_eightyBZ_5230297, prime_eightyBZ_430997482444348249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928022 : Nat.totient 94581350728225789400908928022 = 31527116909408596466969642672 := by
  rw [← show ((([(2, 1), (3, 1), (15763558454704298233484821337, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_15763558454704298233484821337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928023 : Nat.totient 94581350728225789400908928023 = 94581350728220877349394187000 := by
  rw [← show ((([(19331034977251, 1), (4892720479763773, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_19331034977251, prime_eightyBZ_4892720479763773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928024 : Nat.totient 94581350728225789400908928024 = 46500725056501700427572357760 := by
  rw [← show ((([(2, 3), (61, 1), (4943, 1), (8803, 1), (4454145273740651387, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_61, prime_eightyBZ_4943, prime_eightyBZ_8803, prime_eightyBZ_4454145273740651387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928025 : Nat.totient 94581350728225789400908928025 = 45832316106728712891187200000 := by
  rw [← show ((([(3, 1), (5, 2), (11, 1), (3539, 1), (4801, 1), (17519, 1), (247241, 1), (1557792077, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_5, prime_eightyBZ_11, prime_eightyBZ_3539, prime_eightyBZ_4801, prime_eightyBZ_17519, prime_eightyBZ_247241, prime_eightyBZ_1557792077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928026 : Nat.totient 94581350728225789400908928026 = 46133776489232796417012960000 := by
  rw [← show ((([(2, 1), (47, 1), (557, 1), (1051, 1), (1951, 1), (103862573, 1), (8482100239, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_47, prime_eightyBZ_557, prime_eightyBZ_1051, prime_eightyBZ_1951, prime_eightyBZ_103862573, prime_eightyBZ_8482100239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928027 : Nat.totient 94581350728225789400908928027 = 81069727061486672738053796160 := by
  rw [← show ((([(7, 2), (37987153, 1), (50812748391931662491, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_7, prime_eightyBZ_37987153, prime_eightyBZ_50812748391931662491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928028 : Nat.totient 94581350728225789400908928028 = 31527113374874236383308968896 := by
  rw [← show ((([(2, 2), (3, 2), (8919737, 1), (294544530006962803079, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_8919737, prime_eightyBZ_294544530006962803079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928029 : Nat.totient 94581350728225789400908928029 = 91948947105877299609321443328 := by
  rw [← show ((([(37, 1), (2027, 1), (3049, 1), (157427, 1), (2627322562457377, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_37, prime_eightyBZ_2027, prime_eightyBZ_3049, prime_eightyBZ_157427, prime_eightyBZ_2627322562457377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928030 : Nat.totient 94581350728225789400908928030 = 36612135765764821703577649440 := by
  rw [← show ((([(2, 1), (5, 1), (31, 1), (305101131381373514196480413, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_5, prime_eightyBZ_31, prime_eightyBZ_305101131381373514196480413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928031 : Nat.totient 94581350728225789400908928031 = 57105408010050477987647796864 := by
  rw [← show ((([(3, 1), (13, 1), (53, 1), (182339, 1), (250948998396339376087, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_13, prime_eightyBZ_53, prime_eightyBZ_182339, prime_eightyBZ_250948998396339376087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928032 : Nat.totient 94581350728225789400908928032 = 43738985588038771505158656000 := by
  rw [← show ((([(2, 5), (17, 1), (71, 1), (431, 1), (1063, 1), (5344877165671129231, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_17, prime_eightyBZ_71, prime_eightyBZ_431, prime_eightyBZ_1063, prime_eightyBZ_5344877165671129231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928033 : Nat.totient 94581350728225789400908928033 = 93563463925794637548219801600 := by
  rw [← show ((([(97, 1), (3911, 1), (4957, 1), (11141587, 1), (4514191586161, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_97, prime_eightyBZ_3911, prime_eightyBZ_4957, prime_eightyBZ_11141587, prime_eightyBZ_4514191586161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928034 : Nat.totient 94581350728225789400908928034 = 25848291573792320060279808000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (23, 1), (940097, 1), (67227001, 1), (1549216026067, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_7, prime_eightyBZ_23, prime_eightyBZ_940097, prime_eightyBZ_67227001, prime_eightyBZ_1549216026067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928035 : Nat.totient 94581350728225789400908928035 = 75665077447555836093339729600 := by
  rw [← show ((([(5, 1), (24135401, 1), (783756198856822717807, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_5, prime_eightyBZ_24135401, prime_eightyBZ_783756198856822717807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928036 : Nat.totient 94581350728225789400908928036 = 42598946249133999294579609600 := by
  rw [← show ((([(2, 2), (11, 1), (179, 1), (281, 1), (163417, 1), (261514787356833193, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_11, prime_eightyBZ_179, prime_eightyBZ_281, prime_eightyBZ_163417, prime_eightyBZ_261514787356833193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928037 : Nat.totient 94581350728225789400908928037 = 63051235922002595211419204736 := by
  rw [← show ((([(3, 2), (21149, 1), (4372477, 1), (31045307, 1), (3660578063, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_21149, prime_eightyBZ_4372477, prime_eightyBZ_31045307, prime_eightyBZ_3660578063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928038 : Nat.totient 94581350728225789400908928038 = 47290638553809454077610022544 := by
  rw [← show ((([(2, 1), (1284713, 1), (36810303440622843156763, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_1284713, prime_eightyBZ_36810303440622843156763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928039 : Nat.totient 94581350728225789400908928039 = 89589284756537539886818440480 := by
  rw [← show ((([(19, 1), (10631, 1), (15797, 1), (29641704584310183983, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_19, prime_eightyBZ_10631, prime_eightyBZ_15797, prime_eightyBZ_29641704584310183983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928040 : Nat.totient 94581350728225789400908928040 = 25221224015928978350491406592 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (53719, 1), (14672237434338221330893, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_5, prime_eightyBZ_53719, prime_eightyBZ_14672237434338221330893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928041 : Nat.totient 94581350728225789400908928041 = 81069729195622105200779081172 := by
  rw [← show ((([(7, 1), (13511621532603684200129846863, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_7, prime_eightyBZ_13511621532603684200129846863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928042 : Nat.totient 94581350728225789400908928042 = 47290495181016242983825316844 := by
  rw [← show ((([(2, 1), (262459, 1), (180183096651716628884719, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_262459, prime_eightyBZ_180183096651716628884719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928043 : Nat.totient 94581350728225789400908928043 = 60879949747855683191486883360 := by
  rw [← show ((([(3, 1), (29, 1), (416487571, 1), (2610262677906899359, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_29, prime_eightyBZ_416487571, prime_eightyBZ_2610262677906899359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928044 : Nat.totient 94581350728225789400908928044 = 43588417680653814005891040000 := by
  rw [← show ((([(2, 2), (13, 1), (991, 1), (2131, 1), (17965509301, 1), (47940828007, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_13, prime_eightyBZ_991, prime_eightyBZ_2131, prime_eightyBZ_17965509301, prime_eightyBZ_47940828007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928045 : Nat.totient 94581350728225789400908928045 = 75660943391887724274211637760 := by
  rw [← show ((([(5, 1), (18289, 1), (1034297673226811628857881, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_5, prime_eightyBZ_18289, prime_eightyBZ_1034297673226811628857881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928046 : Nat.totient 94581350728225789400908928046 = 31527116909408596466969642628 := by
  rw [← show ((([(2, 1), (3, 4), (583835498322381416054993383, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_583835498322381416054993383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928047 : Nat.totient 94581350728225789400908928047 = 83419480933964780505600510720 := by
  rw [← show ((([(11, 1), (43, 1), (149, 1), (267193, 1), (5022651282738255427, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_11, prime_eightyBZ_43, prime_eightyBZ_149, prime_eightyBZ_267193, prime_eightyBZ_5022651282738255427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928048 : Nat.totient 94581350728225789400908928048 = 40528740545521564678274827008 := by
  rw [← show ((([(2, 4), (7, 1), (6619, 1), (1129495957, 1), (112956292012163, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_7, prime_eightyBZ_6619, prime_eightyBZ_1129495957, prime_eightyBZ_112956292012163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928049 : Nat.totient 94581350728225789400908928049 = 59345161068029218408401416448 := by
  rw [← show ((([(3, 1), (17, 1), (342618743, 1), (5412827893040110093, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_17, prime_eightyBZ_342618743, prime_eightyBZ_5412827893040110093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928050 : Nat.totient 94581350728225789400908928050 = 36781944485802027502161346560 := by
  rw [← show ((([(2, 1), (5, 2), (67, 1), (163, 1), (173, 1), (857, 1), (163997, 1), (7123776276073, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_5, prime_eightyBZ_67, prime_eightyBZ_163, prime_eightyBZ_173, prime_eightyBZ_857, prime_eightyBZ_163997, prime_eightyBZ_7123776276073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928051 : Nat.totient 94581350728225789400908928051 = 93973257584009454349016398080 := by
  rw [← show ((([(157, 1), (16759, 1), (2905163, 1), (3897161, 1), (3174964739, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_157, prime_eightyBZ_16759, prime_eightyBZ_2905163, prime_eightyBZ_3897161, prime_eightyBZ_3174964739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928052 : Nat.totient 94581350728225789400908928052 = 31490063318760959596189040640 := by
  rw [← show ((([(2, 2), (3, 1), (1231, 1), (2753, 1), (2325733784059557542497, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_1231, prime_eightyBZ_2753, prime_eightyBZ_2325733784059557542497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928053 : Nat.totient 94581350728225789400908928053 = 94581258948808880002153082368 := by
  rw [← show ((([(1030529, 1), (91779416909398754815157, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_1030529, prime_eightyBZ_91779416909398754815157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928054 : Nat.totient 94581350728225789400908928054 = 47290648461006263553247056192 := by
  rw [← show ((([(2, 1), (2173337, 1), (9194023, 1), (2366698070428277, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_2173337, prime_eightyBZ_9194023, prime_eightyBZ_2366698070428277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928055 : Nat.totient 94581350728225789400908928055 = 43237069289125770855673096704 := by
  rw [← show ((([(3, 2), (5, 1), (7, 1), (361469, 1), (830661152906838127513, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_5, prime_eightyBZ_7, prime_eightyBZ_361469, prime_eightyBZ_830661152906838127513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928056 : Nat.totient 94581350728225789400908928056 = 46606389669202648622591029248 := by
  rw [← show ((([(2, 3), (73, 1), (1279, 1), (76139180393, 1), (1663082994697, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_73, prime_eightyBZ_1279, prime_eightyBZ_76139180393, prime_eightyBZ_1663082994697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928057 : Nat.totient 94581350728225789400908928057 = 83509952648842929881278632960 := by
  rw [← show ((([(13, 1), (23, 1), (38878481, 1), (232730557, 1), (34960016279, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_13, prime_eightyBZ_23, prime_eightyBZ_38878481, prime_eightyBZ_232730557, prime_eightyBZ_34960016279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928058 : Nat.totient 94581350728225789400908928058 = 27030780604542200203908622080 := by
  rw [← show ((([(2, 1), (3, 1), (11, 3), (19, 1), (223, 1), (23572321933, 1), (118581073693, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_11, prime_eightyBZ_19, prime_eightyBZ_223, prime_eightyBZ_23572321933, prime_eightyBZ_118581073693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928059 : Nat.totient 94581350728225789400908928059 = 94493312421799044182982658560 := by
  rw [← show ((([(1093, 1), (62819, 1), (268629457, 1), (5127913575461, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_1093, prime_eightyBZ_62819, prime_eightyBZ_268629457, prime_eightyBZ_5127913575461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928060 : Nat.totient 94581350728225789400908928060 = 37191310794827768035611645824 := by
  rw [← show ((([(2, 2), (5, 1), (59, 1), (80153687057818465593990617, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_5, prime_eightyBZ_59, prime_eightyBZ_80153687057818465593990617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928061 : Nat.totient 94581350728225789400908928061 = 59531928074281270563736560000 := by
  rw [← show ((([(3, 1), (31, 1), (41, 1), (451029527651, 1), (54996332856947, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_31, prime_eightyBZ_41, prime_eightyBZ_451029527651, prime_eightyBZ_54996332856947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928062 : Nat.totient 94581350728225789400908928062 = 40517534574515393515816600128 := by
  rw [← show ((([(2, 1), (7, 1), (2339, 1), (1582391579, 1), (1825295955014393, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_7, prime_eightyBZ_2339, prime_eightyBZ_1582391579, prime_eightyBZ_1825295955014393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928063 : Nat.totient 94581350728225789400908928063 = 94581344928572024515406998560 := by
  rw [← show ((([(16350221, 1), (6375285487, 1), (907365468469, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_16350221, prime_eightyBZ_6375285487, prime_eightyBZ_907365468469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928064 : Nat.totient 94581350728225789400908928064 = 31526592013663457150411596800 := by
  rw [← show ((([(2, 6), (3, 2), (60091, 1), (131621999, 1), (20760849245221, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_60091, prime_eightyBZ_131621999, prime_eightyBZ_20760849245221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928065 : Nat.totient 94581350728225789400908928065 = 75641451126505873655216040000 := by
  rw [← show ((([(5, 1), (3251, 1), (213043, 1), (27311859462347212741, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_5, prime_eightyBZ_3251, prime_eightyBZ_213043, prime_eightyBZ_27311859462347212741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928066 : Nat.totient 94581350728225789400908928066 = 43305928473320624805641773056 := by
  rw [← show ((([(2, 1), (17, 1), (37, 1), (2931402378973, 1), (25647759631649, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_17, prime_eightyBZ_37, prime_eightyBZ_2931402378973, prime_eightyBZ_25647759631649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928067 : Nat.totient 94581350728225789400908928067 = 62778733515449344977678477312 := by
  rw [← show ((([(3, 1), (257, 1), (2083, 1), (58892754033315082569419, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_257, prime_eightyBZ_2083, prime_eightyBZ_58892754033315082569419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928068 : Nat.totient 94581350728225789400908928068 = 47290675337569172601832739912 := by
  rw [← show ((([(2, 2), (1781614319, 1), (13271861047529247743, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_1781614319, prime_eightyBZ_13271861047529247743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928069 : Nat.totient 94581350728225789400908928069 = 72871666692629917999208192640 := by
  rw [← show ((([(7, 1), (11, 1), (89, 1), (1269391755367, 1), (10872492252119, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_7, prime_eightyBZ_11, prime_eightyBZ_89, prime_eightyBZ_1269391755367, prime_eightyBZ_10872492252119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928070 : Nat.totient 94581350728225789400908928070 = 23281563256178655852531428352 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (13, 1), (242516283918527665130535713, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_5, prime_eightyBZ_13, prime_eightyBZ_242516283918527665130535713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928071 : Nat.totient 94581350728225789400908928071 = 93859346957161838820768000000 := by
  rw [← show ((([(131, 1), (14309201, 1), (43295341, 1), (1165407121201, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_131, prime_eightyBZ_14309201, prime_eightyBZ_43295341, prime_eightyBZ_1165407121201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928072 : Nat.totient 94581350728225789400908928072 = 45109842390614379830788546560 := by
  rw [← show ((([(2, 3), (29, 1), (83, 1), (60555515407, 1), (81112115744641, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_29, prime_eightyBZ_83, prime_eightyBZ_60555515407, prime_eightyBZ_81112115744641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928073 : Nat.totient 94581350728225789400908928073 = 61712654375847953131268572368 := by
  rw [← show ((([(3, 3), (47, 1), (5577704653919, 1), (13362520230043, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_47, prime_eightyBZ_5577704653919, prime_eightyBZ_13362520230043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928074 : Nat.totient 94581350728225789400908928074 = 47251299281205627845620891200 := by
  rw [← show ((([(2, 1), (1201, 1), (273990374299, 1), (143713379841263, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_1201, prime_eightyBZ_273990374299, prime_eightyBZ_143713379841263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928075 : Nat.totient 94581350728225789400908928075 = 75408663855412168877351734560 := by
  rw [← show ((([(5, 2), (563, 1), (619, 1), (10855915629486140701459, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_5, prime_eightyBZ_563, prime_eightyBZ_619, prime_eightyBZ_10855915629486140701459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928076 : Nat.totient 94581350728225789400908928076 = 27010799095897957389463830528 := by
  rw [← show ((([(2, 2), (3, 1), (7, 2), (2437, 1), (22817, 1), (249677, 1), (434407, 1), (26670967, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_7, prime_eightyBZ_2437, prime_eightyBZ_22817, prime_eightyBZ_249677, prime_eightyBZ_434407, prime_eightyBZ_26670967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928077 : Nat.totient 94581350728225789400908928077 = 89603384899413344950356012864 := by
  rw [← show ((([(19, 1), (88620975439, 1), (56171417693634097, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_19, prime_eightyBZ_88620975439, prime_eightyBZ_56171417693634097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928078 : Nat.totient 94581350728225789400908928078 = 47290675364112894700454464038 := by
  rw [← show ((([(2, 1), (47290675364112894700454464039, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_47290675364112894700454464039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928079 : Nat.totient 94581350728225789400908928079 = 63054233818817192933939285384 := by
  rw [← show ((([(3, 1), (31527116909408596466969642693, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_31527116909408596466969642693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928080 : Nat.totient 94581350728225789400908928080 = 32590404476853096063376243200 := by
  rw [← show ((([(2, 4), (5, 1), (11, 1), (23, 1), (107, 1), (43672819035234101714431, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_5, prime_eightyBZ_11, prime_eightyBZ_23, prime_eightyBZ_107, prime_eightyBZ_43672819035234101714431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928081 : Nat.totient 94581350728225789400908928081 = 94074034342431844453376280960 := by
  rw [← show ((([(191, 1), (7759, 1), (63821409711151710596449, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_191, prime_eightyBZ_7759, prime_eightyBZ_63821409711151710596449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928082 : Nat.totient 94581350728225789400908928082 = 31507070533812079214469685056 := by
  rw [← show ((([(2, 1), (3, 2), (2969, 1), (3343, 1), (529403042215107284647, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_2969, prime_eightyBZ_3343, prime_eightyBZ_529403042215107284647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928083 : Nat.totient 94581350728225789400908928083 = 69965185365554422396165286400 := by
  rw [← show ((([(7, 1), (13, 1), (17, 1), (151, 1), (404891119013625129607439, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_7, prime_eightyBZ_13, prime_eightyBZ_17, prime_eightyBZ_151, prime_eightyBZ_404891119013625129607439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928084 : Nat.totient 94581350728225789400908928084 = 46398398470450387253276077824 := by
  rw [← show ((([(2, 2), (53, 1), (446138446831253723589193057, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_53, prime_eightyBZ_446138446831253723589193057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928085 : Nat.totient 94581350728225789400908928085 = 48503356437215635786696320000 := by
  rw [← show ((([(3, 1), (5, 1), (61, 1), (79, 1), (101, 1), (12954956313358877079781, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_5, prime_eightyBZ_61, prime_eightyBZ_79, prime_eightyBZ_101, prime_eightyBZ_12954956313358877079781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928086 : Nat.totient 94581350728225789400908928086 = 46709371494068369880345552000 := by
  rw [← show ((([(2, 1), (211, 1), (229, 1), (311, 1), (48247, 1), (65226920572665541, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_211, prime_eightyBZ_229, prime_eightyBZ_311, prime_eightyBZ_48247, prime_eightyBZ_65226920572665541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928087 : Nat.totient 94581350728225789400908928087 = 94576160509692718510851270912 := by
  rw [← show ((([(18223, 1), (1625821997617, 1), (3192365740457, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_18223, prime_eightyBZ_1625821997617, prime_eightyBZ_3192365740457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928088 : Nat.totient 94581350728225789400908928088 = 31467895908800376354707911680 := by
  rw [← show ((([(2, 3), (3, 1), (541, 1), (33289, 1), (684123959, 1), (319861121507, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_541, prime_eightyBZ_33289, prime_eightyBZ_684123959, prime_eightyBZ_319861121507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928089 : Nat.totient 94581350728225789400908928089 = 94578621810646678536333767136 := by
  rw [← show ((([(65063, 1), (74167, 1), (19600209576387532409, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_65063, prime_eightyBZ_74167, prime_eightyBZ_19600209576387532409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928090 : Nat.totient 94581350728225789400908928090 = 31671721817686288015758904320 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (43, 1), (15581, 1), (2016711100521010861489, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_5, prime_eightyBZ_7, prime_eightyBZ_43, prime_eightyBZ_15581, prime_eightyBZ_2016711100521010861489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928091 : Nat.totient 94581350728225789400908928091 = 57316564735916943497601366960 := by
  rw [← show ((([(3, 2), (11, 1), (10487, 1), (91100141038713432986207, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_11, prime_eightyBZ_10487, prime_eightyBZ_91100141038713432986207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928092 : Nat.totient 94581350728225789400908928092 = 45759115290454296325357579200 := by
  rw [← show ((([(2, 2), (31, 1), (7559, 1), (2077286557, 1), (48576147748091, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_31, prime_eightyBZ_7559, prime_eightyBZ_2077286557, prime_eightyBZ_48576147748091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928093 : Nat.totient 94581350728225789400908928093 = 94492780253798871694793395248 := by
  rw [← show ((([(1069, 1), (1005239, 1), (88015361541674364823, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_1069, prime_eightyBZ_1005239, prime_eightyBZ_88015361541674364823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928094 : Nat.totient 94581350728225789400908928094 = 31527116909385542102634069528 := by
  rw [← show ((([(2, 1), (3, 1), (1367674142543, 1), (11525814493644043, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_1367674142543, prime_eightyBZ_11525814493644043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928095 : Nat.totient 94581350728225789400908928095 = 75432575957223286335155364864 := by
  rw [← show ((([(5, 1), (433, 1), (1307, 1), (33425046773626392405049, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_5, prime_eightyBZ_433, prime_eightyBZ_1307, prime_eightyBZ_33425046773626392405049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928096 : Nat.totient 94581350728225789400908928096 = 41348092758687604133320310784 := by
  rw [← show ((([(2, 5), (13, 1), (19, 1), (5653, 1), (2116798869474239910433, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_13, prime_eightyBZ_19, prime_eightyBZ_5653, prime_eightyBZ_2116798869474239910433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928097 : Nat.totient 94581350728225789400908928097 = 53857515915226759952204372736 := by
  rw [← show ((([(3, 1), (7, 1), (499, 1), (683, 1), (31957, 1), (19122899, 1), (21624458147, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_3, prime_eightyBZ_7, prime_eightyBZ_499, prime_eightyBZ_683, prime_eightyBZ_31957, prime_eightyBZ_19122899, prime_eightyBZ_21624458147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928098 : Nat.totient 94581350728225789400908928098 = 47225574472155815093820161040 := by
  rw [← show ((([(2, 1), (727, 1), (911341, 1), (71377313242425837107, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_727, prime_eightyBZ_911341, prime_eightyBZ_71377313242425837107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928099 : Nat.totient 94581350728225789400908928099 = 94581339322167504500520194064 := by
  rw [← show ((([(8292203, 1), (11406058284900380441833, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_8292203, prime_eightyBZ_11406058284900380441833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928100 : Nat.totient 94581350728225789400908928100 = 23520284071619094059951185920 := by
  rw [← show ((([(2, 2), (3, 3), (5, 2), (17, 1), (109, 1), (1412604227, 1), (13382764233413, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_2, prime_eightyBZ_3, prime_eightyBZ_5, prime_eightyBZ_17, prime_eightyBZ_109, prime_eightyBZ_1412604227, prime_eightyBZ_13382764233413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyBZ_94581350728225789400908928101 : Nat.totient 94581350728225789400908928101 = 90653204860893136789175761920 := by
  rw [← show ((([(29, 1), (137, 1), (682819, 1), (4920841, 1), (7085035279603, 1)] : List FactorBlock).map factorBlockValue).prod) = 94581350728225789400908928101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyBZ_29, prime_eightyBZ_137, prime_eightyBZ_682819, prime_eightyBZ_4920841, prime_eightyBZ_7085035279603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64EightyBZ : certifiedKill 1 94581350728225789400908927999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_eightyBZ_94581350728225789400908928000, phi_eightyBZ_94581350728225789400908928001, phi_eightyBZ_94581350728225789400908928002,
    phi_eightyBZ_94581350728225789400908928003, phi_eightyBZ_94581350728225789400908928004, phi_eightyBZ_94581350728225789400908928005,
    phi_eightyBZ_94581350728225789400908928006, phi_eightyBZ_94581350728225789400908928007, phi_eightyBZ_94581350728225789400908928008,
    phi_eightyBZ_94581350728225789400908928009, phi_eightyBZ_94581350728225789400908928010, phi_eightyBZ_94581350728225789400908928011,
    phi_eightyBZ_94581350728225789400908928012, phi_eightyBZ_94581350728225789400908928013, phi_eightyBZ_94581350728225789400908928014,
    phi_eightyBZ_94581350728225789400908928015, phi_eightyBZ_94581350728225789400908928016, phi_eightyBZ_94581350728225789400908928017,
    phi_eightyBZ_94581350728225789400908928018, phi_eightyBZ_94581350728225789400908928019, phi_eightyBZ_94581350728225789400908928020,
    phi_eightyBZ_94581350728225789400908928021, phi_eightyBZ_94581350728225789400908928022, phi_eightyBZ_94581350728225789400908928023,
    phi_eightyBZ_94581350728225789400908928024, phi_eightyBZ_94581350728225789400908928025, phi_eightyBZ_94581350728225789400908928026,
    phi_eightyBZ_94581350728225789400908928027, phi_eightyBZ_94581350728225789400908928028, phi_eightyBZ_94581350728225789400908928029,
    phi_eightyBZ_94581350728225789400908928030, phi_eightyBZ_94581350728225789400908928031, phi_eightyBZ_94581350728225789400908928032,
    phi_eightyBZ_94581350728225789400908928033, phi_eightyBZ_94581350728225789400908928034, phi_eightyBZ_94581350728225789400908928035,
    phi_eightyBZ_94581350728225789400908928036, phi_eightyBZ_94581350728225789400908928037, phi_eightyBZ_94581350728225789400908928038,
    phi_eightyBZ_94581350728225789400908928039, phi_eightyBZ_94581350728225789400908928040, phi_eightyBZ_94581350728225789400908928041,
    phi_eightyBZ_94581350728225789400908928042, phi_eightyBZ_94581350728225789400908928043, phi_eightyBZ_94581350728225789400908928044,
    phi_eightyBZ_94581350728225789400908928045, phi_eightyBZ_94581350728225789400908928046, phi_eightyBZ_94581350728225789400908928047,
    phi_eightyBZ_94581350728225789400908928048, phi_eightyBZ_94581350728225789400908928049, phi_eightyBZ_94581350728225789400908928050,
    phi_eightyBZ_94581350728225789400908928051, phi_eightyBZ_94581350728225789400908928052, phi_eightyBZ_94581350728225789400908928053,
    phi_eightyBZ_94581350728225789400908928054, phi_eightyBZ_94581350728225789400908928055, phi_eightyBZ_94581350728225789400908928056,
    phi_eightyBZ_94581350728225789400908928057, phi_eightyBZ_94581350728225789400908928058, phi_eightyBZ_94581350728225789400908928059,
    phi_eightyBZ_94581350728225789400908928060, phi_eightyBZ_94581350728225789400908928061, phi_eightyBZ_94581350728225789400908928062,
    phi_eightyBZ_94581350728225789400908928063, phi_eightyBZ_94581350728225789400908928064, phi_eightyBZ_94581350728225789400908928065,
    phi_eightyBZ_94581350728225789400908928066, phi_eightyBZ_94581350728225789400908928067, phi_eightyBZ_94581350728225789400908928068,
    phi_eightyBZ_94581350728225789400908928069, phi_eightyBZ_94581350728225789400908928070, phi_eightyBZ_94581350728225789400908928071,
    phi_eightyBZ_94581350728225789400908928072, phi_eightyBZ_94581350728225789400908928073, phi_eightyBZ_94581350728225789400908928074,
    phi_eightyBZ_94581350728225789400908928075, phi_eightyBZ_94581350728225789400908928076, phi_eightyBZ_94581350728225789400908928077,
    phi_eightyBZ_94581350728225789400908928078, phi_eightyBZ_94581350728225789400908928079, phi_eightyBZ_94581350728225789400908928080,
    phi_eightyBZ_94581350728225789400908928081, phi_eightyBZ_94581350728225789400908928082, phi_eightyBZ_94581350728225789400908928083,
    phi_eightyBZ_94581350728225789400908928084, phi_eightyBZ_94581350728225789400908928085, phi_eightyBZ_94581350728225789400908928086,
    phi_eightyBZ_94581350728225789400908928087, phi_eightyBZ_94581350728225789400908928088, phi_eightyBZ_94581350728225789400908928089,
    phi_eightyBZ_94581350728225789400908928090, phi_eightyBZ_94581350728225789400908928091, phi_eightyBZ_94581350728225789400908928092,
    phi_eightyBZ_94581350728225789400908928093, phi_eightyBZ_94581350728225789400908928094, phi_eightyBZ_94581350728225789400908928095,
    phi_eightyBZ_94581350728225789400908928096, phi_eightyBZ_94581350728225789400908928097, phi_eightyBZ_94581350728225789400908928098,
    phi_eightyBZ_94581350728225789400908928099, phi_eightyBZ_94581350728225789400908928100, phi_eightyBZ_94581350728225789400908928101]

end TotientTailPeriodKiller
end Erdos249257
