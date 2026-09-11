import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def septFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem septFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    septFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [septFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [septFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then septFastPow a n * septFastPow a n * a
        else septFastPow a n * septFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_septE_2 : Nat.Prime 2 := by norm_num
private theorem prime_septE_3 : Nat.Prime 3 := by norm_num
private theorem prime_septE_5 : Nat.Prime 5 := by norm_num
private theorem prime_septE_7 : Nat.Prime 7 := by norm_num
private theorem prime_septE_11 : Nat.Prime 11 := by norm_num
private theorem prime_septE_13 : Nat.Prime 13 := by norm_num
private theorem prime_septE_17 : Nat.Prime 17 := by norm_num
private theorem prime_septE_19 : Nat.Prime 19 := by norm_num
private theorem prime_septE_23 : Nat.Prime 23 := by norm_num
private theorem prime_septE_29 : Nat.Prime 29 := by norm_num
private theorem prime_septE_31 : Nat.Prime 31 := by norm_num
private theorem prime_septE_37 : Nat.Prime 37 := by norm_num
private theorem prime_septE_41 : Nat.Prime 41 := by norm_num
private theorem prime_septE_43 : Nat.Prime 43 := by norm_num
private theorem prime_septE_47 : Nat.Prime 47 := by norm_num
private theorem prime_septE_53 : Nat.Prime 53 := by norm_num
private theorem prime_septE_59 : Nat.Prime 59 := by norm_num
private theorem prime_septE_61 : Nat.Prime 61 := by norm_num
private theorem prime_septE_67 : Nat.Prime 67 := by norm_num
private theorem prime_septE_71 : Nat.Prime 71 := by norm_num
private theorem prime_septE_73 : Nat.Prime 73 := by norm_num
private theorem prime_septE_79 : Nat.Prime 79 := by norm_num
private theorem prime_septE_83 : Nat.Prime 83 := by norm_num
private theorem prime_septE_89 : Nat.Prime 89 := by norm_num
private theorem prime_septE_97 : Nat.Prime 97 := by norm_num
private theorem prime_septE_101 : Nat.Prime 101 := by norm_num
private theorem prime_septE_103 : Nat.Prime 103 := by norm_num
private theorem prime_septE_107 : Nat.Prime 107 := by norm_num
private theorem prime_septE_113 : Nat.Prime 113 := by norm_num
private theorem prime_septE_127 : Nat.Prime 127 := by norm_num
private theorem prime_septE_131 : Nat.Prime 131 := by norm_num
private theorem prime_septE_137 : Nat.Prime 137 := by norm_num
private theorem prime_septE_139 : Nat.Prime 139 := by norm_num
private theorem prime_septE_149 : Nat.Prime 149 := by norm_num
private theorem prime_septE_151 : Nat.Prime 151 := by norm_num
private theorem prime_septE_157 : Nat.Prime 157 := by norm_num
private theorem prime_septE_163 : Nat.Prime 163 := by norm_num
private theorem prime_septE_167 : Nat.Prime 167 := by norm_num
private theorem prime_septE_179 : Nat.Prime 179 := by norm_num
private theorem prime_septE_181 : Nat.Prime 181 := by norm_num
private theorem prime_septE_191 : Nat.Prime 191 := by norm_num
private theorem prime_septE_193 : Nat.Prime 193 := by norm_num
private theorem prime_septE_199 : Nat.Prime 199 := by norm_num
private theorem prime_septE_211 : Nat.Prime 211 := by norm_num
private theorem prime_septE_223 : Nat.Prime 223 := by norm_num
private theorem prime_septE_227 : Nat.Prime 227 := by norm_num
private theorem prime_septE_229 : Nat.Prime 229 := by norm_num
private theorem prime_septE_233 : Nat.Prime 233 := by norm_num
private theorem prime_septE_239 : Nat.Prime 239 := by norm_num
private theorem prime_septE_241 : Nat.Prime 241 := by norm_num
private theorem prime_septE_251 : Nat.Prime 251 := by norm_num
private theorem prime_septE_257 : Nat.Prime 257 := by norm_num
private theorem prime_septE_263 : Nat.Prime 263 := by norm_num
private theorem prime_septE_271 : Nat.Prime 271 := by norm_num
private theorem prime_septE_277 : Nat.Prime 277 := by norm_num
private theorem prime_septE_283 : Nat.Prime 283 := by norm_num
private theorem prime_septE_293 : Nat.Prime 293 := by norm_num
private theorem prime_septE_311 : Nat.Prime 311 := by norm_num
private theorem prime_septE_317 : Nat.Prime 317 := by norm_num
private theorem prime_septE_337 : Nat.Prime 337 := by norm_num
private theorem prime_septE_349 : Nat.Prime 349 := by norm_num
private theorem prime_septE_359 : Nat.Prime 359 := by norm_num
private theorem prime_septE_379 : Nat.Prime 379 := by norm_num
private theorem prime_septE_383 : Nat.Prime 383 := by norm_num
private theorem prime_septE_389 : Nat.Prime 389 := by norm_num
private theorem prime_septE_397 : Nat.Prime 397 := by norm_num
private theorem prime_septE_409 : Nat.Prime 409 := by norm_num
private theorem prime_septE_431 : Nat.Prime 431 := by norm_num
private theorem prime_septE_439 : Nat.Prime 439 := by norm_num
private theorem prime_septE_443 : Nat.Prime 443 := by norm_num
private theorem prime_septE_449 : Nat.Prime 449 := by norm_num
private theorem prime_septE_461 : Nat.Prime 461 := by norm_num
private theorem prime_septE_479 : Nat.Prime 479 := by norm_num
private theorem prime_septE_487 : Nat.Prime 487 := by norm_num
private theorem prime_septE_491 : Nat.Prime 491 := by norm_num
private theorem prime_septE_521 : Nat.Prime 521 := by norm_num
private theorem prime_septE_541 : Nat.Prime 541 := by norm_num
private theorem prime_septE_569 : Nat.Prime 569 := by norm_num
private theorem prime_septE_601 : Nat.Prime 601 := by norm_num
private theorem prime_septE_613 : Nat.Prime 613 := by norm_num
private theorem prime_septE_617 : Nat.Prime 617 := by norm_num
private theorem prime_septE_619 : Nat.Prime 619 := by norm_num
private theorem prime_septE_641 : Nat.Prime 641 := by norm_num
private theorem prime_septE_643 : Nat.Prime 643 := by norm_num
private theorem prime_septE_677 : Nat.Prime 677 := by norm_num
private theorem prime_septE_691 : Nat.Prime 691 := by norm_num
private theorem prime_septE_719 : Nat.Prime 719 := by norm_num
private theorem prime_septE_751 : Nat.Prime 751 := by norm_num
private theorem prime_septE_761 : Nat.Prime 761 := by norm_num
private theorem prime_septE_797 : Nat.Prime 797 := by norm_num
private theorem prime_septE_821 : Nat.Prime 821 := by norm_num
private theorem prime_septE_839 : Nat.Prime 839 := by norm_num
private theorem prime_septE_853 : Nat.Prime 853 := by norm_num
private theorem prime_septE_857 : Nat.Prime 857 := by norm_num
private theorem prime_septE_863 : Nat.Prime 863 := by norm_num
private theorem prime_septE_937 : Nat.Prime 937 := by norm_num
private theorem prime_septE_971 : Nat.Prime 971 := by norm_num
private theorem prime_septE_991 : Nat.Prime 991 := by norm_num
private theorem prime_septE_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_septE_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_septE_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_septE_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_septE_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_septE_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_septE_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_septE_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_septE_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_septE_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_septE_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_septE_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_septE_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_septE_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_septE_1493 : Nat.Prime 1493 := by norm_num
private theorem prime_septE_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_septE_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_septE_1747 : Nat.Prime 1747 := by norm_num
private theorem prime_septE_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_septE_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_septE_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_septE_1979 : Nat.Prime 1979 := by norm_num
private theorem prime_septE_1999 : Nat.Prime 1999 := by norm_num
private theorem prime_septE_2099 : Nat.Prime 2099 := by norm_num
private theorem prime_septE_2153 : Nat.Prime 2153 := by norm_num
private theorem prime_septE_2179 : Nat.Prime 2179 := by norm_num
private theorem prime_septE_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_septE_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_septE_2357 : Nat.Prime 2357 := by norm_num
private theorem prime_septE_2393 : Nat.Prime 2393 := by norm_num
private theorem prime_septE_2423 : Nat.Prime 2423 := by norm_num
private theorem prime_septE_2467 : Nat.Prime 2467 := by norm_num
private theorem prime_septE_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_septE_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_septE_2633 : Nat.Prime 2633 := by norm_num
private theorem prime_septE_2677 : Nat.Prime 2677 := by norm_num
private theorem prime_septE_2687 : Nat.Prime 2687 := by norm_num
private theorem prime_septE_2711 : Nat.Prime 2711 := by norm_num
private theorem prime_septE_2803 : Nat.Prime 2803 := by norm_num
private theorem prime_septE_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_septE_2939 : Nat.Prime 2939 := by norm_num
private theorem prime_septE_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_septE_3049 : Nat.Prime 3049 := by norm_num
private theorem prime_septE_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_septE_3251 : Nat.Prime 3251 := by norm_num
private theorem prime_septE_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_septE_3257 : Nat.Prime 3257 := by norm_num
private theorem prime_septE_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_septE_3457 : Nat.Prime 3457 := by norm_num
private theorem prime_septE_3463 : Nat.Prime 3463 := by norm_num
private theorem prime_septE_3517 : Nat.Prime 3517 := by norm_num
private theorem prime_septE_3623 : Nat.Prime 3623 := by norm_num
private theorem prime_septE_3659 : Nat.Prime 3659 := by norm_num
private theorem prime_septE_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_septE_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_septE_4229 : Nat.Prime 4229 := by norm_num
private theorem prime_septE_4253 : Nat.Prime 4253 := by norm_num
private theorem prime_septE_4349 : Nat.Prime 4349 := by norm_num
private theorem prime_septE_4481 : Nat.Prime 4481 := by norm_num
private theorem prime_septE_4519 : Nat.Prime 4519 := by norm_num
private theorem prime_septE_4889 : Nat.Prime 4889 := by norm_num
private theorem prime_septE_4909 : Nat.Prime 4909 := by norm_num
private theorem prime_septE_4919 : Nat.Prime 4919 := by norm_num
private theorem prime_septE_4999 : Nat.Prime 4999 := by norm_num
private theorem prime_septE_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_septE_5179 : Nat.Prime 5179 := by norm_num
private theorem prime_septE_5387 : Nat.Prime 5387 := by norm_num
private theorem prime_septE_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_septE_5779 : Nat.Prime 5779 := by norm_num
private theorem prime_septE_5821 : Nat.Prime 5821 := by norm_num
private theorem prime_septE_5843 : Nat.Prime 5843 := by norm_num
private theorem prime_septE_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_septE_6029 : Nat.Prime 6029 := by norm_num
private theorem prime_septE_6229 : Nat.Prime 6229 := by norm_num
private theorem prime_septE_6271 : Nat.Prime 6271 := by norm_num
private theorem prime_septE_6389 : Nat.Prime 6389 := by norm_num
private theorem prime_septE_6529 : Nat.Prime 6529 := by norm_num
private theorem prime_septE_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_septE_6863 : Nat.Prime 6863 := by norm_num
private theorem prime_septE_7109 : Nat.Prime 7109 := by norm_num
private theorem prime_septE_7229 : Nat.Prime 7229 := by norm_num
private theorem prime_septE_7243 : Nat.Prime 7243 := by norm_num
private theorem prime_septE_7309 : Nat.Prime 7309 := by norm_num
private theorem prime_septE_7823 : Nat.Prime 7823 := by norm_num
private theorem prime_septE_8287 : Nat.Prime 8287 := by norm_num
private theorem prime_septE_8623 : Nat.Prime 8623 := by norm_num
private theorem prime_septE_8807 : Nat.Prime 8807 := by norm_num
private theorem prime_septE_8929 : Nat.Prime 8929 := by norm_num
private theorem prime_septE_9461 : Nat.Prime 9461 := by norm_num
private theorem prime_septE_10211 : Nat.Prime 10211 := by norm_num
private theorem prime_septE_10391 : Nat.Prime 10391 := by norm_num
private theorem prime_septE_10729 : Nat.Prime 10729 := by norm_num
private theorem prime_septE_11789 : Nat.Prime 11789 := by norm_num
private theorem prime_septE_11831 : Nat.Prime 11831 := by norm_num
private theorem prime_septE_12263 : Nat.Prime 12263 := by norm_num
private theorem prime_septE_12589 : Nat.Prime 12589 := by norm_num
private theorem prime_septE_12743 : Nat.Prime 12743 := by norm_num
private theorem prime_septE_12853 : Nat.Prime 12853 := by norm_num
private theorem prime_septE_13063 : Nat.Prime 13063 := by norm_num
private theorem prime_septE_13163 : Nat.Prime 13163 := by norm_num
private theorem prime_septE_14449 : Nat.Prime 14449 := by norm_num
private theorem prime_septE_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_septE_15661 : Nat.Prime 15661 := by norm_num
private theorem prime_septE_15683 : Nat.Prime 15683 := by norm_num
private theorem prime_septE_15791 : Nat.Prime 15791 := by norm_num
private theorem prime_septE_15907 : Nat.Prime 15907 := by norm_num
private theorem prime_septE_16631 : Nat.Prime 16631 := by norm_num
private theorem prime_septE_17167 : Nat.Prime 17167 := by norm_num
private theorem prime_septE_18043 : Nat.Prime 18043 := by norm_num
private theorem prime_septE_18959 : Nat.Prime 18959 := by norm_num
private theorem prime_septE_19379 : Nat.Prime 19379 := by norm_num
private theorem prime_septE_19417 : Nat.Prime 19417 := by norm_num
private theorem prime_septE_19801 : Nat.Prime 19801 := by norm_num
private theorem prime_septE_21911 : Nat.Prime 21911 := by norm_num
private theorem prime_septE_22157 : Nat.Prime 22157 := by norm_num
private theorem prime_septE_22279 : Nat.Prime 22279 := by norm_num
private theorem prime_septE_22639 : Nat.Prime 22639 := by norm_num
private theorem prime_septE_23603 : Nat.Prime 23603 := by norm_num
private theorem prime_septE_23669 : Nat.Prime 23669 := by norm_num
private theorem prime_septE_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_septE_28979 : Nat.Prime 28979 := by norm_num
private theorem prime_septE_29287 : Nat.Prime 29287 := by norm_num
private theorem prime_septE_30427 : Nat.Prime 30427 := by norm_num
private theorem prime_septE_30911 : Nat.Prime 30911 := by norm_num
private theorem prime_septE_33223 : Nat.Prime 33223 := by norm_num
private theorem prime_septE_33413 : Nat.Prime 33413 := by norm_num
private theorem prime_septE_33811 : Nat.Prime 33811 := by norm_num
private theorem prime_septE_34361 : Nat.Prime 34361 := by norm_num
private theorem prime_septE_34591 : Nat.Prime 34591 := by norm_num
private theorem prime_septE_34871 : Nat.Prime 34871 := by norm_num
private theorem prime_septE_34897 : Nat.Prime 34897 := by norm_num
private theorem prime_septE_34939 : Nat.Prime 34939 := by norm_num
private theorem prime_septE_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_septE_35401 : Nat.Prime 35401 := by norm_num
private theorem prime_septE_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_septE_39227 : Nat.Prime 39227 := by norm_num
private theorem prime_septE_40577 : Nat.Prime 40577 := by norm_num
private theorem prime_septE_43591 : Nat.Prime 43591 := by norm_num
private theorem prime_septE_45127 : Nat.Prime 45127 := by norm_num
private theorem prime_septE_53129 : Nat.Prime 53129 := by norm_num
private theorem prime_septE_57751 : Nat.Prime 57751 := by norm_num
private theorem prime_septE_58111 : Nat.Prime 58111 := by norm_num
private theorem prime_septE_60397 : Nat.Prime 60397 := by norm_num
private theorem prime_septE_61511 : Nat.Prime 61511 := by norm_num
private theorem prime_septE_61603 : Nat.Prime 61603 := by norm_num
private theorem prime_septE_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_septE_62773 : Nat.Prime 62773 := by norm_num
private theorem prime_septE_65777 : Nat.Prime 65777 := by norm_num
private theorem prime_septE_70141 : Nat.Prime 70141 := by norm_num
private theorem prime_septE_72973 : Nat.Prime 72973 := by norm_num
private theorem prime_septE_78889 : Nat.Prime 78889 := by norm_num
private theorem prime_septE_83609 : Nat.Prime 83609 := by norm_num
private theorem prime_septE_87631 : Nat.Prime 87631 := by norm_num
private theorem prime_septE_94477 : Nat.Prime 94477 := by norm_num
private theorem prime_septE_98729 : Nat.Prime 98729 := by norm_num
private theorem prime_septE_102121 : Nat.Prime 102121 := by norm_num
private theorem prime_septE_103919 : Nat.Prime 103919 := by norm_num
private theorem prime_septE_107671 : Nat.Prime 107671 := by norm_num
private theorem prime_septE_108287 : Nat.Prime 108287 := by norm_num
private theorem prime_septE_112199 : Nat.Prime 112199 := by norm_num
private theorem prime_septE_116141 : Nat.Prime 116141 := by norm_num
private theorem prime_septE_127487 : Nat.Prime 127487 := by norm_num
private theorem prime_septE_128749 : Nat.Prime 128749 := by norm_num
private theorem prime_septE_133073 : Nat.Prime 133073 := by norm_num
private theorem prime_septE_133559 : Nat.Prime 133559 := by norm_num
private theorem prime_septE_148157 : Nat.Prime 148157 := by norm_num
private theorem prime_septE_152639 : Nat.Prime 152639 := by norm_num
private theorem prime_septE_158429 : Nat.Prime 158429 := by norm_num
private theorem prime_septE_158791 : Nat.Prime 158791 := by norm_num
private theorem prime_septE_170227 : Nat.Prime 170227 := by norm_num
private theorem prime_septE_183707 : Nat.Prime 183707 := by norm_num
private theorem prime_septE_185621 : Nat.Prime 185621 := by norm_num
private theorem prime_septE_185873 : Nat.Prime 185873 := by norm_num
private theorem prime_septE_189853 : Nat.Prime 189853 := by norm_num
private theorem prime_septE_190793 : Nat.Prime 190793 := by norm_num
private theorem prime_septE_195271 : Nat.Prime 195271 := by norm_num
private theorem prime_septE_203767 : Nat.Prime 203767 := by norm_num
private theorem prime_septE_206467 : Nat.Prime 206467 := by norm_num
private theorem prime_septE_211039 : Nat.Prime 211039 := by norm_num
private theorem prime_septE_222163 : Nat.Prime 222163 := by norm_num
private theorem prime_septE_224429 : Nat.Prime 224429 := by norm_num
private theorem prime_septE_224897 : Nat.Prime 224897 := by norm_num
private theorem prime_septE_242633 : Nat.Prime 242633 := by norm_num
private theorem prime_septE_265399 : Nat.Prime 265399 := by norm_num
private theorem prime_septE_273187 : Nat.Prime 273187 := by norm_num
private theorem prime_septE_274583 : Nat.Prime 274583 := by norm_num
private theorem prime_septE_276173 : Nat.Prime 276173 := by norm_num
private theorem prime_septE_283133 : Nat.Prime 283133 := by norm_num
private theorem prime_septE_292483 : Nat.Prime 292483 := by norm_num
private theorem prime_septE_293147 : Nat.Prime 293147 := by norm_num
private theorem prime_septE_301867 : Nat.Prime 301867 := by norm_num
private theorem prime_septE_302287 : Nat.Prime 302287 := by norm_num
private theorem prime_septE_306689 : Nat.Prime 306689 := by norm_num
private theorem prime_septE_307817 : Nat.Prime 307817 := by norm_num
private theorem prime_septE_311677 : Nat.Prime 311677 := by norm_num
private theorem prime_septE_311713 : Nat.Prime 311713 := by norm_num
private theorem prime_septE_316097 : Nat.Prime 316097 := by norm_num
private theorem prime_septE_319919 : Nat.Prime 319919 := by norm_num
private theorem prime_septE_325319 : Nat.Prime 325319 := by norm_num
private theorem prime_septE_334661 : Nat.Prime 334661 := by norm_num
private theorem prime_septE_340261 : Nat.Prime 340261 := by norm_num
private theorem prime_septE_343559 : Nat.Prime 343559 := by norm_num
private theorem prime_septE_360823 : Nat.Prime 360823 := by norm_num
private theorem prime_septE_363611 : Nat.Prime 363611 := by norm_num
private theorem prime_septE_367219 : Nat.Prime 367219 := by norm_num
private theorem prime_septE_370537 : Nat.Prime 370537 := by norm_num
private theorem prime_septE_378691 : Nat.Prime 378691 := by norm_num
private theorem prime_septE_385471 : Nat.Prime 385471 := by norm_num
private theorem prime_septE_394811 : Nat.Prime 394811 := by norm_num
private theorem prime_septE_413869 : Nat.Prime 413869 := by norm_num
private theorem prime_septE_429467 : Nat.Prime 429467 := by norm_num
private theorem prime_septE_431891 : Nat.Prime 431891 := by norm_num
private theorem prime_septE_447107 : Nat.Prime 447107 := by norm_num
private theorem prime_septE_452293 : Nat.Prime 452293 := by norm_num
private theorem prime_septE_495017 : Nat.Prime 495017 := by norm_num
private theorem prime_septE_525373 : Nat.Prime 525373 := by norm_num
private theorem prime_septE_548897 : Nat.Prime 548897 := by norm_num
private theorem prime_septE_576509 : Nat.Prime 576509 := by norm_num
private theorem prime_septE_620159 : Nat.Prime 620159 := by norm_num
private theorem prime_septE_693829 : Nat.Prime 693829 := by norm_num
private theorem prime_septE_695389 : Nat.Prime 695389 := by norm_num
private theorem prime_septE_874301 : Nat.Prime 874301 := by norm_num
private theorem prime_septE_874693 : Nat.Prime 874693 := by norm_num
private theorem prime_septE_884003 : Nat.Prime 884003 := by norm_num
private theorem prime_septE_908317 : Nat.Prime 908317 := by norm_num
private theorem prime_septE_914737 : Nat.Prime 914737 := by norm_num
private theorem prime_septE_1020757 : Nat.Prime 1020757 := by norm_num
private theorem prime_septE_1099177 : Nat.Prime 1099177 := by norm_num
private theorem prime_septE_1115447 : Nat.Prime 1115447 := by norm_num
private theorem prime_septE_1173959 : Nat.Prime 1173959 := by norm_num
private theorem prime_septE_1180537 : Nat.Prime 1180537 := by norm_num
private theorem prime_septE_1296089 : Nat.Prime 1296089 := by norm_num
private theorem prime_septE_1305709 : Nat.Prime 1305709 := by norm_num
private theorem prime_septE_1319293 : Nat.Prime 1319293 := by norm_num
private theorem prime_septE_1328143 : Nat.Prime 1328143 := by norm_num
private theorem prime_septE_1346333 : Nat.Prime 1346333 := by norm_num
private theorem prime_septE_1355153 : Nat.Prime 1355153 := by norm_num
private theorem prime_septE_1463149 : Nat.Prime 1463149 := by norm_num
private theorem prime_septE_1487623 : Nat.Prime 1487623 := by norm_num
private theorem prime_septE_1489003 : Nat.Prime 1489003 := by norm_num
private theorem prime_septE_1588921 : Nat.Prime 1588921 := by norm_num
private theorem prime_septE_1693169 : Nat.Prime 1693169 := by norm_num
private theorem prime_septE_1794697 : Nat.Prime 1794697 := by norm_num
private theorem prime_septE_1804613 : Nat.Prime 1804613 := by norm_num
private theorem prime_septE_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_septE_1881863 : Nat.Prime 1881863 := by norm_num
private theorem prime_septE_1957301 : Nat.Prime 1957301 := by norm_num
private theorem prime_septE_2536943 : Nat.Prime 2536943 := by norm_num
private theorem prime_septE_2633923 : Nat.Prime 2633923 := by norm_num
private theorem prime_septE_2643737 : Nat.Prime 2643737 := by norm_num
private theorem prime_septE_2668217 : Nat.Prime 2668217 := by norm_num
private theorem prime_septE_2795809 : Nat.Prime 2795809 := by norm_num
private theorem prime_septE_2846287 : Nat.Prime 2846287 := by norm_num
private theorem prime_septE_2858927 : Nat.Prime 2858927 := by norm_num
private theorem prime_septE_3149387 : Nat.Prime 3149387 := by norm_num
private theorem prime_septE_3369409 : Nat.Prime 3369409 := by norm_num
private theorem prime_septE_3528331 : Nat.Prime 3528331 := by norm_num
private theorem prime_septE_3532679 : Nat.Prime 3532679 := by norm_num
private theorem prime_septE_3581117 : Nat.Prime 3581117 := by norm_num
private theorem prime_septE_3600853 : Nat.Prime 3600853 := by norm_num
private theorem prime_septE_3779417 : Nat.Prime 3779417 := by norm_num
private theorem prime_septE_4528157 : Nat.Prime 4528157 := by norm_num
private theorem prime_septE_5037757 : Nat.Prime 5037757 := by norm_num
private theorem prime_septE_5243207 : Nat.Prime 5243207 := by norm_num
private theorem prime_septE_5326523 : Nat.Prime 5326523 := by norm_num
private theorem prime_septE_6470753 : Nat.Prime 6470753 := by norm_num
private theorem prime_septE_6475879 : Nat.Prime 6475879 := by norm_num
private theorem prime_septE_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_septE_7978459 : Nat.Prime 7978459 := by norm_num
private theorem prime_septE_8696203 : Nat.Prime 8696203 := by norm_num
private theorem prime_septE_8730583 : Nat.Prime 8730583 := by norm_num
private theorem prime_septE_10111469 : Nat.Prime 10111469 := by norm_num
private theorem prime_septE_12045937 : Nat.Prime 12045937 := by norm_num
private theorem prime_septE_13505171 : Nat.Prime 13505171 := by norm_num
private theorem prime_septE_14751743 : Nat.Prime 14751743 := by norm_num
private theorem prime_septE_15279391 : Nat.Prime 15279391 := by norm_num
private theorem prime_septE_15583927 : Nat.Prime 15583927 := by norm_num
private theorem prime_septE_15959533 : Nat.Prime 15959533 := by norm_num
private theorem prime_septE_16775153 : Nat.Prime 16775153 := by norm_num
private theorem prime_septE_18142381 : Nat.Prime 18142381 := by norm_num
private theorem prime_septE_18223631 : Nat.Prime 18223631 := by norm_num
private theorem prime_septE_18974357 : Nat.Prime 18974357 := by norm_num

private theorem prime_septE_20354891 : Nat.Prime 20354891 := by
  apply lucas_primality 20354891 (2 : ZMod 20354891)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (19, 1), (149, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (19, 1), (149, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod = 20354891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_19
      · exact prime_septE_149
      · exact prime_septE_719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20354891) ^ 10177445 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 4070978 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 1071310 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 136610 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 28310 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_20930737 : Nat.Prime 20930737 := by
  apply lucas_primality 20930737 (5 : ZMod 20930737)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod = 20930737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_23
      · exact prime_septE_18959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20930737) ^ 10465368 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 6976912 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 910032 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 1104 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_75997183 : Nat.Prime 75997183 := by
  apply lucas_primality 75997183 (3 : ZMod 75997183)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (31, 1), (479, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (31, 1), (479, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod = 75997183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_31
      · exact prime_septE_479
      · exact prime_septE_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75997183) ^ 37998591 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 25332394 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 2451522 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 158658 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 89094 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_84545803 : Nat.Prime 84545803 := by
  apply lucas_primality 84545803 (2 : ZMod 84545803)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (11, 1), (317, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (11, 1), (317, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod = 84545803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_11
      · exact prime_septE_317
      · exact prime_septE_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 84545803) ^ 42272901 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 84545803) ^ 28181934 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 84545803) ^ 7685982 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 84545803) ^ 266706 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 84545803) ^ 188298 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_116512763 : Nat.Prime 116512763 := by
  apply lucas_primality 116512763 (2 : ZMod 116512763)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (1099177, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (1099177, 1)] : List FactorBlock).map factorBlockValue).prod = 116512763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_53
      · exact prime_septE_1099177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116512763) ^ 58256381 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 116512763) ^ 2198354 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 116512763) ^ 106 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_135236417 : Nat.Prime 135236417 := by
  apply lucas_primality 135236417 (3 : ZMod 135236417)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (7, 1), (301867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (7, 1), (301867, 1)] : List FactorBlock).map factorBlockValue).prod = 135236417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_301867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 135236417) ^ 67618208 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 135236417) ^ 19319488 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 135236417) ^ 448 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_200110847 : Nat.Prime 200110847 := by
  apply lucas_primality 200110847 (5 : ZMod 200110847)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (29, 1), (265399, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (29, 1), (265399, 1)] : List FactorBlock).map factorBlockValue).prod = 200110847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_13
      · exact prime_septE_29
      · exact prime_septE_265399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 200110847) ^ 100055423 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 200110847) ^ 15393142 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 200110847) ^ 6900374 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 200110847) ^ 754 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_224566541 : Nat.Prime 224566541 := by
  apply lucas_primality 224566541 (3 : ZMod 224566541)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (11, 1), (1020757, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (11, 1), (1020757, 1)] : List FactorBlock).map factorBlockValue).prod = 224566541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_11
      · exact prime_septE_1020757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 224566541) ^ 112283270 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 224566541) ^ 44913308 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 224566541) ^ 20415140 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 224566541) ^ 220 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_282045737 : Nat.Prime 282045737 := by
  apply lucas_primality 282045737 (3 : ZMod 282045737)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (97, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (97, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod = 282045737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_97
      · exact prime_septE_137
      · exact prime_septE_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 282045737) ^ 141022868 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 40292248 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 2907688 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 2058728 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 282045737) ^ 744184 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_550990241 : Nat.Prime 550990241 := by
  apply lucas_primality 550990241 (3 : ZMod 550990241)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod = 550990241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_79
      · exact prime_septE_43591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 550990241) ^ 275495120 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 110198048 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 6974560 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 12640 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_626080687 : Nat.Prime 626080687 := by
  apply lucas_primality 626080687 (5 : ZMod 626080687)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod = 626080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_1355153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626080687) ^ 313040343 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 208693562 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 89440098 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 56916426 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 462 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_790484371 : Nat.Prime 790484371 := by
  apply lucas_primality 790484371 (3 : ZMod 790484371)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (13, 1), (227, 1), (8929, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (13, 1), (227, 1), (8929, 1)] : List FactorBlock).map factorBlockValue).prod = 790484371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_13
      · exact prime_septE_227
      · exact prime_septE_8929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 790484371) ^ 395242185 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 790484371) ^ 263494790 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 790484371) ^ 158096874 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 790484371) ^ 60806490 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 790484371) ^ 3482310 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 790484371) ^ 88530 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_29
      · exact prime_septE_113
      · exact prime_septE_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_197209589 : Nat.Prime 197209589 := by
  apply lucas_primality 197209589 (2 : ZMod 197209589)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (19, 1), (152639, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (19, 1), (152639, 1)] : List FactorBlock).map factorBlockValue).prod = 197209589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_152639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 197209589) ^ 98604794 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 197209589) ^ 11600564 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 197209589) ^ 10379452 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 197209589) ^ 1292 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1577676713 : Nat.Prime 1577676713 := by
  apply lucas_primality 1577676713 (3 : ZMod 1577676713)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (197209589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (197209589, 1)] : List FactorBlock).map factorBlockValue).prod = 1577676713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_197209589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1577676713) ^ 788838356 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1577676713) ^ 8 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1907132687 : Nat.Prime 1907132687 := by
  apply lucas_primality 1907132687 (5 : ZMod 1907132687)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (641, 1), (1487623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (641, 1), (1487623, 1)] : List FactorBlock).map factorBlockValue).prod = 1907132687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_641
      · exact prime_septE_1487623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1907132687) ^ 953566343 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 1907132687) ^ 2975246 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 1907132687) ^ 1282 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_2418084863 : Nat.Prime 2418084863 := by
  apply lucas_primality 2418084863 (5 : ZMod 2418084863)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (337, 1), (211039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (337, 1), (211039, 1)] : List FactorBlock).map factorBlockValue).prod = 2418084863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_17
      · exact prime_septE_337
      · exact prime_septE_211039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2418084863) ^ 1209042431 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2418084863) ^ 142240286 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2418084863) ^ 7175326 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2418084863) ^ 11458 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_381350491 : Nat.Prime 381350491 := by
  apply lucas_primality 381350491 (2 : ZMod 381350491)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (37, 1), (343559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (37, 1), (343559, 1)] : List FactorBlock).map factorBlockValue).prod = 381350491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_37
      · exact prime_septE_343559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 381350491) ^ 190675245 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 127116830 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 76270098 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 10306770 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 1110 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_3813504911 : Nat.Prime 3813504911 := by
  apply lucas_primality 3813504911 (17 : ZMod 3813504911)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (381350491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (381350491, 1)] : List FactorBlock).map factorBlockValue).prod = 3813504911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_381350491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 3813504911) ^ 1906752455 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 3813504911) ^ 762700982 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 3813504911) ^ 10 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_8696692033 : Nat.Prime 8696692033 := by
  apply lucas_primality 8696692033 (17 : ZMod 8696692033)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod = 8696692033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_6470753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 8696692033) ^ 4348346016 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 2898897344 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1242384576 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1344 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_9754532209 : Nat.Prime 9754532209 := by
  apply lucas_primality 9754532209 (29 : ZMod 9754532209)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (19, 1), (23, 1), (379, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (19, 1), (23, 1), (379, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod = 9754532209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_379
      · exact prime_septE_409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 9754532209) ^ 4877266104 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 9754532209) ^ 3251510736 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 9754532209) ^ 513396432 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 9754532209) ^ 424110096 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 9754532209) ^ 25737552 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 9754532209) ^ 23849712 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_13492702567 : Nat.Prime 13492702567 := by
  apply lucas_primality 13492702567 (3 : ZMod 13492702567)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod = 13492702567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_23
      · exact prime_septE_47
      · exact prime_septE_59
      · exact prime_septE_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13492702567) ^ 6746351283 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 4497567522 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 1927528938 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 586639242 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 287078778 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 228689874 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 184831542 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_19462639909 : Nat.Prime 19462639909 := by
  apply lucas_primality 19462639909 (13 : ZMod 19462639909)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17167, 1), (94477, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17167, 1), (94477, 1)] : List FactorBlock).map factorBlockValue).prod = 19462639909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_17167
      · exact prime_septE_94477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 19462639909) ^ 9731319954 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 19462639909) ^ 6487546636 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 19462639909) ^ 1133724 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 19462639909) ^ 206004 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_19573967087 : Nat.Prime 19573967087 := by
  apply lucas_primality 19573967087 (5 : ZMod 19573967087)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (59, 1), (8730583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (59, 1), (8730583, 1)] : List FactorBlock).map factorBlockValue).prod = 19573967087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_19
      · exact prime_septE_59
      · exact prime_septE_8730583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19573967087) ^ 9786983543 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 19573967087) ^ 1030208794 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 19573967087) ^ 331762154 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 19573967087) ^ 2242 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_24913302187 : Nat.Prime 24913302187 := by
  apply lucas_primality 24913302187 (2 : ZMod 24913302187)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod = 24913302187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_487
      · exact prime_septE_2621
      · exact prime_septE_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24913302187) ^ 12456651093 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 8304434062 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 51156678 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 9505266 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 7658562 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_29245518173 : Nat.Prime 29245518173 := by
  apply lucas_primality 29245518173 (5 : ZMod 29245518173)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (31, 1), (18142381, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (31, 1), (18142381, 1)] : List FactorBlock).map factorBlockValue).prod = 29245518173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_13
      · exact prime_septE_31
      · exact prime_septE_18142381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29245518173) ^ 14622759086 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 29245518173) ^ 2249655244 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 29245518173) ^ 943403812 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 29245518173) ^ 1612 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_985318699 : Nat.Prime 985318699 := by
  apply lucas_primality 985318699 (2 : ZMod 985318699)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (13, 1), (1804613, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (13, 1), (1804613, 1)] : List FactorBlock).map factorBlockValue).prod = 985318699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_13
      · exact prime_septE_1804613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 985318699) ^ 492659349 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 985318699) ^ 328439566 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 985318699) ^ 140759814 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 985318699) ^ 75793746 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 985318699) ^ 546 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_3941274797 : Nat.Prime 3941274797 := by
  apply lucas_primality 3941274797 (2 : ZMod 3941274797)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (985318699, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (985318699, 1)] : List FactorBlock).map factorBlockValue).prod = 3941274797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_985318699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3941274797) ^ 1970637398 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 3941274797) ^ 4 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_31530198377 : Nat.Prime 31530198377 := by
  apply lucas_primality 31530198377 (3 : ZMod 31530198377)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3941274797, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3941274797, 1)] : List FactorBlock).map factorBlockValue).prod = 31530198377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3941274797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 31530198377) ^ 15765099188 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 31530198377) ^ 8 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_70908014633 : Nat.Prime 70908014633 := by
  apply lucas_primality 70908014633 (3 : ZMod 70908014633)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (13, 1), (4919, 1), (19801, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (13, 1), (4919, 1), (19801, 1)] : List FactorBlock).map factorBlockValue).prod = 70908014633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_13
      · exact prime_septE_4919
      · exact prime_septE_19801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 70908014633) ^ 35454007316 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 10129716376 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 5454462664 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 14415128 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 3581032 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_45885799 : Nat.Prime 45885799 := by
  apply lucas_primality 45885799 (7 : ZMod 45885799)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod = 45885799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_19
      · exact prime_septE_6389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 45885799) ^ 22942899 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 15295266 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 6555114 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 2415042 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 7182 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_120863194567 : Nat.Prime 120863194567 := by
  apply lucas_primality 120863194567 (3 : ZMod 120863194567)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod = 120863194567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_439
      · exact prime_septE_45885799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 120863194567) ^ 60431597283 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 40287731522 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 275314794 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 2634 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_23153183 : Nat.Prime 23153183 := by
  apply lucas_primality 23153183 (5 : ZMod 23153183)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (83, 1), (10729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (83, 1), (10729, 1)] : List FactorBlock).map factorBlockValue).prod = 23153183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_13
      · exact prime_septE_83
      · exact prime_septE_10729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 23153183) ^ 11576591 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 23153183) ^ 1781014 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 23153183) ^ 278954 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 23153183) ^ 2158 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_210091982543 : Nat.Prime 210091982543 := by
  apply lucas_primality 210091982543 (5 : ZMod 210091982543)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (349, 1), (23153183, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (349, 1), (23153183, 1)] : List FactorBlock).map factorBlockValue).prod = 210091982543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_13
      · exact prime_septE_349
      · exact prime_septE_23153183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 210091982543) ^ 105045991271 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 210091982543) ^ 16160921734 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 210091982543) ^ 601982758 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 210091982543) ^ 9074 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_4225305743 : Nat.Prime 4225305743 := by
  apply lucas_primality 4225305743 (5 : ZMod 4225305743)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (29, 1), (2393, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (29, 1), (2393, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod = 4225305743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_29
      · exact prime_septE_2393
      · exact prime_septE_4349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4225305743) ^ 2112652871 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 4225305743) ^ 603615106 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 4225305743) ^ 145700198 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 4225305743) ^ 1765694 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 4225305743) ^ 971558 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_211265287151 : Nat.Prime 211265287151 := by
  apply lucas_primality 211265287151 (7 : ZMod 211265287151)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (4225305743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (4225305743, 1)] : List FactorBlock).map factorBlockValue).prod = 211265287151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_4225305743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 211265287151) ^ 105632643575 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 211265287151) ^ 42253057430 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 211265287151) ^ 50 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_223418077447 : Nat.Prime 223418077447 := by
  apply lucas_primality 223418077447 (3 : ZMod 223418077447)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (2287, 1), (3257, 1), (4999, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (2287, 1), (3257, 1), (4999, 1)] : List FactorBlock).map factorBlockValue).prod = 223418077447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_2287
      · exact prime_septE_3257
      · exact prime_septE_4999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 223418077447) ^ 111709038723 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 223418077447) ^ 74472692482 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 223418077447) ^ 97690458 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 223418077447) ^ 68596278 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 223418077447) ^ 44692554 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_214229656601 : Nat.Prime 214229656601 := by
  apply lucas_primality 214229656601 (3 : ZMod 214229656601)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 2), (47, 1), (83, 1), (274583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 2), (47, 1), (83, 1), (274583, 1)] : List FactorBlock).map factorBlockValue).prod = 214229656601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_47
      · exact prime_septE_83
      · exact prime_septE_274583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 214229656601) ^ 107114828300 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 214229656601) ^ 42845931320 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 214229656601) ^ 4558077800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 214229656601) ^ 2581080200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 214229656601) ^ 780200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_428459313203 : Nat.Prime 428459313203 := by
  apply lucas_primality 428459313203 (2 : ZMod 428459313203)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (214229656601, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (214229656601, 1)] : List FactorBlock).map factorBlockValue).prod = 428459313203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_214229656601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 428459313203) ^ 214229656601 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 428459313203) ^ 2 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_2265698544397 : Nat.Prime 2265698544397 := by
  apply lucas_primality 2265698544397 (2 : ZMod 2265698544397)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (59, 1), (181, 1), (360823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (59, 1), (181, 1), (360823, 1)] : List FactorBlock).map factorBlockValue).prod = 2265698544397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_59
      · exact prime_septE_181
      · exact prime_septE_360823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2265698544397) ^ 1132849272198 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2265698544397) ^ 755232848132 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2265698544397) ^ 323671220628 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2265698544397) ^ 38401670244 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2265698544397) ^ 12517671516 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2265698544397) ^ 6279252 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_938870431 : Nat.Prime 938870431 := by
  apply lucas_primality 938870431 (7 : ZMod 938870431)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (107, 1), (292483, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (107, 1), (292483, 1)] : List FactorBlock).map factorBlockValue).prod = 938870431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_107
      · exact prime_septE_292483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 938870431) ^ 469435215 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 312956810 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 187774086 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 8774490 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 3210 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_4405180062253 : Nat.Prime 4405180062253 := by
  apply lucas_primality 4405180062253 (6 : ZMod 4405180062253)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (23, 1), (938870431, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (23, 1), (938870431, 1)] : List FactorBlock).map factorBlockValue).prod = 4405180062253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_17
      · exact prime_septE_23
      · exact prime_septE_938870431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4405180062253) ^ 2202590031126 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 1468393354084 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 259128238956 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 191529567924 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 4692 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_101995373461 : Nat.Prime 101995373461 := by
  apply lucas_primality 101995373461 (2 : ZMod 101995373461)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (643, 1), (2643737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (643, 1), (2643737, 1)] : List FactorBlock).map factorBlockValue).prod = 101995373461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_643
      · exact prime_septE_2643737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 101995373461) ^ 50997686730 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 101995373461) ^ 33998457820 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 101995373461) ^ 20399074692 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 101995373461) ^ 158624220 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 101995373461) ^ 38580 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_5915731660739 : Nat.Prime 5915731660739 := by
  apply lucas_primality 5915731660739 (2 : ZMod 5915731660739)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (101995373461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (101995373461, 1)] : List FactorBlock).map factorBlockValue).prod = 5915731660739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_29
      · exact prime_septE_101995373461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5915731660739) ^ 2957865830369 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5915731660739) ^ 203990746922 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5915731660739) ^ 58 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_277280084413 : Nat.Prime 277280084413 := by
  apply lucas_primality 277280084413 (5 : ZMod 277280084413)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (23, 1), (31, 1), (3600853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (23, 1), (31, 1), (3600853, 1)] : List FactorBlock).map factorBlockValue).prod = 277280084413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_23
      · exact prime_septE_31
      · exact prime_septE_3600853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 277280084413) ^ 138640042206 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 92426694804 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 12055655844 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 8944518852 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 77004 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_9427522870043 : Nat.Prime 9427522870043 := by
  apply lucas_primality 9427522870043 (2 : ZMod 9427522870043)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (277280084413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (277280084413, 1)] : List FactorBlock).map factorBlockValue).prod = 9427522870043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_17
      · exact prime_septE_277280084413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9427522870043) ^ 4713761435021 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 9427522870043) ^ 554560168826 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 9427522870043) ^ 34 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_24993457 : Nat.Prime 24993457 := by
  apply lucas_primality 24993457 (5 : ZMod 24993457)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (23, 1), (22639, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (23, 1), (22639, 1)] : List FactorBlock).map factorBlockValue).prod = 24993457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_23
      · exact prime_septE_22639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24993457) ^ 12496728 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 24993457) ^ 8331152 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 24993457) ^ 1086672 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 24993457) ^ 1104 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_11241906997859 : Nat.Prime 11241906997859 := by
  apply lucas_primality 11241906997859 (2 : ZMod 11241906997859)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (224897, 1), (24993457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (224897, 1), (24993457, 1)] : List FactorBlock).map factorBlockValue).prod = 11241906997859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_224897
      · exact prime_septE_24993457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11241906997859) ^ 5620953498929 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 11241906997859) ^ 49986914 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 11241906997859) ^ 449794 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_24500423998151 : Nat.Prime 24500423998151 := by
  apply lucas_primality 24500423998151 (23 : ZMod 24500423998151)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (73, 1), (5179, 1), (1296089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (73, 1), (5179, 1), (1296089, 1)] : List FactorBlock).map factorBlockValue).prod = 24500423998151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_73
      · exact prime_septE_5179
      · exact prime_septE_1296089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 24500423998151) ^ 12250211999075 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (23 : ZMod 24500423998151) ^ 4900084799630 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (23 : ZMod 24500423998151) ^ 335622246550 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (23 : ZMod 24500423998151) ^ 4730724850 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (23 : ZMod 24500423998151) ^ 18903350 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_590282327407 : Nat.Prime 590282327407 := by
  apply lucas_primality 590282327407 (3 : ZMod 590282327407)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod = 590282327407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_29
      · exact prime_septE_34361
      · exact prime_septE_98729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 590282327407) ^ 295141163703 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 196760775802 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 20354563014 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 17178846 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 5978814 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_27152987060723 : Nat.Prime 27152987060723 := by
  apply lucas_primality 27152987060723 (2 : ZMod 27152987060723)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod = 27152987060723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_23
      · exact prime_septE_590282327407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27152987060723) ^ 13576493530361 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 1180564654814 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 46 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_33962219399197 : Nat.Prime 33962219399197 := by
  apply lucas_primality 33962219399197 (2 : ZMod 33962219399197)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (11, 1), (57751, 1), (495017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (11, 1), (57751, 1), (495017, 1)] : List FactorBlock).map factorBlockValue).prod = 33962219399197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_11
      · exact prime_septE_57751
      · exact prime_septE_495017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33962219399197) ^ 16981109699598 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 33962219399197) ^ 11320739799732 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 33962219399197) ^ 3087474490836 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 33962219399197) ^ 588080196 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 33962219399197) ^ 68608188 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_31913837 : Nat.Prime 31913837 := by
  apply lucas_primality 31913837 (2 : ZMod 31913837)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod = 31913837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7978459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31913837) ^ 15956918 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 31913837) ^ 4 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_41007301887107 : Nat.Prime 41007301887107 := by
  apply lucas_primality 41007301887107 (2 : ZMod 41007301887107)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod = 41007301887107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_601
      · exact prime_septE_1069
      · exact prime_septE_31913837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41007301887107) ^ 20503650943553 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 68231783506 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 38360432074 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 1284938 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1153512413 : Nat.Prime 1153512413 := by
  apply lucas_primality 1153512413 (2 : ZMod 1153512413)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (191, 1), (116141, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (191, 1), (116141, 1)] : List FactorBlock).map factorBlockValue).prod = 1153512413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_13
      · exact prime_septE_191
      · exact prime_septE_116141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1153512413) ^ 576756206 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1153512413) ^ 88731724 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1153512413) ^ 6039332 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1153512413) ^ 9932 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_107511970941253 : Nat.Prime 107511970941253 := by
  apply lucas_primality 107511970941253 (5 : ZMod 107511970941253)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (863, 1), (1153512413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (863, 1), (1153512413, 1)] : List FactorBlock).map factorBlockValue).prod = 107511970941253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_863
      · exact prime_septE_1153512413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 107511970941253) ^ 53755985470626 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 107511970941253) ^ 35837323647084 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 107511970941253) ^ 124579340604 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 107511970941253) ^ 93204 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_20211619 : Nat.Prime 20211619 := by
  apply lucas_primality 20211619 (7 : ZMod 20211619)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 4), (23, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 4), (23, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 20211619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_23
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20211619) ^ 10105809 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 20211619) ^ 6737206 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 20211619) ^ 2887374 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 20211619) ^ 878766 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 20211619) ^ 331338 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1778622473 : Nat.Prime 1778622473 := by
  apply lucas_primality 1778622473 (3 : ZMod 1778622473)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (20211619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (20211619, 1)] : List FactorBlock).map factorBlockValue).prod = 1778622473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_11
      · exact prime_septE_20211619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1778622473) ^ 889311236 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1778622473) ^ 161692952 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1778622473) ^ 88 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_209681803341971 : Nat.Prime 209681803341971 := by
  apply lucas_primality 209681803341971 (6 : ZMod 209681803341971)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11789, 1), (1778622473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11789, 1), (1778622473, 1)] : List FactorBlock).map factorBlockValue).prod = 209681803341971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_11789
      · exact prime_septE_1778622473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 209681803341971) ^ 104840901670985 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 209681803341971) ^ 41936360668394 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 209681803341971) ^ 17786224730 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 209681803341971) ^ 117890 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_556509832673117 : Nat.Prime 556509832673117 := by
  apply lucas_primality 556509832673117 (2 : ZMod 556509832673117)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (193, 1), (229, 1), (2357, 1), (190793, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (193, 1), (229, 1), (2357, 1), (190793, 1)] : List FactorBlock).map factorBlockValue).prod = 556509832673117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_193
      · exact prime_septE_229
      · exact prime_septE_2357
      · exact prime_septE_190793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 556509832673117) ^ 278254916336558 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 556509832673117) ^ 79501404667588 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 556509832673117) ^ 2883470635612 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 556509832673117) ^ 2430173941804 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 556509832673117) ^ 236109390188 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 556509832673117) ^ 2916825212 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_598744972004371 : Nat.Prime 598744972004371 := by
  apply lucas_primality 598744972004371 (2 : ZMod 598744972004371)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod = 598744972004371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_107
      · exact prime_septE_233
      · exact prime_septE_409
      · exact prime_septE_1957301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 598744972004371) ^ 299372486002185 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 199581657334790 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 119748994400874 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 5595747401910 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 2569720909890 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 1463924136930 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 305903370 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_6525635713 : Nat.Prime 6525635713 := by
  apply lucas_primality 6525635713 (5 : ZMod 6525635713)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (191, 1), (193, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (191, 1), (193, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod = 6525635713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_191
      · exact prime_septE_193
      · exact prime_septE_461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6525635713) ^ 3262817856 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 6525635713) ^ 2175211904 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 6525635713) ^ 34165632 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 6525635713) ^ 33811584 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 6525635713) ^ 14155392 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_748529570095379 : Nat.Prime 748529570095379 := by
  apply lucas_primality 748529570095379 (2 : ZMod 748529570095379)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (83, 1), (691, 1), (6525635713, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (83, 1), (691, 1), (6525635713, 1)] : List FactorBlock).map factorBlockValue).prod = 748529570095379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_83
      · exact prime_septE_691
      · exact prime_septE_6525635713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 748529570095379) ^ 374264785047689 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 748529570095379) ^ 9018428555366 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 748529570095379) ^ 1083255528358 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 748529570095379) ^ 114706 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_817016986973969 : Nat.Prime 817016986973969 := by
  apply lucas_primality 817016986973969 (3 : ZMod 817016986973969)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod = 817016986973969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_11
      · exact prime_septE_223
      · exact prime_septE_283
      · exact prime_septE_5843
      · exact prime_septE_12589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 817016986973969) ^ 408508493486984 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 74274271543088 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 3663753304816 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 2886985819696 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 139828339376 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 64899276112 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_73271521 : Nat.Prime 73271521 := by
  apply lucas_primality 73271521 (13 : ZMod 73271521)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 1), (7, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 1), (7, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod = 73271521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_2423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 73271521) ^ 36635760 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 73271521) ^ 24423840 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 73271521) ^ 14654304 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 73271521) ^ 10467360 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 73271521) ^ 30240 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_879258253 : Nat.Prime 879258253 := by
  apply lucas_primality 879258253 (2 : ZMod 879258253)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (73271521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (73271521, 1)] : List FactorBlock).map factorBlockValue).prod = 879258253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_73271521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 879258253) ^ 439629126 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 879258253) ^ 293086084 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 879258253) ^ 12 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_47479945663 : Nat.Prime 47479945663 := by
  apply lucas_primality 47479945663 (3 : ZMod 47479945663)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (879258253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (879258253, 1)] : List FactorBlock).map factorBlockValue).prod = 47479945663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_879258253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47479945663) ^ 23739972831 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 47479945663) ^ 15826648554 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 47479945663) ^ 54 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_7121991849451 : Nat.Prime 7121991849451 := by
  apply lucas_primality 7121991849451 (3 : ZMod 7121991849451)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (47479945663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (47479945663, 1)] : List FactorBlock).map factorBlockValue).prod = 7121991849451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_47479945663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7121991849451) ^ 3560995924725 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 7121991849451) ^ 2373997283150 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 7121991849451) ^ 1424398369890 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 7121991849451) ^ 150 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_854639021934121 : Nat.Prime 854639021934121 := by
  apply lucas_primality 854639021934121 (11 : ZMod 854639021934121)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (7121991849451, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (7121991849451, 1)] : List FactorBlock).map factorBlockValue).prod = 854639021934121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7121991849451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 854639021934121) ^ 427319510967060 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 854639021934121) ^ 284879673978040 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 854639021934121) ^ 170927804386824 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 854639021934121) ^ 120 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_865882729346359 : Nat.Prime 865882729346359 := by
  apply lucas_primality 865882729346359 (3 : ZMod 865882729346359)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (79, 1), (1931, 1), (7109, 1), (133073, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (79, 1), (1931, 1), (7109, 1), (133073, 1)] : List FactorBlock).map factorBlockValue).prod = 865882729346359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_79
      · exact prime_septE_1931
      · exact prime_septE_7109
      · exact prime_septE_133073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 865882729346359) ^ 432941364673179 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 865882729346359) ^ 288627576448786 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 865882729346359) ^ 10960540877802 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 865882729346359) ^ 448411563618 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 865882729346359) ^ 121800918462 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 865882729346359) ^ 6506825046 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_2267262637 : Nat.Prime 2267262637 := by
  apply lucas_primality 2267262637 (2 : ZMod 2267262637)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (8623, 1), (21911, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (8623, 1), (21911, 1)] : List FactorBlock).map factorBlockValue).prod = 2267262637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_8623
      · exact prime_septE_21911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2267262637) ^ 1133631318 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267262637) ^ 755754212 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267262637) ^ 262932 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267262637) ^ 103476 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_145104808769 : Nat.Prime 145104808769 := by
  apply lucas_primality 145104808769 (3 : ZMod 145104808769)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (2267262637, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (2267262637, 1)] : List FactorBlock).map factorBlockValue).prod = 145104808769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_2267262637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 145104808769) ^ 72552404384 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 145104808769) ^ 64 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1206981799340543 : Nat.Prime 1206981799340543 := by
  apply lucas_primality 1206981799340543 (5 : ZMod 1206981799340543)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4159, 1), (145104808769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4159, 1), (145104808769, 1)] : List FactorBlock).map factorBlockValue).prod = 1206981799340543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_4159
      · exact prime_septE_145104808769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1206981799340543) ^ 603490899670271 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 1206981799340543) ^ 290209617538 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 1206981799340543) ^ 8318 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1073037023 : Nat.Prime 1073037023 := by
  apply lucas_primality 1073037023 (5 : ZMod 1073037023)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2633, 1), (203767, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2633, 1), (203767, 1)] : List FactorBlock).map factorBlockValue).prod = 1073037023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_2633
      · exact prime_septE_203767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1073037023) ^ 536518511 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 1073037023) ^ 407534 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 1073037023) ^ 5266 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_2465570819598251 : Nat.Prime 2465570819598251 := by
  apply lucas_primality 2465570819598251 (2 : ZMod 2465570819598251)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 3), (7, 1), (13, 1), (101, 1), (1073037023, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 3), (7, 1), (13, 1), (101, 1), (1073037023, 1)] : List FactorBlock).map factorBlockValue).prod = 2465570819598251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_13
      · exact prime_septE_101
      · exact prime_septE_1073037023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2465570819598251) ^ 1232785409799125 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2465570819598251) ^ 493114163919650 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2465570819598251) ^ 352224402799750 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2465570819598251) ^ 189659293815250 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2465570819598251) ^ 24411592273250 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2465570819598251) ^ 2297750 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_29623871 : Nat.Prime 29623871 := by
  apply lucas_primality 29623871 (7 : ZMod 29623871)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (409, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (409, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod = 29623871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_409
      · exact prime_septE_7243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 29623871) ^ 14811935 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 29623871) ^ 5924774 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 29623871) ^ 72430 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 29623871) ^ 4090 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_59247743 : Nat.Prime 59247743 := by
  apply lucas_primality 59247743 (5 : ZMod 59247743)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29623871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29623871, 1)] : List FactorBlock).map factorBlockValue).prod = 59247743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_29623871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 59247743) ^ 29623871 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 59247743) ^ 2 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_2743295750628703 : Nat.Prime 2743295750628703 := by
  apply lucas_primality 2743295750628703 (5 : ZMod 2743295750628703)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (2531, 1), (3049, 1), (59247743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (2531, 1), (3049, 1), (59247743, 1)] : List FactorBlock).map factorBlockValue).prod = 2743295750628703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_2531
      · exact prime_septE_3049
      · exact prime_septE_59247743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2743295750628703) ^ 1371647875314351 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 914431916876234 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 1083878210442 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 899736225198 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2743295750628703) ^ 46302114 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_706708969 : Nat.Prime 706708969 := by
  apply lucas_primality 706708969 (11 : ZMod 706708969)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 3), (293, 2)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 3), (293, 2)] : List FactorBlock).map factorBlockValue).prod = 706708969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 706708969) ^ 353354484 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 706708969) ^ 235569656 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 706708969) ^ 100958424 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 706708969) ^ 2411976 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_3052027275553913 : Nat.Prime 3052027275553913 := by
  apply lucas_primality 3052027275553913 (3 : ZMod 3052027275553913)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (461, 1), (1171, 1), (706708969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (461, 1), (1171, 1), (706708969, 1)] : List FactorBlock).map factorBlockValue).prod = 3052027275553913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_461
      · exact prime_septE_1171
      · exact prime_septE_706708969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3052027275553913) ^ 1526013637776956 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 3052027275553913) ^ 6620449621592 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 3052027275553913) ^ 2606342677672 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 3052027275553913) ^ 4318648 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_663911472061 : Nat.Prime 663911472061 := by
  apply lucas_primality 663911472061 (2 : ZMod 663911472061)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 1), (11831, 1), (103919, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 1), (11831, 1), (103919, 1)] : List FactorBlock).map factorBlockValue).prod = 663911472061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_11831
      · exact prime_septE_103919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 663911472061) ^ 331955736030 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 663911472061) ^ 221303824020 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 663911472061) ^ 132782294412 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 663911472061) ^ 56116260 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 663911472061) ^ 6388740 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_9335923120121783 : Nat.Prime 9335923120121783 := by
  apply lucas_primality 9335923120121783 (5 : ZMod 9335923120121783)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (79, 1), (89, 1), (663911472061, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (79, 1), (89, 1), (663911472061, 1)] : List FactorBlock).map factorBlockValue).prod = 9335923120121783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_79
      · exact prime_septE_89
      · exact prime_septE_663911472061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9335923120121783) ^ 4667961560060891 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 9335923120121783) ^ 118176242026858 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 9335923120121783) ^ 104898012585638 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 9335923120121783) ^ 14062 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_96140073437 : Nat.Prime 96140073437 := by
  apply lucas_primality 96140073437 (2 : ZMod 96140073437)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (6529, 1), (334661, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (6529, 1), (334661, 1)] : List FactorBlock).map factorBlockValue).prod = 96140073437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_11
      · exact prime_septE_6529
      · exact prime_septE_334661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 96140073437) ^ 48070036718 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 96140073437) ^ 8740006676 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 96140073437) ^ 14725084 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 96140073437) ^ 287276 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_89410268296411 : Nat.Prime 89410268296411 := by
  apply lucas_primality 89410268296411 (2 : ZMod 89410268296411)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (31, 1), (96140073437, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (31, 1), (96140073437, 1)] : List FactorBlock).map factorBlockValue).prod = 89410268296411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_31
      · exact prime_septE_96140073437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89410268296411) ^ 44705134148205 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 89410268296411) ^ 29803422765470 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 89410268296411) ^ 17882053659282 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 89410268296411) ^ 2884202203110 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 89410268296411) ^ 930 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_9656308976012389 : Nat.Prime 9656308976012389 := by
  apply lucas_primality 9656308976012389 (2 : ZMod 9656308976012389)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (89410268296411, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (89410268296411, 1)] : List FactorBlock).map factorBlockValue).prod = 9656308976012389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_89410268296411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9656308976012389) ^ 4828154488006194 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 9656308976012389) ^ 3218769658670796 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 9656308976012389) ^ 108 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_2306239349 : Nat.Prime 2306239349 := by
  apply lucas_primality 2306239349 (2 : ZMod 2306239349)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (23, 1), (3581117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (23, 1), (3581117, 1)] : List FactorBlock).map factorBlockValue).prod = 2306239349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_23
      · exact prime_septE_3581117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2306239349) ^ 1153119674 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306239349) ^ 329462764 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306239349) ^ 100271276 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306239349) ^ 644 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_11465035350555889 : Nat.Prime 11465035350555889 := by
  apply lucas_primality 11465035350555889 (17 : ZMod 11465035350555889)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (19, 1), (23, 1), (79, 1), (2306239349, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (19, 1), (23, 1), (79, 1), (2306239349, 1)] : List FactorBlock).map factorBlockValue).prod = 11465035350555889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_79
      · exact prime_septE_2306239349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 11465035350555889) ^ 5732517675277944 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 11465035350555889) ^ 3821678450185296 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 11465035350555889) ^ 603422913187152 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 11465035350555889) ^ 498479797850256 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 11465035350555889) ^ 145127029753872 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 11465035350555889) ^ 4971312 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_13593741208926217 : Nat.Prime 13593741208926217 := by
  apply lucas_primality 13593741208926217 (10 : ZMod 13593741208926217)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (13, 1), (2795809, 1), (15583927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (13, 1), (2795809, 1), (15583927, 1)] : List FactorBlock).map factorBlockValue).prod = 13593741208926217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_13
      · exact prime_septE_2795809
      · exact prime_septE_15583927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 13593741208926217) ^ 6796870604463108 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 13593741208926217) ^ 4531247069642072 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 13593741208926217) ^ 1045672400686632 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 13593741208926217) ^ 4862185224 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 13593741208926217) ^ 872292408 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1590164911 : Nat.Prime 1590164911 := by
  apply lucas_primality 1590164911 (3 : ZMod 1590164911)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod = 1590164911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_19
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1590164911) ^ 795082455 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 530054970 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 318032982 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 83692890 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 42977430 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 38784510 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 2594070 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_254426385761 : Nat.Prime 254426385761 := by
  apply lucas_primality 254426385761 (3 : ZMod 254426385761)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod = 254426385761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_1590164911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 254426385761) ^ 127213192880 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 50885277152 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 160 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_22145781469408963 : Nat.Prime 22145781469408963 := by
  apply lucas_primality 22145781469408963 (2 : ZMod 22145781469408963)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod = 22145781469408963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_89
      · exact prime_septE_163
      · exact prime_septE_254426385761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22145781469408963) ^ 11072890734704481 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 7381927156469654 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 248829005274258 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 135863689996374 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 87042 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_114218290024018991 : Nat.Prime 114218290024018991 := by
  apply lucas_primality 114218290024018991 (17 : ZMod 114218290024018991)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (491, 1), (2677, 1), (15073, 1), (576509, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (491, 1), (2677, 1), (15073, 1), (576509, 1)] : List FactorBlock).map factorBlockValue).prod = 114218290024018991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_491
      · exact prime_septE_2677
      · exact prime_septE_15073
      · exact prime_septE_576509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 114218290024018991) ^ 57109145012009495 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 22843658004803798 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 232623808602890 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 42666525970870 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 7577674651630 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 198120567110 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_12144067051 : Nat.Prime 12144067051 := by
  apply lucas_primality 12144067051 (3 : ZMod 12144067051)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (179, 1), (452293, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (179, 1), (452293, 1)] : List FactorBlock).map factorBlockValue).prod = 12144067051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_179
      · exact prime_septE_452293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12144067051) ^ 6072033525 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 12144067051) ^ 4048022350 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 12144067051) ^ 2428813410 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 12144067051) ^ 67843950 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 12144067051) ^ 26850 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_72864402307 : Nat.Prime 72864402307 := by
  apply lucas_primality 72864402307 (5 : ZMod 72864402307)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (12144067051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (12144067051, 1)] : List FactorBlock).map factorBlockValue).prod = 72864402307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_12144067051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 72864402307) ^ 36432201153 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 72864402307) ^ 24288134102 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 72864402307) ^ 6 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_728644023071 : Nat.Prime 728644023071 := by
  apply lucas_primality 728644023071 (17 : ZMod 728644023071)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (72864402307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (72864402307, 1)] : List FactorBlock).map factorBlockValue).prod = 728644023071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_72864402307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 728644023071) ^ 364322011535 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 728644023071) ^ 145728804614 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (17 : ZMod 728644023071) ^ 10 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_135695376416512331 : Nat.Prime 135695376416512331 := by
  apply lucas_primality 135695376416512331 (2 : ZMod 135695376416512331)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (1693, 1), (728644023071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (1693, 1), (728644023071, 1)] : List FactorBlock).map factorBlockValue).prod = 135695376416512331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_11
      · exact prime_septE_1693
      · exact prime_septE_728644023071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135695376416512331) ^ 67847688208256165 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 135695376416512331) ^ 27139075283302466 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 135695376416512331) ^ 12335943310592030 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 135695376416512331) ^ 80150842537810 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 135695376416512331) ^ 186230 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_89405586621479 : Nat.Prime 89405586621479 := by
  apply lucas_primality 89405586621479 (7 : ZMod 89405586621479)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (113, 1), (39227, 1), (325319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (113, 1), (39227, 1), (325319, 1)] : List FactorBlock).map factorBlockValue).prod = 89405586621479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_31
      · exact prime_septE_113
      · exact prime_septE_39227
      · exact prime_septE_325319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 89405586621479) ^ 44702793310739 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 89405586621479) ^ 2884051181338 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 89405586621479) ^ 791199881606 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 89405586621479) ^ 2279184914 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 89405586621479) ^ 274824362 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_138042225743563577 : Nat.Prime 138042225743563577 := by
  apply lucas_primality 138042225743563577 (3 : ZMod 138042225743563577)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (193, 1), (89405586621479, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (193, 1), (89405586621479, 1)] : List FactorBlock).map factorBlockValue).prod = 138042225743563577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_193
      · exact prime_septE_89405586621479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 138042225743563577) ^ 69021112871781788 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 138042225743563577) ^ 715244692971832 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 138042225743563577) ^ 1544 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_64759129 : Nat.Prime 64759129 := by
  apply lucas_primality 64759129 (11 : ZMod 64759129)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (385471, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (385471, 1)] : List FactorBlock).map factorBlockValue).prod = 64759129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_385471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 64759129) ^ 32379564 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 64759129) ^ 21586376 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 64759129) ^ 9251304 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 64759129) ^ 168 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_647591291 : Nat.Prime 647591291 := by
  apply lucas_primality 647591291 (2 : ZMod 647591291)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (64759129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (64759129, 1)] : List FactorBlock).map factorBlockValue).prod = 647591291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_64759129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 647591291) ^ 323795645 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 647591291) ^ 129518258 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 647591291) ^ 10 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_169065085989715453 : Nat.Prime 169065085989715453 := by
  apply lucas_primality 169065085989715453 (15 : ZMod 169065085989715453)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (17, 2), (23, 1), (1091, 1), (647591291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (17, 2), (23, 1), (1091, 1), (647591291, 1)] : List FactorBlock).map factorBlockValue).prod = 169065085989715453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_17
      · exact prime_septE_23
      · exact prime_septE_1091
      · exact prime_septE_647591291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 169065085989715453) ^ 84532542994857726 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (15 : ZMod 169065085989715453) ^ 56355028663238484 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (15 : ZMod 169065085989715453) ^ 9945005058218556 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (15 : ZMod 169065085989715453) ^ 7350655912596324 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (15 : ZMod 169065085989715453) ^ 154963415205972 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (15 : ZMod 169065085989715453) ^ 261067572 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_267926829178745687 : Nat.Prime 267926829178745687 := by
  apply lucas_primality 267926829178745687 (5 : ZMod 267926829178745687)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (251, 1), (1747, 1), (170227, 1), (1794697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (251, 1), (1747, 1), (170227, 1), (1794697, 1)] : List FactorBlock).map factorBlockValue).prod = 267926829178745687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_251
      · exact prime_septE_1747
      · exact prime_septE_170227
      · exact prime_septE_1794697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 267926829178745687) ^ 133963414589372843 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 267926829178745687) ^ 1067437566449186 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 267926829178745687) ^ 153363954881938 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 267926829178745687) ^ 1573938500818 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 267926829178745687) ^ 149288057638 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_16103786791 : Nat.Prime 16103786791 := by
  apply lucas_primality 16103786791 (7 : ZMod 16103786791)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 2), (13, 1), (569, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 2), (13, 1), (569, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod = 16103786791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_13
      · exact prime_septE_569
      · exact prime_septE_1481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16103786791) ^ 8051893395 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 5367928930 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 3220757358 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 2300540970 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 1238752830 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 28301910 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 16103786791) ^ 10873590 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_284004322561366753 : Nat.Prime 284004322561366753 := by
  apply lucas_primality 284004322561366753 (5 : ZMod 284004322561366753)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (183707, 1), (16103786791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (183707, 1), (16103786791, 1)] : List FactorBlock).map factorBlockValue).prod = 284004322561366753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_183707
      · exact prime_septE_16103786791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 284004322561366753) ^ 142002161280683376 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 284004322561366753) ^ 94668107520455584 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 284004322561366753) ^ 1545963531936 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 284004322561366753) ^ 17635872 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_377672369920211983 : Nat.Prime 377672369920211983 := by
  apply lucas_primality 377672369920211983 (3 : ZMod 377672369920211983)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod = 377672369920211983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_5037757
      · exact prime_septE_14751743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 377672369920211983) ^ 188836184960105991 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 125890789973403994 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 53953195702887426 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 34333851810928362 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 74968357926 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 25601881074 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_17
      · exact prime_septE_397
      · exact prime_septE_2531
      · exact prime_septE_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_11
      · exact prime_septE_41
      · exact prime_septE_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_29
      · exact prime_septE_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_119543144893 : Nat.Prime 119543144893 := by
  apply lucas_primality 119543144893 (2 : ZMod 119543144893)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (6271, 1), (83609, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (6271, 1), (83609, 1)] : List FactorBlock).map factorBlockValue).prod = 119543144893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_19
      · exact prime_septE_6271
      · exact prime_septE_83609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 119543144893) ^ 59771572446 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 39847714964 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 6291744468 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 19062852 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 1429788 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1533142745943043289 : Nat.Prime 1533142745943043289 := by
  apply lucas_primality 1533142745943043289 (3 : ZMod 1533142745943043289)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (157, 1), (10211, 1), (119543144893, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (157, 1), (10211, 1), (119543144893, 1)] : List FactorBlock).map factorBlockValue).prod = 1533142745943043289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_157
      · exact prime_septE_10211
      · exact prime_septE_119543144893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1533142745943043289) ^ 766571372971521644 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1533142745943043289) ^ 9765240420019384 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1533142745943043289) ^ 150146189985608 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1533142745943043289) ^ 12825016 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_234618376831987 : Nat.Prime 234618376831987 := by
  apply lucas_primality 234618376831987 (2 : ZMod 234618376831987)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (113, 1), (4889, 1), (10111469, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (113, 1), (4889, 1), (10111469, 1)] : List FactorBlock).map factorBlockValue).prod = 234618376831987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_113
      · exact prime_septE_4889
      · exact prime_septE_10111469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 234618376831987) ^ 117309188415993 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 234618376831987) ^ 78206125610662 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 234618376831987) ^ 33516910975998 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 234618376831987) ^ 2076268821522 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 234618376831987) ^ 47989031874 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 234618376831987) ^ 23203194 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_3330173240753223479 : Nat.Prime 3330173240753223479 := by
  apply lucas_primality 3330173240753223479 (19 : ZMod 3330173240753223479)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (47, 1), (151, 1), (234618376831987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (47, 1), (151, 1), (234618376831987, 1)] : List FactorBlock).map factorBlockValue).prod = 3330173240753223479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_47
      · exact prime_septE_151
      · exact prime_septE_234618376831987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 3330173240753223479) ^ 1665086620376611739 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (19 : ZMod 3330173240753223479) ^ 70854749803260074 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (19 : ZMod 3330173240753223479) ^ 22054127422206778 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (19 : ZMod 3330173240753223479) ^ 14194 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_7843620229 : Nat.Prime 7843620229 := by
  apply lucas_primality 7843620229 (2 : ZMod 7843620229)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (79, 1), (1999, 1), (4139, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (79, 1), (1999, 1), (4139, 1)] : List FactorBlock).map factorBlockValue).prod = 7843620229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_79
      · exact prime_septE_1999
      · exact prime_septE_4139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7843620229) ^ 3921810114 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7843620229) ^ 2614540076 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7843620229) ^ 99286332 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7843620229) ^ 3923772 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7843620229) ^ 1895052 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_21083651175553 : Nat.Prime 21083651175553 := by
  apply lucas_primality 21083651175553 (29 : ZMod 21083651175553)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (7, 1), (7843620229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (7, 1), (7843620229, 1)] : List FactorBlock).map factorBlockValue).prod = 21083651175553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_7843620229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 21083651175553) ^ 10541825587776 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 21083651175553) ^ 7027883725184 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 21083651175553) ^ 3011950167936 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 21083651175553) ^ 2688 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_4478294011594510519 : Nat.Prime 4478294011594510519 := by
  apply lucas_primality 4478294011594510519 (3 : ZMod 4478294011594510519)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35401, 1), (21083651175553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35401, 1), (21083651175553, 1)] : List FactorBlock).map factorBlockValue).prod = 4478294011594510519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_35401
      · exact prime_septE_21083651175553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4478294011594510519) ^ 2239147005797255259 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 4478294011594510519) ^ 1492764670531503506 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 4478294011594510519) ^ 126501907053318 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 4478294011594510519) ^ 212406 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_3094302641740947971 : Nat.Prime 3094302641740947971 := by
  apply lucas_primality 3094302641740947971 (2 : ZMod 3094302641740947971)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (3463, 1), (5326523, 1), (16775153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (3463, 1), (5326523, 1), (16775153, 1)] : List FactorBlock).map factorBlockValue).prod = 3094302641740947971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_3463
      · exact prime_septE_5326523
      · exact prime_septE_16775153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3094302641740947971) ^ 1547151320870473985 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 3094302641740947971) ^ 618860528348189594 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 3094302641740947971) ^ 893532382830190 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 3094302641740947971) ^ 580923548390 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 3094302641740947971) ^ 184457491490 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_6188605283481895943 : Nat.Prime 6188605283481895943 := by
  apply lucas_primality 6188605283481895943 (5 : ZMod 6188605283481895943)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3094302641740947971, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3094302641740947971, 1)] : List FactorBlock).map factorBlockValue).prod = 6188605283481895943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3094302641740947971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 6188605283481895943) ^ 3094302641740947971 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 6188605283481895943) ^ 2 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_90735599 : Nat.Prime 90735599 := by
  apply lucas_primality 90735599 (11 : ZMod 90735599)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (151, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (151, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod = 90735599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_23
      · exact prime_septE_151
      · exact prime_septE_13063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 90735599) ^ 45367799 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 3945026 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 600898 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 6946 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_7361524796742341989 : Nat.Prime 7361524796742341989 := by
  apply lucas_primality 7361524796742341989 (2 : ZMod 7361524796742341989)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (53, 1), (18223631, 1), (90735599, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (53, 1), (18223631, 1), (90735599, 1)] : List FactorBlock).map factorBlockValue).prod = 7361524796742341989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_53
      · exact prime_septE_18223631
      · exact prime_septE_90735599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7361524796742341989) ^ 3680762398371170994 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 2453841598914113996 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 1051646399534620284 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 138896694278157396 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 403954886748 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 81131605212 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_7510116500595532297 : Nat.Prime 7510116500595532297 := by
  apply lucas_primality 7510116500595532297 (5 : ZMod 7510116500595532297)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (11, 1), (443, 1), (3457, 1), (15683, 1), (394811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (11, 1), (443, 1), (3457, 1), (15683, 1), (394811, 1)] : List FactorBlock).map factorBlockValue).prod = 7510116500595532297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_11
      · exact prime_septE_443
      · exact prime_septE_3457
      · exact prime_septE_15683
      · exact prime_septE_394811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7510116500595532297) ^ 3755058250297766148 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 2503372166865177432 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 682737863690502936 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 16952858917822872 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 2172437518251528 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 478869891002712 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 19022054858136 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_118081211 : Nat.Prime 118081211 := by
  apply lucas_primality 118081211 (14 : ZMod 118081211)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod = 118081211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_13
      · exact prime_septE_908317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 118081211) ^ 59040605 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 23616242 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 9083170 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 130 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_10675900157669865007 : Nat.Prime 10675900157669865007 := by
  apply lucas_primality 10675900157669865007 (10 : ZMod 10675900157669865007)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod = 10675900157669865007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_19
      · exact prime_septE_1823
      · exact prime_septE_3271
      · exact prime_septE_118081211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10675900157669865007) ^ 5337950078834932503 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3558633385889955002 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 1525128593952837858 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 561889481982624474 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 5856226087586322 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3263803166514786 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 90411506346 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_67
      · exact prime_septE_28807
      · exact prime_septE_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_23
      · exact prime_septE_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1686291654781 : Nat.Prime 1686291654781 := by
  apply lucas_primality 1686291654781 (2 : ZMod 1686291654781)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (131, 1), (193, 1), (370537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (131, 1), (193, 1), (370537, 1)] : List FactorBlock).map factorBlockValue).prod = 1686291654781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_131
      · exact prime_septE_193
      · exact prime_septE_370537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1686291654781) ^ 843145827390 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 562097218260 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 337258330956 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 12872455380 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 8737262460 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 4550940 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_15713735765743224997 : Nat.Prime 15713735765743224997 := by
  apply lucas_primality 15713735765743224997 (2 : ZMod 15713735765743224997)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 2), (2687, 1), (1686291654781, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 2), (2687, 1), (1686291654781, 1)] : List FactorBlock).map factorBlockValue).prod = 15713735765743224997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_17
      · exact prime_septE_2687
      · exact prime_septE_1686291654781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15713735765743224997) ^ 7856867882871612498 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 5237911921914408332 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 924337397984895588 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 5848059458780508 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 9318516 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_811821761 : Nat.Prime 811821761 := by
  apply lucas_primality 811821761 (3 : ZMod 811821761)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (2536943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (2536943, 1)] : List FactorBlock).map factorBlockValue).prod = 811821761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_2536943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 811821761) ^ 405910880 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 811821761) ^ 162364352 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 811821761) ^ 320 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_5484812849 : Nat.Prime 5484812849 := by
  apply lucas_primality 5484812849 (3 : ZMod 5484812849)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5573, 1), (61511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5573, 1), (61511, 1)] : List FactorBlock).map factorBlockValue).prod = 5484812849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5573
      · exact prime_septE_61511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5484812849) ^ 2742406424 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 5484812849) ^ 984176 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 5484812849) ^ 89168 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_53432285109967285069 : Nat.Prime 53432285109967285069 := by
  apply lucas_primality 53432285109967285069 (2 : ZMod 53432285109967285069)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (811821761, 1), (5484812849, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (811821761, 1), (5484812849, 1)] : List FactorBlock).map factorBlockValue).prod = 53432285109967285069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_811821761
      · exact prime_septE_5484812849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53432285109967285069) ^ 26716142554983642534 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 53432285109967285069) ^ 17810761703322428356 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 53432285109967285069) ^ 65817754188 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 53432285109967285069) ^ 9741861132 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_5623407091 : Nat.Prime 5623407091 := by
  apply lucas_primality 5623407091 (2 : ZMod 5623407091)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (7, 2), (163, 1), (7823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (7, 2), (163, 1), (7823, 1)] : List FactorBlock).map factorBlockValue).prod = 5623407091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_163
      · exact prime_septE_7823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5623407091) ^ 2811703545 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5623407091) ^ 1874469030 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5623407091) ^ 1124681418 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5623407091) ^ 803343870 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5623407091) ^ 34499430 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5623407091) ^ 718830 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_61195559393737530569 : Nat.Prime 61195559393737530569 := by
  apply lucas_primality 61195559393737530569 (3 : ZMod 61195559393737530569)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (491, 1), (1123, 1), (2467, 1), (5623407091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (491, 1), (1123, 1), (2467, 1), (5623407091, 1)] : List FactorBlock).map factorBlockValue).prod = 61195559393737530569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_491
      · exact prime_septE_1123
      · exact prime_septE_2467
      · exact prime_septE_5623407091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 61195559393737530569) ^ 30597779696868765284 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 61195559393737530569) ^ 124634540516777048 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 61195559393737530569) ^ 54492929112856216 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 61195559393737530569) ^ 24805658449022104 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 61195559393737530569) ^ 10882292248 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_32982869 : Nat.Prime 32982869 := by
  apply lucas_primality 32982869 (2 : ZMod 32982869)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (271, 1), (30427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (271, 1), (30427, 1)] : List FactorBlock).map factorBlockValue).prod = 32982869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_271
      · exact prime_septE_30427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32982869) ^ 16491434 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 32982869) ^ 121708 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 32982869) ^ 1084 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1385280499 : Nat.Prime 1385280499 := by
  apply lucas_primality 1385280499 (2 : ZMod 1385280499)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (32982869, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (32982869, 1)] : List FactorBlock).map factorBlockValue).prod = 1385280499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_32982869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1385280499) ^ 692640249 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1385280499) ^ 461760166 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1385280499) ^ 197897214 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1385280499) ^ 42 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_148978605984457 : Nat.Prime 148978605984457 := by
  apply lucas_primality 148978605984457 (10 : ZMod 148978605984457)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (4481, 1), (1385280499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (4481, 1), (1385280499, 1)] : List FactorBlock).map factorBlockValue).prod = 148978605984457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_4481
      · exact prime_septE_1385280499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 148978605984457) ^ 74489302992228 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 148978605984457) ^ 49659535328152 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 148978605984457) ^ 33246731976 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 148978605984457) ^ 107544 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_68933592817856129557 : Nat.Prime 68933592817856129557 := by
  apply lucas_primality 68933592817856129557 (2 : ZMod 68933592817856129557)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (12853, 1), (148978605984457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (12853, 1), (148978605984457, 1)] : List FactorBlock).map factorBlockValue).prod = 68933592817856129557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_12853
      · exact prime_septE_148978605984457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68933592817856129557) ^ 34466796408928064778 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 68933592817856129557) ^ 22977864272618709852 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 68933592817856129557) ^ 5363229815440452 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 68933592817856129557) ^ 462708 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_11376245767 : Nat.Prime 11376245767 := by
  apply lucas_primality 11376245767 (3 : ZMod 11376245767)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (83, 1), (1031, 1), (22157, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (83, 1), (1031, 1), (22157, 1)] : List FactorBlock).map factorBlockValue).prod = 11376245767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_83
      · exact prime_septE_1031
      · exact prime_septE_22157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11376245767) ^ 5688122883 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 11376245767) ^ 3792081922 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 11376245767) ^ 137063202 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 11376245767) ^ 11034186 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 11376245767) ^ 513438 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_68257474603 : Nat.Prime 68257474603 := by
  apply lucas_primality 68257474603 (2 : ZMod 68257474603)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11376245767, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11376245767, 1)] : List FactorBlock).map factorBlockValue).prod = 68257474603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_11376245767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68257474603) ^ 34128737301 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 68257474603) ^ 22752491534 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 68257474603) ^ 6 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_15972249057103 : Nat.Prime 15972249057103 := by
  apply lucas_primality 15972249057103 (6 : ZMod 15972249057103)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (13, 1), (68257474603, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (13, 1), (68257474603, 1)] : List FactorBlock).map factorBlockValue).prod = 15972249057103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_13
      · exact prime_septE_68257474603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 15972249057103) ^ 7986124528551 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 15972249057103) ^ 5324083019034 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 15972249057103) ^ 1228634542854 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 15972249057103) ^ 234 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_575000966055709 : Nat.Prime 575000966055709 := by
  apply lucas_primality 575000966055709 (2 : ZMod 575000966055709)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (15972249057103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (15972249057103, 1)] : List FactorBlock).map factorBlockValue).prod = 575000966055709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_15972249057103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 575000966055709) ^ 287500483027854 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 575000966055709) ^ 191666988685236 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 575000966055709) ^ 36 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_76161177957942879887 : Nat.Prime 76161177957942879887 := by
  apply lucas_primality 76161177957942879887 (5 : ZMod 76161177957942879887)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (9461, 1), (575000966055709, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (9461, 1), (575000966055709, 1)] : List FactorBlock).map factorBlockValue).prod = 76161177957942879887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_9461
      · exact prime_septE_575000966055709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 76161177957942879887) ^ 38080588978971439943 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 76161177957942879887) ^ 10880168279706125698 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 76161177957942879887) ^ 8050013524779926 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 76161177957942879887) ^ 132454 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_23463297631 : Nat.Prime 23463297631 := by
  apply lucas_primality 23463297631 (6 : ZMod 23463297631)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (14449, 1), (18043, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (14449, 1), (18043, 1)] : List FactorBlock).map factorBlockValue).prod = 23463297631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_14449
      · exact prime_septE_18043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 23463297631) ^ 11731648815 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 23463297631) ^ 7821099210 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 23463297631) ^ 4692659526 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 23463297631) ^ 1623870 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 23463297631) ^ 1300410 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_78585209989176375449 : Nat.Prime 78585209989176375449 := by
  apply lucas_primality 78585209989176375449 (3 : ZMod 78585209989176375449)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (13505171, 1), (23463297631, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (13505171, 1), (23463297631, 1)] : List FactorBlock).map factorBlockValue).prod = 78585209989176375449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_31
      · exact prime_septE_13505171
      · exact prime_septE_23463297631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 78585209989176375449) ^ 39292604994588187724 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 78585209989176375449) ^ 2535006773844399208 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 78585209989176375449) ^ 5818897812488 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 78585209989176375449) ^ 3349282408 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_73987284121 : Nat.Prime 73987284121 := by
  apply lucas_primality 73987284121 (29 : ZMod 73987284121)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod = 73987284121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_23
      · exact prime_septE_73
      · exact prime_septE_367219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 73987284121) ^ 36993642060 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 24662428040 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 14797456824 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 3216838440 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 1013524440 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 201480 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_93639150386551147643 : Nat.Prime 93639150386551147643 := by
  apply lucas_primality 93639150386551147643 (2 : ZMod 93639150386551147643)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod = 93639150386551147643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_11
      · exact prime_septE_139
      · exact prime_septE_413869
      · exact prime_septE_73987284121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93639150386551147643) ^ 46819575193275573821 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 8512650035141013422 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 673662952421231278 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 226253114842018 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 1265611402 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_389938247 : Nat.Prime 389938247 := by
  apply lucas_primality 389938247 (5 : ZMod 389938247)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (223, 1), (874301, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (223, 1), (874301, 1)] : List FactorBlock).map factorBlockValue).prod = 389938247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_223
      · exact prime_septE_874301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 389938247) ^ 194969123 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 389938247) ^ 1748602 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 389938247) ^ 446 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_145461232974775570669 : Nat.Prime 145461232974775570669 := by
  apply lucas_primality 145461232974775570669 (10 : ZMod 145461232974775570669)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (383, 1), (431, 1), (62773, 1), (389938247, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (383, 1), (431, 1), (62773, 1), (389938247, 1)] : List FactorBlock).map factorBlockValue).prod = 145461232974775570669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_383
      · exact prime_septE_431
      · exact prime_septE_62773
      · exact prime_septE_389938247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 145461232974775570669) ^ 72730616487387785334 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 145461232974775570669) ^ 48487077658258523556 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 145461232974775570669) ^ 379794341970693396 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 145461232974775570669) ^ 337497060266300628 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 145461232974775570669) ^ 2317257944893116 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 145461232974775570669) ^ 373036587444 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_97937826197793863 : Nat.Prime 97937826197793863 := by
  apply lucas_primality 97937826197793863 (5 : ZMod 97937826197793863)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (89, 1), (167, 1), (316097, 1), (1489003, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (89, 1), (167, 1), (316097, 1), (1489003, 1)] : List FactorBlock).map factorBlockValue).prod = 97937826197793863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_89
      · exact prime_septE_167
      · exact prime_septE_316097
      · exact prime_septE_1489003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97937826197793863) ^ 48968913098896931 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 13991118028256266 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 1100425013458358 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 586454049088586 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 309834722246 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 65774095954 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_361586454322254942197 : Nat.Prime 361586454322254942197 := by
  apply lucas_primality 361586454322254942197 (2 : ZMod 361586454322254942197)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (71, 1), (97937826197793863, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (71, 1), (97937826197793863, 1)] : List FactorBlock).map factorBlockValue).prod = 361586454322254942197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_13
      · exact prime_septE_71
      · exact prime_septE_97937826197793863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 361586454322254942197) ^ 180793227161127471098 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 27814342640173457092 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 5092766962285280876 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 3692 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_20319607769 : Nat.Prime 20319607769 := by
  apply lucas_primality 20319607769 (3 : ZMod 20319607769)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5881, 1), (431891, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5881, 1), (431891, 1)] : List FactorBlock).map factorBlockValue).prod = 20319607769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5881
      · exact prime_septE_431891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20319607769) ^ 10159803884 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 20319607769) ^ 3455128 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 20319607769) ^ 47048 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_607348163015529886877 : Nat.Prime 607348163015529886877 := by
  apply lucas_primality 607348163015529886877 (2 : ZMod 607348163015529886877)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2837, 1), (2633923, 1), (20319607769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2837, 1), (2633923, 1), (20319607769, 1)] : List FactorBlock).map factorBlockValue).prod = 607348163015529886877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_2837
      · exact prime_septE_2633923
      · exact prime_septE_20319607769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 607348163015529886877) ^ 303674081507764943438 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 214081129014991148 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 230586908962612 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 29889758204 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_34081261 : Nat.Prime 34081261 := by
  apply lucas_primality 34081261 (2 : ZMod 34081261)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (17, 1), (33413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (17, 1), (33413, 1)] : List FactorBlock).map factorBlockValue).prod = 34081261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_17
      · exact prime_septE_33413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34081261) ^ 17040630 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 34081261) ^ 11360420 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 34081261) ^ 6816252 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 34081261) ^ 2004780 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 34081261) ^ 1020 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_167426535252945869317 : Nat.Prime 167426535252945869317 := by
  apply lucas_primality 167426535252945869317 (6 : ZMod 167426535252945869317)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (13, 1), (229, 1), (15279391, 1), (34081261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (13, 1), (229, 1), (15279391, 1), (34081261, 1)] : List FactorBlock).map factorBlockValue).prod = 167426535252945869317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_13
      · exact prime_septE_229
      · exact prime_septE_15279391
      · exact prime_septE_34081261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 167426535252945869317) ^ 83713267626472934658 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 167426535252945869317) ^ 55808845084315289772 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 167426535252945869317) ^ 12878964250226605332 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 167426535252945869317) ^ 731120241279239604 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 167426535252945869317) ^ 10957670711676 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 167426535252945869317) ^ 4912568676756 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_669706141011783477269 : Nat.Prime 669706141011783477269 := by
  apply lucas_primality 669706141011783477269 (2 : ZMod 669706141011783477269)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (167426535252945869317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (167426535252945869317, 1)] : List FactorBlock).map factorBlockValue).prod = 669706141011783477269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_167426535252945869317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 669706141011783477269) ^ 334853070505891738634 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 669706141011783477269) ^ 4 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_24079071829 : Nat.Prime 24079071829 := by
  apply lucas_primality 24079071829 (2 : ZMod 24079071829)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (8287, 1), (34591, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (8287, 1), (34591, 1)] : List FactorBlock).map factorBlockValue).prod = 24079071829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_8287
      · exact prime_septE_34591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24079071829) ^ 12039535914 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 24079071829) ^ 8026357276 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 24079071829) ^ 3439867404 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 24079071829) ^ 2905644 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 24079071829) ^ 696108 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_28569770566964843 : Nat.Prime 28569770566964843 := by
  apply lucas_primality 28569770566964843 (2 : ZMod 28569770566964843)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (34897, 1), (24079071829, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (34897, 1), (24079071829, 1)] : List FactorBlock).map factorBlockValue).prod = 28569770566964843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_17
      · exact prime_septE_34897
      · exact prime_septE_24079071829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28569770566964843) ^ 14284885283482421 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 28569770566964843) ^ 1680574739233226 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 28569770566964843) ^ 818688442186 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 28569770566964843) ^ 1186498 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_841494022279382485723 : Nat.Prime 841494022279382485723 := by
  apply lucas_primality 841494022279382485723 (2 : ZMod 841494022279382485723)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (4909, 1), (28569770566964843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (4909, 1), (28569770566964843, 1)] : List FactorBlock).map factorBlockValue).prod = 841494022279382485723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_4909
      · exact prime_septE_28569770566964843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 841494022279382485723) ^ 420747011139691242861 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 841494022279382485723) ^ 280498007426460828574 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 841494022279382485723) ^ 171418623401789058 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 841494022279382485723) ^ 29454 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_126410709323573137 : Nat.Prime 126410709323573137 := by
  apply lucas_primality 126410709323573137 (5 : ZMod 126410709323573137)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (7, 1), (11, 1), (31, 1), (70141, 1), (5243207, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (7, 1), (11, 1), (31, 1), (70141, 1), (5243207, 1)] : List FactorBlock).map factorBlockValue).prod = 126410709323573137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_31
      · exact prime_septE_70141
      · exact prime_septE_5243207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 126410709323573137) ^ 63205354661786568 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 126410709323573137) ^ 42136903107857712 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 126410709323573137) ^ 18058672760510448 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 126410709323573137) ^ 11491882665779376 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 126410709323573137) ^ 4077764816889456 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 126410709323573137) ^ 1802237055696 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 126410709323573137) ^ 24109425648 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1827646035400220414747 : Nat.Prime 1827646035400220414747 := by
  apply lucas_primality 1827646035400220414747 (2 : ZMod 1827646035400220414747)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7229, 1), (126410709323573137, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7229, 1), (126410709323573137, 1)] : List FactorBlock).map factorBlockValue).prod = 1827646035400220414747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7229
      · exact prime_septE_126410709323573137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1827646035400220414747) ^ 913823017700110207373 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1827646035400220414747) ^ 252821418647146274 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1827646035400220414747) ^ 14458 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_856838051 : Nat.Prime 856838051 := by
  apply lucas_primality 856838051 (2 : ZMod 856838051)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (83, 1), (206467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (83, 1), (206467, 1)] : List FactorBlock).map factorBlockValue).prod = 856838051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_83
      · exact prime_septE_206467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 856838051) ^ 428419025 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 856838051) ^ 171367610 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 856838051) ^ 10323350 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 856838051) ^ 4150 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_6165806614997 : Nat.Prime 6165806614997 := by
  apply lucas_primality 6165806614997 (2 : ZMod 6165806614997)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (257, 1), (856838051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (257, 1), (856838051, 1)] : List FactorBlock).map factorBlockValue).prod = 6165806614997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_257
      · exact prime_septE_856838051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6165806614997) ^ 3082903307498 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 6165806614997) ^ 880829516428 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 6165806614997) ^ 23991465428 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 6165806614997) ^ 7196 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_433579521166589041 : Nat.Prime 433579521166589041 := by
  apply lucas_primality 433579521166589041 (11 : ZMod 433579521166589041)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (293, 1), (6165806614997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (293, 1), (6165806614997, 1)] : List FactorBlock).map factorBlockValue).prod = 433579521166589041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_293
      · exact prime_septE_6165806614997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 433579521166589041) ^ 216789760583294520 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 433579521166589041) ^ 144526507055529680 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 433579521166589041) ^ 86715904233317808 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 433579521166589041) ^ 1479793587599280 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 433579521166589041) ^ 70320 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1930296028233654410533 : Nat.Prime 1930296028233654410533 := by
  apply lucas_primality 1930296028233654410533 (2 : ZMod 1930296028233654410533)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (53, 1), (433579521166589041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (53, 1), (433579521166589041, 1)] : List FactorBlock).map factorBlockValue).prod = 1930296028233654410533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_53
      · exact prime_septE_433579521166589041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1930296028233654410533) ^ 965148014116827205266 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1930296028233654410533) ^ 643432009411218136844 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1930296028233654410533) ^ 275756575461950630076 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1930296028233654410533) ^ 36420679777993479444 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1930296028233654410533) ^ 4452 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_35279
      · exact prime_septE_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_61717
      · exact prime_septE_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_19
      · exact prime_septE_107
      · exact prime_septE_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_53364341 : Nat.Prime 53364341 := by
  apply lucas_primality 53364341 (2 : ZMod 53364341)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (2668217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (2668217, 1)] : List FactorBlock).map factorBlockValue).prod = 53364341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_2668217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53364341) ^ 26682170 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 53364341) ^ 10672868 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 53364341) ^ 20 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_2894746241761246744873 : Nat.Prime 2894746241761246744873 := by
  apply lucas_primality 2894746241761246744873 (5 : ZMod 2894746241761246744873)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 2), (11, 1), (13, 1), (17, 1), (18974357, 1), (53364341, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 2), (11, 1), (13, 1), (17, 1), (18974357, 1), (53364341, 1)] : List FactorBlock).map factorBlockValue).prod = 2894746241761246744873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_18974357
      · exact prime_septE_53364341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2894746241761246744873) ^ 1447373120880623372436 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2894746241761246744873) ^ 964915413920415581624 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2894746241761246744873) ^ 413535177394463820696 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2894746241761246744873) ^ 263158749251022431352 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2894746241761246744873) ^ 222672787827788211144 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2894746241761246744873) ^ 170279190691838043816 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2894746241761246744873) ^ 152560966453896 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 2894746241761246744873) ^ 54244954355592 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_3139143389 : Nat.Prime 3139143389 := by
  apply lucas_primality 3139143389 (2 : ZMod 3139143389)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod = 3139143389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_359
      · exact prime_septE_677
      · exact prime_septE_3229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3139143389) ^ 1569571694 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 8744132 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 4636844 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 972172 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_4712696973609818164547 : Nat.Prime 4712696973609818164547 := by
  apply lucas_primality 4712696973609818164547 (2 : ZMod 4712696973609818164547)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod = 4712696973609818164547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_17
      · exact prime_septE_29
      · exact prime_septE_431
      · exact prime_septE_3532679
      · exact prime_septE_3139143389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4712696973609818164547) ^ 2356348486804909082273 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 277217469035871656738 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 162506792193442005674 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 10934331725312803166 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1334029209449774 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1501268463914 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_33421867861 : Nat.Prime 33421867861 := by
  apply lucas_primality 33421867861 (2 : ZMod 33421867861)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (1787, 1), (311713, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (1787, 1), (311713, 1)] : List FactorBlock).map factorBlockValue).prod = 33421867861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_1787
      · exact prime_septE_311713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33421867861) ^ 16710933930 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 33421867861) ^ 11140622620 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 33421867861) ^ 6684373572 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 33421867861) ^ 18702780 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 33421867861) ^ 107220 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_2606905693159 : Nat.Prime 2606905693159 := by
  apply lucas_primality 2606905693159 (3 : ZMod 2606905693159)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (33421867861, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (33421867861, 1)] : List FactorBlock).map factorBlockValue).prod = 2606905693159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_13
      · exact prime_septE_33421867861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2606905693159) ^ 1303452846579 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 2606905693159) ^ 868968564386 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 2606905693159) ^ 200531207166 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 2606905693159) ^ 78 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_4970987010548652822191 : Nat.Prime 4970987010548652822191 := by
  apply lucas_primality 4970987010548652822191 (7 : ZMod 4970987010548652822191)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (11, 1), (23, 1), (107671, 1), (2606905693159, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (11, 1), (23, 1), (107671, 1), (2606905693159, 1)] : List FactorBlock).map factorBlockValue).prod = 4970987010548652822191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_23
      · exact prime_septE_107671
      · exact prime_septE_2606905693159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4970987010548652822191) ^ 2485493505274326411095 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 4970987010548652822191) ^ 994197402109730564438 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 4970987010548652822191) ^ 710141001506950403170 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 4970987010548652822191) ^ 451907910049877529290 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 4970987010548652822191) ^ 216129870023854470530 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 4970987010548652822191) ^ 46168299825845890 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 4970987010548652822191) ^ 1906853410 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_142598237 : Nat.Prime 142598237 := by
  apply lucas_primality 142598237 (2 : ZMod 142598237)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (61, 1), (53129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (61, 1), (53129, 1)] : List FactorBlock).map factorBlockValue).prod = 142598237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_11
      · exact prime_septE_61
      · exact prime_septE_53129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 142598237) ^ 71299118 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 142598237) ^ 12963476 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 142598237) ^ 2337676 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 142598237) ^ 2684 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_6874478291154704700553 : Nat.Prime 6874478291154704700553 := by
  apply lucas_primality 6874478291154704700553 (7 : ZMod 6874478291154704700553)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (821, 1), (13163, 1), (185873, 1), (142598237, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (821, 1), (13163, 1), (185873, 1), (142598237, 1)] : List FactorBlock).map factorBlockValue).prod = 6874478291154704700553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_821
      · exact prime_septE_13163
      · exact prime_septE_185873
      · exact prime_septE_142598237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6874478291154704700553) ^ 3437239145577352350276 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 6874478291154704700553) ^ 2291492763718234900184 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 6874478291154704700553) ^ 8373298771199396712 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 6874478291154704700553) ^ 522257714134673304 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 6874478291154704700553) ^ 36984813776905224 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 6874478291154704700553) ^ 48208718675496 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_17332122450967 : Nat.Prime 17332122450967 := by
  apply lucas_primality 17332122450967 (3 : ZMod 17332122450967)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (37, 1), (41, 1), (30911, 1), (61603, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (37, 1), (41, 1), (30911, 1), (61603, 1)] : List FactorBlock).map factorBlockValue).prod = 17332122450967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_30911
      · exact prime_septE_61603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17332122450967) ^ 8666061225483 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 17332122450967) ^ 5777374150322 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 17332122450967) ^ 468435741918 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 17332122450967) ^ 422734693926 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 17332122450967) ^ 560710506 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 17332122450967) ^ 281351922 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_7439082943787786687083 : Nat.Prime 7439082943787786687083 := by
  apply lucas_primality 7439082943787786687083 (2 : ZMod 7439082943787786687083)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1231, 1), (58111, 1), (17332122450967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1231, 1), (58111, 1), (17332122450967, 1)] : List FactorBlock).map factorBlockValue).prod = 7439082943787786687083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_1231
      · exact prime_septE_58111
      · exact prime_septE_17332122450967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7439082943787786687083) ^ 3719541471893893343541 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7439082943787786687083) ^ 2479694314595928895694 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7439082943787786687083) ^ 6043121806488860022 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7439082943787786687083) ^ 128015056422842262 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 7439082943787786687083) ^ 429207846 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_216317813 : Nat.Prime 216317813 := by
  apply lucas_primality 216317813 (2 : ZMod 216317813)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod = 216317813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_19
      · exact prime_septE_2846287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 216317813) ^ 108158906 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 11385148 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 76 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_11380112522338097407091 : Nat.Prime 11380112522338097407091 := by
  apply lucas_primality 11380112522338097407091 (2 : ZMod 11380112522338097407091)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod = 11380112522338097407091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_13
      · exact prime_septE_67
      · exact prime_septE_19379
      · exact prime_septE_311677
      · exact prime_septE_216317813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11380112522338097407091) ^ 5690056261169048703545 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 2276022504467619481418 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 875393270949084415930 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 169852425706538767270 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 587239409790912710 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 36512519442686170 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 52608300557930 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_26209442713 : Nat.Prime 26209442713 := by
  apply lucas_primality 26209442713 (5 : ZMod 26209442713)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (613, 1), (761, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (613, 1), (761, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod = 26209442713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_613
      · exact prime_septE_761
      · exact prime_septE_2341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 26209442713) ^ 13104721356 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 26209442713) ^ 8736480904 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 26209442713) ^ 42756024 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 26209442713) ^ 34440792 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 26209442713) ^ 11195832 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_18241772128249 : Nat.Prime 18241772128249 := by
  apply lucas_primality 18241772128249 (7 : ZMod 18241772128249)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (29, 1), (26209442713, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (29, 1), (26209442713, 1)] : List FactorBlock).map factorBlockValue).prod = 18241772128249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_29
      · exact prime_septE_26209442713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 18241772128249) ^ 9120886064124 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 18241772128249) ^ 6080590709416 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 18241772128249) ^ 629026625112 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 18241772128249) ^ 696 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_19903269217234175419 : Nat.Prime 19903269217234175419 := by
  apply lucas_primality 19903269217234175419 (3 : ZMod 19903269217234175419)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (43, 1), (4229, 1), (18241772128249, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (43, 1), (4229, 1), (18241772128249, 1)] : List FactorBlock).map factorBlockValue).prod = 19903269217234175419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_43
      · exact prime_septE_4229
      · exact prime_septE_18241772128249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19903269217234175419) ^ 9951634608617087709 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 19903269217234175419) ^ 6634423072411391806 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 19903269217234175419) ^ 462866725982190126 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 19903269217234175419) ^ 4706377209088242 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 19903269217234175419) ^ 1091082 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_31725811132271275617887 : Nat.Prime 31725811132271275617887 := by
  apply lucas_primality 31725811132271275617887 (5 : ZMod 31725811132271275617887)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (797, 1), (19903269217234175419, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (797, 1), (19903269217234175419, 1)] : List FactorBlock).map factorBlockValue).prod = 31725811132271275617887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_797
      · exact prime_septE_19903269217234175419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 31725811132271275617887) ^ 15862905566135637808943 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 31725811132271275617887) ^ 39806538434468350838 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 31725811132271275617887) ^ 1594 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_596057951 : Nat.Prime 596057951 := by
  apply lucas_primality 596057951 (11 : ZMod 596057951)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (2803, 1), (4253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (2803, 1), (4253, 1)] : List FactorBlock).map factorBlockValue).prod = 596057951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_2803
      · exact prime_septE_4253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 596057951) ^ 298028975 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 596057951) ^ 119211590 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 596057951) ^ 212650 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (11 : ZMod 596057951) ^ 140150 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_45573398817559 : Nat.Prime 45573398817559 := by
  apply lucas_primality 45573398817559 (6 : ZMod 45573398817559)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (12743, 1), (596057951, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (12743, 1), (596057951, 1)] : List FactorBlock).map factorBlockValue).prod = 45573398817559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_12743
      · exact prime_septE_596057951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 45573398817559) ^ 22786699408779 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 45573398817559) ^ 15191132939186 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 45573398817559) ^ 3576347706 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 45573398817559) ^ 76458 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_820321178716063 : Nat.Prime 820321178716063 := by
  apply lucas_primality 820321178716063 (3 : ZMod 820321178716063)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (45573398817559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (45573398817559, 1)] : List FactorBlock).map factorBlockValue).prod = 820321178716063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_45573398817559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 820321178716063) ^ 410160589358031 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 820321178716063) ^ 273440392905354 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 820321178716063) ^ 18 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_47520948302171412746219 : Nat.Prime 47520948302171412746219 := by
  apply lucas_primality 47520948302171412746219 (2 : ZMod 47520948302171412746219)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (43, 1), (29287, 1), (820321178716063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (43, 1), (29287, 1), (820321178716063, 1)] : List FactorBlock).map factorBlockValue).prod = 47520948302171412746219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_23
      · exact prime_septE_43
      · exact prime_septE_29287
      · exact prime_septE_820321178716063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47520948302171412746219) ^ 23760474151085706373109 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 47520948302171412746219) ^ 2066128187050930988966 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 47520948302171412746219) ^ 1105138332608637505726 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 47520948302171412746219) ^ 1622595291500372614 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 47520948302171412746219) ^ 57929686 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_38554545693913 : Nat.Prime 38554545693913 := by
  apply lucas_primality 38554545693913 (10 : ZMod 38554545693913)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod = 38554545693913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_59
      · exact prime_septE_293
      · exact prime_septE_317
      · exact prime_septE_293147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 38554545693913) ^ 19277272846956 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 12851515231304 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 653466876168 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131585480184 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 121623172536 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131519496 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_32457694465787711188511 : Nat.Prime 32457694465787711188511 := by
  apply lucas_primality 32457694465787711188511 (7 : ZMod 32457694465787711188511)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod = 32457694465787711188511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_13
      · exact prime_septE_6475879
      · exact prime_septE_38554545693913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32457694465787711188511) ^ 16228847232893855594255 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 6491538893157542237702 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 2496745728137516245270 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 5012090940208690 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 841864270 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_64915388931575422377023 : Nat.Prime 64915388931575422377023 := by
  apply lucas_primality 64915388931575422377023 (5 : ZMod 64915388931575422377023)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod = 64915388931575422377023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_32457694465787711188511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 64915388931575422377023) ^ 32457694465787711188511 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 64915388931575422377023) ^ 2 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1462090577 : Nat.Prime 1462090577 := by
  apply lucas_primality 1462090577 (6 : ZMod 1462090577)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (17, 1), (89, 1), (60397, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (17, 1), (89, 1), (60397, 1)] : List FactorBlock).map factorBlockValue).prod = 1462090577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_17
      · exact prime_septE_89
      · exact prime_septE_60397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1462090577) ^ 731045288 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 1462090577) ^ 86005328 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 1462090577) ^ 16427984 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (6 : ZMod 1462090577) ^ 24208 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_3911415413 : Nat.Prime 3911415413 := by
  apply lucas_primality 3911415413 (2 : ZMod 3911415413)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1069, 1), (914737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1069, 1), (914737, 1)] : List FactorBlock).map factorBlockValue).prod = 3911415413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_1069
      · exact prime_septE_914737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3911415413) ^ 1955707706 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 3911415413) ^ 3658948 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 3911415413) ^ 4276 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_270718619192664568942739 : Nat.Prime 270718619192664568942739 := by
  apply lucas_primality 270718619192664568942739 (2 : ZMod 270718619192664568942739)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23669, 1), (1462090577, 1), (3911415413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23669, 1), (1462090577, 1), (3911415413, 1)] : List FactorBlock).map factorBlockValue).prod = 270718619192664568942739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_23669
      · exact prime_septE_1462090577
      · exact prime_septE_3911415413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 270718619192664568942739) ^ 135359309596332284471369 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 270718619192664568942739) ^ 11437687236159726602 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 270718619192664568942739) ^ 185158582820594 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 270718619192664568942739) ^ 69212443734026 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_12213322787 : Nat.Prime 12213322787 := by
  apply lucas_primality 12213322787 (2 : ZMod 12213322787)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (277, 1), (3149387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (277, 1), (3149387, 1)] : List FactorBlock).map factorBlockValue).prod = 12213322787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_277
      · exact prime_septE_3149387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12213322787) ^ 6106661393 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 12213322787) ^ 1744760398 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 12213322787) ^ 44091418 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 12213322787) ^ 3878 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_13190388609961 : Nat.Prime 13190388609961 := by
  apply lucas_primality 13190388609961 (7 : ZMod 13190388609961)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (5, 1), (12213322787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (5, 1), (12213322787, 1)] : List FactorBlock).map factorBlockValue).prod = 13190388609961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_12213322787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 13190388609961) ^ 6595194304980 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 13190388609961) ^ 4396796203320 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 13190388609961) ^ 2638077721992 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 13190388609961) ^ 1080 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_158284663319533 : Nat.Prime 158284663319533 := by
  apply lucas_primality 158284663319533 (2 : ZMod 158284663319533)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13190388609961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13190388609961, 1)] : List FactorBlock).map factorBlockValue).prod = 158284663319533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_13190388609961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 158284663319533) ^ 79142331659766 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 158284663319533) ^ 52761554439844 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 158284663319533) ^ 12 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_403386049362436921065487 : Nat.Prime 403386049362436921065487 := by
  apply lucas_primality 403386049362436921065487 (5 : ZMod 403386049362436921065487)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (37, 1), (131, 1), (87631, 1), (158284663319533, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (37, 1), (131, 1), (87631, 1), (158284663319533, 1)] : List FactorBlock).map factorBlockValue).prod = 403386049362436921065487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_37
      · exact prime_septE_131
      · exact prime_septE_87631
      · exact prime_septE_158284663319533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 403386049362436921065487) ^ 201693024681218460532743 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 403386049362436921065487) ^ 134462016454145640355162 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 403386049362436921065487) ^ 10902325658444241109878 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 403386049362436921065487) ^ 3079282819560587183706 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 403386049362436921065487) ^ 4603234578658658706 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 403386049362436921065487) ^ 2548484742 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_21461729 : Nat.Prime 21461729 := by
  apply lucas_primality 21461729 (3 : ZMod 21461729)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (617, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (617, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod = 21461729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_617
      · exact prime_septE_1087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 21461729) ^ 10730864 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 21461729) ^ 34784 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 21461729) ^ 19744 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_807520332674926021 : Nat.Prime 807520332674926021 := by
  apply lucas_primality 807520332674926021 (2 : ZMod 807520332674926021)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (19, 1), (97, 1), (340261, 1), (21461729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (19, 1), (97, 1), (340261, 1), (21461729, 1)] : List FactorBlock).map factorBlockValue).prod = 807520332674926021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_19
      · exact prime_septE_97
      · exact prime_septE_340261
      · exact prime_septE_21461729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 807520332674926021) ^ 403760166337463010 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 807520332674926021) ^ 269173444224975340 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 807520332674926021) ^ 161504066534985204 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 807520332674926021) ^ 42501070140785580 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 807520332674926021) ^ 8324951883246660 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 807520332674926021) ^ 2373237992820 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 807520332674926021) ^ 37626061380 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_601618798249473384165421 : Nat.Prime 601618798249473384165421 := by
  apply lucas_primality 601618798249473384165421 (2 : ZMod 601618798249473384165421)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (4139, 1), (807520332674926021, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (4139, 1), (807520332674926021, 1)] : List FactorBlock).map factorBlockValue).prod = 601618798249473384165421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_4139
      · exact prime_septE_807520332674926021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 601618798249473384165421) ^ 300809399124736692082710 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 601618798249473384165421) ^ 200539599416491128055140 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 601618798249473384165421) ^ 120323759649894676833084 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 601618798249473384165421) ^ 145353659881486683780 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 601618798249473384165421) ^ 745020 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_315283291 : Nat.Prime 315283291 := by
  apply lucas_primality 315283291 (7 : ZMod 315283291)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (40577, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (40577, 1)] : List FactorBlock).map factorBlockValue).prod = 315283291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_37
      · exact prime_septE_40577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 315283291) ^ 157641645 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 105094430 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 63056658 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 45040470 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 8521170 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 315283291) ^ 7770 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_18054505621 : Nat.Prime 18054505621 := by
  apply lucas_primality 18054505621 (2 : ZMod 18054505621)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (751, 1), (133559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (751, 1), (133559, 1)] : List FactorBlock).map factorBlockValue).prod = 18054505621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_751
      · exact prime_septE_133559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18054505621) ^ 9027252810 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 6018168540 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 3610901124 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 24040620 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 18054505621) ^ 135180 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_58528063569446646906503 : Nat.Prime 58528063569446646906503 := by
  apply lucas_primality 58528063569446646906503 (5 : ZMod 58528063569446646906503)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (97, 1), (315283291, 1), (18054505621, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (97, 1), (315283291, 1), (18054505621, 1)] : List FactorBlock).map factorBlockValue).prod = 58528063569446646906503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_53
      · exact prime_septE_97
      · exact prime_septE_315283291
      · exact prime_septE_18054505621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 58528063569446646906503) ^ 29264031784723323453251 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 1104303086215974469934 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 603382098654089143366 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 185636426795122 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 58528063569446646906503) ^ 3241742798062 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_1170561271388932938130061 : Nat.Prime 1170561271388932938130061 := by
  apply lucas_primality 1170561271388932938130061 (2 : ZMod 1170561271388932938130061)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (58528063569446646906503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (58528063569446646906503, 1)] : List FactorBlock).map factorBlockValue).prod = 1170561271388932938130061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_58528063569446646906503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1170561271388932938130061) ^ 585280635694466469065030 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1170561271388932938130061) ^ 234112254277786587626012 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 1170561271388932938130061) ^ 20 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_13203689273969 : Nat.Prime 13203689273969 := by
  apply lucas_primality 13203689273969 (3 : ZMod 13203689273969)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod = 13203689273969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_37
      · exact prime_septE_971
      · exact prime_septE_1031
      · exact prime_septE_22279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13203689273969) ^ 6601844636984 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 356856466864 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 13598032208 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 12806682128 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 592651792 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_5360018256942847067732857 : Nat.Prime 5360018256942847067732857 := by
  apply lucas_primality 5360018256942847067732857 (5 : ZMod 5360018256942847067732857)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod = 5360018256942847067732857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_239
      · exact prime_septE_4519
      · exact prime_septE_15661
      · exact prime_septE_13203689273969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5360018256942847067732857) ^ 2680009128471423533866428 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1786672752314282355910952 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 22426854631560029572104 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1186107160199789127624 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 342252618411522065496 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 405948530424 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_6044411890991 : Nat.Prime 6044411890991 := by
  apply lucas_primality 6044411890991 (13 : ZMod 6044411890991)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (389, 1), (761, 1), (185621, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (389, 1), (761, 1), (185621, 1)] : List FactorBlock).map factorBlockValue).prod = 6044411890991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_11
      · exact prime_septE_389
      · exact prime_septE_761
      · exact prime_septE_185621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 6044411890991) ^ 3022205945495 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 6044411890991) ^ 1208882378198 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 6044411890991) ^ 549491990090 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 6044411890991) ^ 15538333910 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 6044411890991) ^ 7942722590 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 6044411890991) ^ 32563190 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_5676178455912041064869363 : Nat.Prime 5676178455912041064869363 := by
  apply lucas_primality 5676178455912041064869363 (2 : ZMod 5676178455912041064869363)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (127, 1), (751, 1), (378691, 1), (6044411890991, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (127, 1), (751, 1), (378691, 1), (6044411890991, 1)] : List FactorBlock).map factorBlockValue).prod = 5676178455912041064869363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_13
      · exact prime_septE_127
      · exact prime_septE_751
      · exact prime_septE_378691
      · exact prime_septE_6044411890991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5676178455912041064869363) ^ 2838089227956020532434681 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5676178455912041064869363) ^ 436629111993233928066874 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5676178455912041064869363) ^ 44694318550488512321806 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5676178455912041064869363) ^ 7558160394024022722862 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5676178455912041064869363) ^ 14988944696103263782 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 5676178455912041064869363) ^ 939078699182 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_22951043 : Nat.Prime 22951043 := by
  apply lucas_primality 22951043 (2 : ZMod 22951043)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1303, 1), (8807, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1303, 1), (8807, 1)] : List FactorBlock).map factorBlockValue).prod = 22951043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_1303
      · exact prime_septE_8807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22951043) ^ 11475521 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951043) ^ 17614 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951043) ^ 2606 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_21910764024983 : Nat.Prime 21910764024983 := by
  apply lucas_primality 21910764024983 (5 : ZMod 21910764024983)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod = 21910764024983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_7
      · exact prime_septE_19
      · exact prime_septE_37
      · exact prime_septE_97
      · exact prime_septE_22951043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21910764024983) ^ 10955382012491 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 3130109146426 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 1153198106578 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 592182811486 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 225884165206 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 954674 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_180018837229260329 : Nat.Prime 180018837229260329 := by
  apply lucas_primality 180018837229260329 (3 : ZMod 180018837229260329)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod = 180018837229260329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_13
      · exact prime_septE_79
      · exact prime_septE_21910764024983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 180018837229260329) ^ 90009418614630164 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 13847602863789256 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 2278719458598232 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 8216 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_18597456603864619938380969 : Nat.Prime 18597456603864619938380969 := by
  apply lucas_primality 18597456603864619938380969 (3 : ZMod 18597456603864619938380969)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod = 18597456603864619938380969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_11
      · exact prime_septE_1173959
      · exact prime_septE_180018837229260329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18597456603864619938380969) ^ 9298728301932309969190484 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 1690677873078601812580088 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 15841657676174908952 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 103308392 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_39530687550041 : Nat.Prime 39530687550041 := by
  apply lucas_primality 39530687550041 (3 : ZMod 39530687550041)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod = 39530687550041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_5
      · exact prime_septE_101
      · exact prime_septE_5779
      · exact prime_septE_1693169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39530687550041) ^ 19765343775020 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 7906137510008 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 391392946040 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 6840402760 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 23347160 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_20135932332651474142529273 : Nat.Prime 20135932332651474142529273 := by
  apply lucas_primality 20135932332651474142529273 (3 : ZMod 20135932332651474142529273)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod = 20135932332651474142529273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_17
      · exact prime_septE_991
      · exact prime_septE_3779417
      · exact prime_septE_39530687550041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20135932332651474142529273) ^ 10067966166325737071264636 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 1184466607803027890737016 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 20318801546570609629192 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 5327787945244325816 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 509374705592 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_103448352358996948407244141 : Nat.Prime 103448352358996948407244141 := by
  apply lucas_primality 103448352358996948407244141 (2 : ZMod 103448352358996948407244141)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 1), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 1), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 103448352358996948407244141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 103448352358996948407244141) ^ 51724176179498474203622070 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 34482784119665649469081380 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 20689670471799389681448828 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 14778336051285278343892020 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 9404395668999722582476740 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 7957565566076688339018780 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 6085197197588055788661420 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 5444650124157734126697060 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 4497754450391171669880180 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 3567184564103343048525660 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 3337043624483772529265940 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 2795901415108025632628220 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 2523130545341388985542540 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 2405775636255742986214980 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 2201028773595679753345620 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 1951855704886734875608380 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 1753361904389778786563460 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (2 : ZMod 103448352358996948407244141) ^ 1695874628836015547659740 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_107478807645711115228305601 : Nat.Prime 107478807645711115228305601 := by
  apply lucas_primality 107478807645711115228305601 (67 : ZMod 107478807645711115228305601)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 107478807645711115228305601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 107478807645711115228305601) ^ 53739403822855557614152800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 35826269215237038409435200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 21495761529142223045661120 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 15354115377958730746900800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 8267600588131624248331200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 6322282802688889131076800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 5656779349774269222542400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 4672991636770048488187200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 3706165780886590180286400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 3467058311151971458977600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2904832639073273384548800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2621434332822222322641600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2499507154551421284379200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2286783141398108834644800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 2027902031051153117515200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 1821674705859510427598400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 107478807645711115228305601) ^ 1761947666323133036529600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_131362987122535807501262401 : Nat.Prime 131362987122535807501262401 := by
  apply lucas_primality 131362987122535807501262401 (71 : ZMod 131362987122535807501262401)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 131362987122535807501262401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 131362987122535807501262401) ^ 65681493561267903750631200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 43787662374178602500420800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 26272597424507161500252480 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 18766141017505115357323200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 11942089738412346136478400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 10104845163271985192404800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 7727234536619753382427200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 6913841427501884605329600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 5711434222718948152228800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 4529758176639165775905600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 4237515713630187338750400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3550351003311778581115200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3203975295671605061006400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 3054953188896181569796800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2794957172819910797899200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2478546926840298254740800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2226491307161623855953600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (71 : ZMod 131362987122535807501262401) ^ 2153491592172718155758400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_179910178015646866795207201 : Nat.Prime 179910178015646866795207201 := by
  apply lucas_primality 179910178015646866795207201 (79 : ZMod 179910178015646866795207201)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 179910178015646866795207201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 179910178015646866795207201) ^ 89955089007823433397603600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 59970059338548955598402400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 35982035603129373359041440 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 25701454002235266685029600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 16355470728695169708655200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 13839244462742066676554400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 10582951647979227458541600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 9468956737665624568168800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 6203799241918857475696800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 5803554129536995703071200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 4862437243666131535005600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 4388053122332850409639200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 4183957628270857367330400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 3827876127992486527557600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 3394531660672582392362400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 3049325051112658759240800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (79 : ZMod 179910178015646866795207201) ^ 2949347180584374865495200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_201850443627311118843403201 : Nat.Prime 201850443627311118843403201 := by
  apply lucas_primality 201850443627311118843403201 (41 : ZMod 201850443627311118843403201)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 201850443627311118843403201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (41 : ZMod 201850443627311118843403201) ^ 100925221813655559421701600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 67283481209103706281134400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 40370088725462223768680640 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 28835777661044445549057600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 18350040329755556258491200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 15526957202100855295646400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 11873555507488889343729600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 10623707559332164149652800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 8776106244665700819278400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 6960360125079693753220800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 6511304633139068349787200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 5455417395332732941713600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 4694196363425839973102400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 4294690289942789762625600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 3808498936364360732894400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 3421193959784934217684800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (41 : ZMod 201850443627311118843403201) ^ 3309023666021493751531200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_212201748428711689040500801 : Nat.Prime 212201748428711689040500801 := by
  apply lucas_primality 212201748428711689040500801 (13 : ZMod 212201748428711689040500801)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 3), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 3), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 212201748428711689040500801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 212201748428711689040500801) ^ 106100874214355844520250400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 70733916142903896346833600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 42440349685742337808100160 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 30314535489815955577214400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 19291068038973789912772800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 12482455789924217002382400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 11168513075195352054763200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 9226162975161377784369600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 7317301669955575484155200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 6845217691248764162596800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 5735182389965180784878400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 5175652400700285098548800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 4934924382063062535825600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 4514930817632163596606400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 4003806574126635642273600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 3596639803876469305771200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (13 : ZMod 212201748428711689040500801) ^ 3478717187355929328532800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_285374765128267443882052801 : Nat.Prime 285374765128267443882052801 := by
  apply lucas_primality 285374765128267443882052801 (29 : ZMod 285374765128267443882052801)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 285374765128267443882052801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 285374765128267443882052801) ^ 142687382564133721941026400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 95124921709422481294017600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 57074953025653488776410560 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 40767823589752491983150400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 25943160466206131262004800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 21951905009866726452465600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 16786750889898084934238400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 15019724480435128625371200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 12407598483837714951393600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 9205637584782820770388800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 7712831489953174158974400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 6960360125079693753220800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 6636622444843428927489600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 6071803513367392423022400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 5384429530722027243057600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 4836860425902838031899200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 4678274838168318752164800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_331034727548790234903181249 : Nat.Prime 331034727548790234903181249 := by
  apply lucas_primality 331034727548790234903181249 (67 : ZMod 331034727548790234903181249)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 331034727548790234903181249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 331034727548790234903181249) ^ 165517363774395117451590624 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 110344909182930078301060416 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 47290675364112890700454464 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 30094066140799112263925568 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 25464209811445402684860096 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 19472631032281778523716544 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 17422880397304749205430592 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 14392814241251749343616576 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 11414990605130697755282112 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 10678539598348072093651008 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 8946884528345682024410304 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 8074017745092444753736128 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 7698482036018377555887936 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 7043292075506175210705984 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 6245938255637551601946816 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 5610758094047292117003072 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 5426798812275249752511168 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_344827841196656494690813801 : Nat.Prime 344827841196656494690813801 := by
  apply lucas_primality 344827841196656494690813801 (97 : ZMod 344827841196656494690813801)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 344827841196656494690813801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 344827841196656494690813801) ^ 172413920598328247345406900 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 114942613732218831563604600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 68965568239331298938162760 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 49261120170950927812973400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 31347985563332408608255800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 26525218553588961130062600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 20283990658626852628871400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 18148833747192447088990200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 14992514834637238899600600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 11890615213677810161752200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 11123478748279241764219800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 9319671383693418775427400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 8410435151137963285141800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 8019252120852476620716600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 7336762578652265844485400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 6506185682955782918694600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 5844539681299262621878200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 5652915429453385158865800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_376175826759988903299069601 : Nat.Prime 376175826759988903299069601 := by
  apply lucas_primality 376175826759988903299069601 (33 : ZMod 376175826759988903299069601)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 376175826759988903299069601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 376175826759988903299069601) ^ 188087913379994451649534800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 125391942253329634433023200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 75235165351997780659813920 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 53739403822855557614152800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 28936602058460684869159200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 22127989809411111958768800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 19798727724209942278898400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 16355470728695169708655200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 12971580233103065631002400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 12134704089031900106421600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 10166914236756456845920800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 9175020164877778129245600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 8748275040929974495327200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 8003740994893380921256800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 7097657108679035911303200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 6375861470508286496594400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 6166816832130965627853600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_752351653519977806598139201 : Nat.Prime 752351653519977806598139201 := by
  apply lucas_primality 752351653519977806598139201 (22 : ZMod 752351653519977806598139201)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 752351653519977806598139201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 752351653519977806598139201) ^ 376175826759988903299069600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 250783884506659268866046400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 150470330703995561319627840 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 107478807645711115228305600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 57873204116921369738318400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 44255979618822223917537600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 39597455448419884557796800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 32710941457390339417310400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 25943160466206131262004800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 24269408178063800212843200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 20333828473512913691841600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 18350040329755556258491200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 17496550081859948990654400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 16007481989786761842513600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 14195314217358071822606400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12751722941016572993188800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12333633664261931255707200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_919540909857750652508836801 : Nat.Prime 919540909857750652508836801 := by
  apply lucas_primality 919540909857750652508836801 (113 : ZMod 919540909857750652508836801)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 919540909857750652508836801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_5
      · exact prime_septE_7
      · exact prime_septE_11
      · exact prime_septE_13
      · exact prime_septE_17
      · exact prime_septE_19
      · exact prime_septE_23
      · exact prime_septE_29
      · exact prime_septE_31
      · exact prime_septE_37
      · exact prime_septE_41
      · exact prime_septE_43
      · exact prime_septE_47
      · exact prime_septE_53
      · exact prime_septE_59
      · exact prime_septE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 919540909857750652508836801) ^ 459770454928875326254418400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 306513636619250217502945600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 183908181971550130501767360 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 131362987122535807501262400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 83594628168886422955348800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 70733916142903896346833600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 54090641756338273676990400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 48396889992513192237307200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 39980039559032637065601600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 31708307236474160431339200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 29662609995411311371252800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 24852457023182450067806400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 22427827069701235427044800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 21384672322273270988577600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 19564700209739375585294400 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 17349828487882087783185600 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15585439150131366991675200 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15074441145209027090308800 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem prime_septE_8275868188719755872579531297 : Nat.Prime 8275868188719755872579531297 := by
  apply lucas_primality 8275868188719755872579531297 (7 : ZMod 8275868188719755872579531297)
  · rw [← septFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (1481, 1), (6863, 1), (78889, 1), (107511970941253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (1481, 1), (6863, 1), (78889, 1), (107511970941253, 1)] : List FactorBlock).map factorBlockValue).prod = 8275868188719755872579531297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_septE_2
      · exact prime_septE_3
      · exact prime_septE_1481
      · exact prime_septE_6863
      · exact prime_septE_78889
      · exact prime_septE_107511970941253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8275868188719755872579531297) ^ 4137934094359877936289765648 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 8275868188719755872579531297) ^ 2758622729573251957526510432 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 8275868188719755872579531297) ^ 5588027136205101872099616 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 8275868188719755872579531297) ^ 1205867432423102997607392 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 8275868188719755872579531297) ^ 104905223652470634341664 ≠ 1
      rw [← septFastPow_eq_pow]
      decide
    · change (7 : ZMod 8275868188719755872579531297) ^ 76976248470432 ≠ 1
      rw [← septFastPow_eq_pow]
      decide

private theorem phi_septE_8275868188719755872579531200 : Nat.totient 8275868188719755872579531200 = 1088999579215524475699200000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_5, prime_septE_7, prime_septE_11, prime_septE_13, prime_septE_17, prime_septE_19, prime_septE_23, prime_septE_29, prime_septE_31, prime_septE_37, prime_septE_41, prime_septE_43, prime_septE_47, prime_septE_53, prime_septE_59, prime_septE_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531201 : Nat.totient 8275868188719755872579531201 = 8275803273330824297157026692 := by
  rw [← show ((([(127487, 1), (64915388931575422377023, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_127487, prime_septE_64915388931575422377023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531202 : Nat.totient 8275868188719755872579531202 = 4137922714247355598191994900 := by
  rw [← show ((([(2, 1), (363611, 1), (11380112522338097407091, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_363611, prime_septE_11380112522338097407091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531203 : Nat.totient 8275868188719755872579531203 = 5476973594481200966767961984 := by
  rw [← show ((([(3, 1), (137, 1), (20135932332651474142529273, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_137, prime_septE_20135932332651474142529273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531204 : Nat.totient 8275868188719755872579531204 = 4135999322234591016432996384 := by
  rw [← show ((([(2, 2), (3023, 1), (7309, 1), (93639150386551147643, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3023, prime_septE_7309, prime_septE_93639150386551147643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531205 : Nat.totient 8275868188719755872579531205 = 6546304724560346218310100736 := by
  rw [← show ((([(5, 1), (89, 1), (18597456603864619938380969, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_5, prime_septE_89, prime_septE_18597456603864619938380969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531206 : Nat.totient 8275868188719755872579531206 = 2748037915854517917770979840 := by
  rw [← show ((([(2, 1), (3, 1), (263, 1), (33811, 1), (189853, 1), (817016986973969, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_263, prime_septE_33811, prime_septE_189853, prime_septE_817016986973969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531207 : Nat.totient 8275868188719755872579531207 = 7023328967119773837005857152 := by
  rw [← show ((([(7, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_7, prime_septE_103, prime_septE_5009, prime_septE_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531208 : Nat.totient 8275868188719755872579531208 = 4116494021332106548018833408 := by
  rw [← show ((([(2, 3), (193, 1), (5360018256942847067732857, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_193, prime_septE_5360018256942847067732857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531209 : Nat.totient 8275868188719755872579531209 = 5517245459146503915053020800 := by
  rw [← show ((([(3, 2), (919540909857750652508836801, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_919540909857750652508836801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531210 : Nat.totient 8275868188719755872579531210 = 3276158310075371853873715200 := by
  rw [← show ((([(2, 1), (5, 1), (97, 1), (72973, 1), (195271, 1), (598744972004371, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_5, prime_septE_97, prime_septE_72973, prime_septE_195271, prime_septE_598744972004371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531211 : Nat.totient 8275868188719755872579531211 = 7523516535199778065981392000 := by
  rw [← show ((([(11, 1), (752351653519977806598139201, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_11, prime_septE_752351653519977806598139201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531212 : Nat.totient 8275868188719755872579531212 = 2725815331812937093673881600 := by
  rw [← show ((([(2, 2), (3, 1), (131, 1), (233, 1), (550990241, 1), (41007301887107, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_131, prime_septE_233, prime_septE_550990241, prime_septE_41007301887107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531213 : Nat.totient 8275868188719755872579531213 = 7638527762705737673822738640 := by
  rw [← show ((([(13, 2), (10391, 1), (4712696973609818164547, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_13, prime_septE_10391, prime_septE_4712696973609818164547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531214 : Nat.totient 8275868188719755872579531214 = 3546800649407473472293236600 := by
  rw [← show ((([(2, 1), (7, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_7, prime_septE_1222615931, prime_septE_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531215 : Nat.totient 8275868188719755872579531215 = 4413796367140036680980727456 := by
  rw [← show ((([(3, 1), (5, 1), (24913302187, 1), (22145781469408963, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_5, prime_septE_24913302187, prime_septE_22145781469408963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531216 : Nat.totient 8275868188719755872579531216 = 4084899288641224253891518464 := by
  rw [← show ((([(2, 4), (79, 1), (6229, 1), (8696692033, 1), (120863194567, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_79, prime_septE_6229, prime_septE_8696692033, prime_septE_120863194567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531217 : Nat.totient 8275868188719755872579531217 = 7789046627529442253386001152 := by
  rw [← show ((([(17, 1), (1346333, 1), (361586454322254942197, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_17, prime_septE_1346333, prime_septE_361586454322254942197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531218 : Nat.totient 8275868188719755872579531218 = 2751432942019474114721130240 := by
  rw [← show ((([(2, 1), (3, 2), (521, 1), (1453, 1), (607348163015529886877, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_521, prime_septE_1453, prime_septE_607348163015529886877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531219 : Nat.totient 8275868188719755872579531219 = 7840296176731207853368336200 := by
  rw [← show ((([(19, 1), (3813504911, 1), (114218290024018991, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_19, prime_septE_3813504911, prime_septE_114218290024018991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531220 : Nat.totient 8275868188719755872579531220 = 3304999380003966497127265536 := by
  rw [← show ((([(2, 2), (5, 1), (619, 1), (70908014633, 1), (9427522870043, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_5, prime_septE_619, prime_septE_70908014633, prime_septE_9427522870043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531221 : Nat.totient 8275868188719755872579531221 = 4729067536411289070045446400 := by
  rw [← show ((([(3, 1), (7, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_7, prime_septE_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531222 : Nat.totient 8275868188719755872579531222 = 3761758267599889032990696000 := by
  rw [← show ((([(2, 1), (11, 1), (376175826759988903299069601, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_11, prime_septE_376175826759988903299069601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531223 : Nat.totient 8275868188719755872579531223 = 7912878563756018218325799840 := by
  rw [← show ((([(23, 1), (2939, 1), (16631, 1), (7361524796742341989, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_23, prime_septE_2939, prime_septE_16631, prime_septE_7361524796742341989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531224 : Nat.totient 8275868188719755872579531224 = 2758622729573251957526510400 := by
  rw [← show ((([(2, 3), (3, 1), (344827841196656494690813801, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_344827841196656494690813801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531225 : Nat.totient 8275868188719755872579531225 = 6620694550975804698063624960 := by
  rw [← show ((([(5, 2), (331034727548790234903181249, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_5, prime_septE_331034727548790234903181249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531226 : Nat.totient 8275868188719755872579531226 = 3819625279816644655002765504 := by
  rw [← show ((([(2, 1), (13, 1), (620159, 1), (116512763, 1), (4405180062253, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_13, prime_septE_620159, prime_septE_116512763, prime_septE_4405180062253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531227 : Nat.totient 8275868188719755872579531227 = 5499798181795815391554280704 := by
  rw [← show ((([(3, 3), (317, 1), (128749, 1), (7510116500595532297, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_317, prime_septE_128749, prime_septE_7510116500595532297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531228 : Nat.totient 8275868188719755872579531228 = 3546800482854297447975573504 := by
  rw [← show ((([(2, 2), (7, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_7, prime_septE_20930737, prime_septE_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531229 : Nat.totient 8275868188719755872579531229 = 7990493423591488428697478400 := by
  rw [← show ((([(29, 1), (285374765128267443882052801, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_29, prime_septE_285374765128267443882052801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531230 : Nat.totient 8275868188719755872579531230 = 2204732434705060249469658272 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1019, 1), (270718619192664568942739, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_5, prime_septE_1019, prime_septE_270718619192664568942739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531231 : Nat.totient 8275868188719755872579531231 = 7973915489449094086047129600 := by
  rw [← show ((([(31, 1), (257, 1), (2099, 1), (319919, 1), (20354891, 1), (75997183, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_31, prime_septE_257, prime_septE_2099, prime_septE_319919, prime_septE_20354891, prime_septE_75997183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531232 : Nat.totient 8275868188719755872579531232 = 4137080465009220782176711680 := by
  rw [← show ((([(2, 5), (5821, 1), (28979, 1), (1533142745943043289, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_5821, prime_septE_28979, prime_septE_1533142745943043289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531233 : Nat.totient 8275868188719755872579531233 = 5015677375858470062137237440 := by
  rw [← show ((([(3, 1), (11, 1), (15959533, 1), (15713735765743224997, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_11, prime_septE_15959533, prime_septE_15713735765743224997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531234 : Nat.totient 8275868188719755872579531234 = 3876557906441476509047193600 := by
  rw [← show ((([(2, 1), (17, 1), (241, 1), (2153, 1), (548897, 1), (854639021934121, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_17, prime_septE_241, prime_septE_2153, prime_septE_548897, prime_septE_854639021934121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531235 : Nat.totient 8275868188719755872579531235 = 5674881034629409990943511648 := by
  rw [← show ((([(5, 1), (7, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_5, prime_septE_7, prime_septE_626080687, prime_septE_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531236 : Nat.totient 8275868188719755872579531236 = 2758612631644984604933403504 := by
  rw [← show ((([(2, 2), (3, 2), (273187, 1), (841494022279382485723, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_273187, prime_septE_841494022279382485723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531237 : Nat.totient 8275868188719755872579531237 = 8052163749580099852848112128 := by
  rw [← show ((([(37, 1), (307817, 1), (1305709, 1), (556509832673117, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_37, prime_septE_307817, prime_septE_1305709, prime_septE_556509832673117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531238 : Nat.totient 8275868188719755872579531238 = 3920148086908808479439558016 := by
  rw [← show ((([(2, 1), (19, 1), (1577676713, 1), (138042225743563577, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_19, prime_septE_1577676713, prime_septE_138042225743563577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531239 : Nat.totient 8275868188719755872579531239 = 5092841962289080536972019200 := by
  rw [← show ((([(3, 1), (13, 1), (212201748428711689040500801, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_13, prime_septE_212201748428711689040500801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531240 : Nat.totient 8275868188719755872579531240 = 3305980452539223796158793728 := by
  rw [← show ((([(2, 3), (5, 1), (1117, 1), (2357, 1), (78585209989176375449, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_5, prime_septE_1117, prime_septE_2357, prime_septE_78585209989176375449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531241 : Nat.totient 8275868188719755872579531241 = 8074017745092444753736128000 := by
  rw [← show ((([(41, 1), (201850443627311118843403201, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_41, prime_septE_201850443627311118843403201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531242 : Nat.totient 8275868188719755872579531242 = 2358700242841490567164661376 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_7, prime_septE_409, prime_septE_45127, prime_septE_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531243 : Nat.totient 8275868188719755872579531243 = 8079655789860152849537709600 := by
  rw [← show ((([(43, 1), (2179, 1), (222163, 1), (1881863, 1), (211265287151, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_43, prime_septE_2179, prime_septE_222163, prime_septE_1881863, prime_septE_211265287151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531244 : Nat.totient 8275868188719755872579531244 = 3753873543579702534099763200 := by
  rw [← show ((([(2, 2), (11, 1), (479, 1), (242633, 1), (302287, 1), (1588921, 1), (3369409, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_11, prime_septE_479, prime_septE_242633, prime_septE_302287, prime_septE_1588921, prime_septE_3369409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531245 : Nat.totient 8275868188719755872579531245 = 4409644159858699940223696768 := by
  rw [← show ((([(3, 2), (5, 1), (1063, 1), (29245518173, 1), (5915731660739, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_5, prime_septE_1063, prime_septE_29245518173, prime_septE_5915731660739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531246 : Nat.totient 8275868188719755872579531246 = 3958023916344231069494558400 := by
  rw [← show ((([(2, 1), (23, 1), (179910178015646866795207201, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_23, prime_septE_179910178015646866795207201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531247 : Nat.totient 8275868188719755872579531247 = 8088840924414746013421532928 := by
  rw [← show ((([(47, 1), (937, 1), (3517, 1), (53432285109967285069, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_47, prime_septE_937, prime_septE_3517, prime_septE_53432285109967285069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531248 : Nat.totient 8275868188719755872579531248 = 2720833377100151693639081472 := by
  rw [← show ((([(2, 4), (3, 1), (73, 1), (210091982543, 1), (11241906997859, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_73, prime_septE_210091982543, prime_septE_11241906997859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531249 : Nat.totient 8275868188719755872579531249 = 7078213882607007945748436640 := by
  rw [← show ((([(7, 2), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_7, prime_septE_461, prime_septE_13492702567, prime_septE_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531250 : Nat.totient 8275868188719755872579531250 = 3309398935305685213600000000 := by
  rw [← show ((([(2, 1), (5, 7), (4481, 1), (15791, 1), (748529570095379, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_5, prime_septE_4481, prime_septE_15791, prime_septE_748529570095379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531251 : Nat.totient 8275868188719755872579531251 = 5191282449661382511926555136 := by
  rw [← show ((([(3, 1), (17, 1), (3659, 1), (19573967087, 1), (2265698544397, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_17, prime_septE_3659, prime_septE_19573967087, prime_septE_2265698544397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531252 : Nat.totient 8275868188719755872579531252 = 3819627513238261161135853440 := by
  rw [← show ((([(2, 2), (13, 1), (1328143, 1), (3528331, 1), (33962219399197, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_13, prime_septE_1328143, prime_septE_3528331, prime_septE_33962219399197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531253 : Nat.totient 8275868188719755872579531253 = 8111780420119480424769993024 := by
  rw [← show ((([(53, 1), (1069, 1), (23603, 1), (6188605283481895943, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_53, prime_septE_1069, prime_septE_23603, prime_septE_6188605283481895943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531254 : Nat.totient 8275868188719755872579531254 = 2758622729573251957526509932 := by
  rw [← show ((([(2, 1), (3, 6), (5676178455912041064869363, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_5676178455912041064869363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531255 : Nat.totient 8275868188719755872579531255 = 5932222302694132615746670080 := by
  rw [← show ((([(5, 1), (11, 1), (113, 1), (179, 1), (7439082943787786687083, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_5, prime_septE_11, prime_septE_113, prime_septE_179, prime_septE_7439082943787786687083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531256 : Nat.totient 8275868188719755872579531256 = 3528231002875955915514904320 := by
  rw [← show ((([(2, 3), (7, 1), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_7, prime_septE_191, prime_septE_282045737, prime_septE_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531257 : Nat.totient 8275868188719755872579531257 = 5222749743415767491099555328 := by
  rw [← show ((([(3, 1), (19, 1), (1279, 1), (224429, 1), (1180537, 1), (428459313203, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_19, prime_septE_1279, prime_septE_224429, prime_septE_1180537, prime_septE_428459313203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531258 : Nat.totient 8275868188719755872579531258 = 3938308032865232394981733120 := by
  rw [← show ((([(2, 1), (29, 1), (71, 1), (6029, 1), (276173, 1), (1206981799340543, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_29, prime_septE_71, prime_septE_6029, prime_septE_276173, prime_septE_1206981799340543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531259 : Nat.totient 8275868188719755872579531259 = 8135508621162451673137812000 := by
  rw [← show ((([(59, 1), (108287, 1), (525373, 1), (2465570819598251, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_59, prime_septE_108287, prime_septE_525373, prime_septE_2465570819598251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531260 : Nat.totient 8275868188719755872579531260 = 2196011284206166524767093760 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (211, 1), (5387, 1), (148157, 1), (429467, 1), (1907132687, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_5, prime_septE_211, prime_septE_5387, prime_septE_148157, prime_septE_429467, prime_septE_1907132687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531261 : Nat.totient 8275868188719755872579531261 = 8042122873461347002323129600 := by
  rw [← show ((([(61, 1), (83, 1), (12045937, 1), (135695376416512331, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_61, prime_septE_83, prime_septE_12045937, prime_septE_135695376416512331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531262 : Nat.totient 8275868188719755872579531262 = 4004246115031792393977528960 := by
  rw [← show ((([(2, 1), (31, 1), (19417, 1), (6874478291154704700553, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_31, prime_septE_19417, prime_septE_6874478291154704700553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531263 : Nat.totient 8275868188719755872579531263 = 4729067536411289070045446400 := by
  rw [← show ((([(3, 2), (7, 1), (131362987122535807501262401, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_7, prime_septE_131362987122535807501262401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531264 : Nat.totient 8275868188719755872579531264 = 4133890571369569445074432000 := by
  rw [← show ((([(2, 9), (1493, 1), (3251, 1), (3330173240753223479, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_1493, prime_septE_3251, prime_septE_3330173240753223479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531265 : Nat.totient 8275868188719755872579531265 = 5998913873287908552351212544 := by
  rw [← show ((([(5, 1), (13, 1), (67, 1), (283, 1), (695389, 1), (9656308976012389, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_5, prime_septE_13, prime_septE_67, prime_septE_283, prime_septE_695389, prime_septE_9656308976012389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531266 : Nat.totient 8275868188719755872579531266 = 2504846930671548157621631040 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (839, 1), (884003, 1), (169065085989715453, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_11, prime_septE_839, prime_septE_884003, prime_septE_169065085989715453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531267 : Nat.totient 8275868188719755872579531267 = 8272815452438178868938254400 := by
  rw [← show ((([(2711, 1), (224566541, 1), (13593741208926217, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2711, prime_septE_224566541, prime_septE_13593741208926217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531268 : Nat.totient 8275868188719755872579531268 = 3894294349373655896632465920 := by
  rw [← show ((([(2, 2), (17, 1), (34871, 1), (34939, 1), (447107, 1), (223418077447, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_17, prime_septE_34871, prime_septE_34939, prime_septE_447107, prime_septE_223418077447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531269 : Nat.totient 8275868188719755872579531269 = 5277284383779750087490863360 := by
  rw [← show ((([(3, 1), (23, 1), (65777, 1), (8696203, 1), (209681803341971, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_23, prime_septE_65777, prime_septE_8696203, prime_septE_209681803341971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531270 : Nat.totient 8275868188719755872579531270 = 2809347051333439051512144000 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (101, 1), (1170561271388932938130061, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_5, prime_septE_7, prime_septE_101, prime_septE_1170561271388932938130061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531271 : Nat.totient 8275868188719755872579531271 = 8275865293973514111329927472 := by
  rw [← show ((([(2858927, 1), (2894746241761246744873, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2858927, prime_septE_2894746241761246744873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531272 : Nat.totient 8275868188719755872579531272 = 2757861310106077446911594208 := by
  rw [← show ((([(2, 3), (3, 2), (3623, 1), (31725811132271275617887, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_3623, prime_septE_31725811132271275617887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531273 : Nat.totient 8275868188719755872579531273 = 8275868127524196478706764288 := by
  rw [← show ((([(135236417, 1), (61195559393737530569, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_135236417, prime_septE_61195559393737530569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531274 : Nat.totient 8275868188719755872579531274 = 4026098037342815287201465344 := by
  rw [← show ((([(2, 1), (37, 1), (9754532209, 1), (11465035350555889, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_37, prime_septE_9754532209, prime_septE_11465035350555889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531275 : Nat.totient 8275868188719755872579531275 = 4410669622438307843813151360 := by
  rw [← show ((([(3, 1), (5, 2), (1549, 1), (15907, 1), (4478294011594510519, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_5, prime_septE_1549, prime_septE_15907, prime_septE_4478294011594510519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531276 : Nat.totient 8275868188719755872579531276 = 3898489812656587529391921600 := by
  rw [← show ((([(2, 2), (19, 1), (181, 1), (601618798249473384165421, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_19, prime_septE_181, prime_septE_601618798249473384165421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531277 : Nat.totient 8275868188719755872579531277 = 6448728458742666913698336000 := by
  rw [← show ((([(7, 1), (11, 1), (107478807645711115228305601, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_7, prime_septE_11, prime_septE_107478807645711115228305601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531278 : Nat.totient 8275868188719755872579531278 = 2546404908197155985678752896 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (158429, 1), (669706141011783477269, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_13, prime_septE_158429, prime_septE_669706141011783477269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531279 : Nat.totient 8275868188719755872579531279 = 8275866361073720472354588376 := by
  rw [← show ((([(4528157, 1), (1827646035400220414747, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_4528157, prime_septE_1827646035400220414747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531280 : Nat.totient 8275868188719755872579531280 = 3310347275487902349031812480 := by
  rw [← show ((([(2, 4), (5, 1), (103448352358996948407244141, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_5, prime_septE_103448352358996948407244141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531281 : Nat.totient 8275868188719755872579531281 = 5517210713817995709270773040 := by
  rw [← show ((([(3, 3), (158791, 1), (1930296028233654410533, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_158791, prime_septE_1930296028233654410533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531282 : Nat.totient 8275868188719755872579531282 = 4037003054096903385817484160 := by
  rw [← show ((([(2, 1), (41, 1), (693829, 1), (145461232974775570669, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_41, prime_septE_693829, prime_septE_145461232974775570669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531283 : Nat.totient 8275868188719755872579531283 = 8215498442931153675566961600 := by
  rw [← show ((([(163, 1), (857, 1), (2418084863, 1), (24500423998151, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_163, prime_septE_857, prime_septE_2418084863, prime_septE_24500423998151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531284 : Nat.totient 8275868188719755872579531284 = 2356928652743370057502356480 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (311, 1), (1115447, 1), (284004322561366753, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_7, prime_septE_311, prime_septE_1115447, prime_septE_284004322561366753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531285 : Nat.totient 8275868188719755872579531285 = 6174977707791382909105935360 := by
  rw [← show ((([(5, 1), (17, 2), (139, 1), (541, 1), (76161177957942879887, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_5, prime_septE_17, prime_septE_139, prime_septE_541, prime_septE_76161177957942879887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531286 : Nat.totient 8275868188719755872579531286 = 4041703068781461746999570304 := by
  rw [← show ((([(2, 1), (43, 1), (31530198377, 1), (3052027275553913, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_43, prime_septE_31530198377, prime_septE_3052027275553913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531287 : Nat.totient 8275868188719755872579531287 = 5326817906281692093831462912 := by
  rw [← show ((([(3, 1), (29, 1), (33223, 1), (306689, 1), (9335923120121783, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_29, prime_septE_33223, prime_septE_306689, prime_septE_9335923120121783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531288 : Nat.totient 8275868188719755872579531288 = 3759857429667802176480768160 := by
  rw [← show ((([(2, 3), (11, 1), (1979, 1), (47520948302171412746219, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_11, prime_septE_1979, prime_septE_47520948302171412746219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531289 : Nat.totient 8275868188719755872579531289 = 8198433970824657710162113920 := by
  rw [← show ((([(107, 1), (102121, 1), (874693, 1), (865882729346359, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_107, prime_septE_102121, prime_septE_874693, prime_septE_865882729346359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531290 : Nat.totient 8275868188719755872579531290 = 2206698522899190536281253760 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (12263, 1), (112199, 1), (84545803, 1), (790484371, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_5, prime_septE_12263, prime_septE_112199, prime_septE_84545803, prime_septE_790484371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531291 : Nat.totient 8275868188719755872579531291 = 6547934702581563518941993344 := by
  rw [← show ((([(7, 1), (13, 1), (1319293, 1), (68933592817856129557, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_7, prime_septE_13, prime_septE_1319293, prime_septE_68933592817856129557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531292 : Nat.totient 8275868188719755872579531292 = 3940274930172283844967667248 := by
  rw [← show ((([(2, 2), (23, 1), (223, 1), (403386049362436921065487, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_23, prime_septE_223, prime_septE_403386049362436921065487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531293 : Nat.totient 8275868188719755872579531293 = 5315745153755069208802399680 := by
  rw [← show ((([(3, 1), (31, 1), (227, 1), (1463149, 1), (267926829178745687, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_3, prime_septE_31, prime_septE_227, prime_septE_1463149, prime_septE_267926829178745687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531294 : Nat.totient 8275868188719755872579531294 = 3984265972902787431596573760 := by
  rw [← show ((([(2, 1), (47, 1), (89, 1), (199, 1), (4970987010548652822191, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_47, prime_septE_89, prime_septE_199, prime_septE_4970987010548652822191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531295 : Nat.totient 8275868188719755872579531295 = 6192819634869459754401148416 := by
  rw [← show ((([(5, 1), (19, 1), (79, 1), (283133, 1), (200110847, 1), (19462639909, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531295 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_5, prime_septE_19, prime_septE_79, prime_septE_283133, prime_septE_200110847, prime_septE_19462639909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531296 : Nat.totient 8275868188719755872579531296 = 2756323429753962067711672320 := by
  rw [← show ((([(2, 5), (3, 1), (1481, 1), (6863, 1), (78889, 1), (107511970941253, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531296 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_2, prime_septE_3, prime_septE_1481, prime_septE_6863, prime_septE_78889, prime_septE_107511970941253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_septE_8275868188719755872579531297 : Nat.totient 8275868188719755872579531297 = 8275868188719755872579531296 := by
  rw [← show ((([(8275868188719755872579531297, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755872579531297 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_septE_8275868188719755872579531297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeptE : certifiedKill 1 8275868188719755872579531199 97 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_septE_8275868188719755872579531200, phi_septE_8275868188719755872579531201, phi_septE_8275868188719755872579531202,
    phi_septE_8275868188719755872579531203, phi_septE_8275868188719755872579531204, phi_septE_8275868188719755872579531205,
    phi_septE_8275868188719755872579531206, phi_septE_8275868188719755872579531207, phi_septE_8275868188719755872579531208,
    phi_septE_8275868188719755872579531209, phi_septE_8275868188719755872579531210, phi_septE_8275868188719755872579531211,
    phi_septE_8275868188719755872579531212, phi_septE_8275868188719755872579531213, phi_septE_8275868188719755872579531214,
    phi_septE_8275868188719755872579531215, phi_septE_8275868188719755872579531216, phi_septE_8275868188719755872579531217,
    phi_septE_8275868188719755872579531218, phi_septE_8275868188719755872579531219, phi_septE_8275868188719755872579531220,
    phi_septE_8275868188719755872579531221, phi_septE_8275868188719755872579531222, phi_septE_8275868188719755872579531223,
    phi_septE_8275868188719755872579531224, phi_septE_8275868188719755872579531225, phi_septE_8275868188719755872579531226,
    phi_septE_8275868188719755872579531227, phi_septE_8275868188719755872579531228, phi_septE_8275868188719755872579531229,
    phi_septE_8275868188719755872579531230, phi_septE_8275868188719755872579531231, phi_septE_8275868188719755872579531232,
    phi_septE_8275868188719755872579531233, phi_septE_8275868188719755872579531234, phi_septE_8275868188719755872579531235,
    phi_septE_8275868188719755872579531236, phi_septE_8275868188719755872579531237, phi_septE_8275868188719755872579531238,
    phi_septE_8275868188719755872579531239, phi_septE_8275868188719755872579531240, phi_septE_8275868188719755872579531241,
    phi_septE_8275868188719755872579531242, phi_septE_8275868188719755872579531243, phi_septE_8275868188719755872579531244,
    phi_septE_8275868188719755872579531245, phi_septE_8275868188719755872579531246, phi_septE_8275868188719755872579531247,
    phi_septE_8275868188719755872579531248, phi_septE_8275868188719755872579531249, phi_septE_8275868188719755872579531250,
    phi_septE_8275868188719755872579531251, phi_septE_8275868188719755872579531252, phi_septE_8275868188719755872579531253,
    phi_septE_8275868188719755872579531254, phi_septE_8275868188719755872579531255, phi_septE_8275868188719755872579531256,
    phi_septE_8275868188719755872579531257, phi_septE_8275868188719755872579531258, phi_septE_8275868188719755872579531259,
    phi_septE_8275868188719755872579531260, phi_septE_8275868188719755872579531261, phi_septE_8275868188719755872579531262,
    phi_septE_8275868188719755872579531263, phi_septE_8275868188719755872579531264, phi_septE_8275868188719755872579531265,
    phi_septE_8275868188719755872579531266, phi_septE_8275868188719755872579531267, phi_septE_8275868188719755872579531268,
    phi_septE_8275868188719755872579531269, phi_septE_8275868188719755872579531270, phi_septE_8275868188719755872579531271,
    phi_septE_8275868188719755872579531272, phi_septE_8275868188719755872579531273, phi_septE_8275868188719755872579531274,
    phi_septE_8275868188719755872579531275, phi_septE_8275868188719755872579531276, phi_septE_8275868188719755872579531277,
    phi_septE_8275868188719755872579531278, phi_septE_8275868188719755872579531279, phi_septE_8275868188719755872579531280,
    phi_septE_8275868188719755872579531281, phi_septE_8275868188719755872579531282, phi_septE_8275868188719755872579531283,
    phi_septE_8275868188719755872579531284, phi_septE_8275868188719755872579531285, phi_septE_8275868188719755872579531286,
    phi_septE_8275868188719755872579531287, phi_septE_8275868188719755872579531288, phi_septE_8275868188719755872579531289,
    phi_septE_8275868188719755872579531290, phi_septE_8275868188719755872579531291, phi_septE_8275868188719755872579531292,
    phi_septE_8275868188719755872579531293, phi_septE_8275868188719755872579531294, phi_septE_8275868188719755872579531295,
    phi_septE_8275868188719755872579531296, phi_septE_8275868188719755872579531297]

end TotientTailPeriodKiller
end Erdos249257
