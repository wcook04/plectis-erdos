import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def thirtyThreeAEFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem thirtyThreeAEFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    thirtyThreeAEFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [thirtyThreeAEFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [thirtyThreeAEFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then thirtyThreeAEFastPow a n * thirtyThreeAEFastPow a n * a
        else thirtyThreeAEFastPow a n * thirtyThreeAEFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_thirtyThreeAE_2 : Nat.Prime 2 := by norm_num
private theorem prime_thirtyThreeAE_3 : Nat.Prime 3 := by norm_num
private theorem prime_thirtyThreeAE_5 : Nat.Prime 5 := by norm_num
private theorem prime_thirtyThreeAE_7 : Nat.Prime 7 := by norm_num
private theorem prime_thirtyThreeAE_11 : Nat.Prime 11 := by norm_num
private theorem prime_thirtyThreeAE_13 : Nat.Prime 13 := by norm_num
private theorem prime_thirtyThreeAE_17 : Nat.Prime 17 := by norm_num
private theorem prime_thirtyThreeAE_19 : Nat.Prime 19 := by norm_num
private theorem prime_thirtyThreeAE_23 : Nat.Prime 23 := by norm_num
private theorem prime_thirtyThreeAE_29 : Nat.Prime 29 := by norm_num
private theorem prime_thirtyThreeAE_31 : Nat.Prime 31 := by norm_num
private theorem prime_thirtyThreeAE_37 : Nat.Prime 37 := by norm_num
private theorem prime_thirtyThreeAE_41 : Nat.Prime 41 := by norm_num
private theorem prime_thirtyThreeAE_43 : Nat.Prime 43 := by norm_num
private theorem prime_thirtyThreeAE_47 : Nat.Prime 47 := by norm_num
private theorem prime_thirtyThreeAE_53 : Nat.Prime 53 := by norm_num
private theorem prime_thirtyThreeAE_59 : Nat.Prime 59 := by norm_num
private theorem prime_thirtyThreeAE_61 : Nat.Prime 61 := by norm_num
private theorem prime_thirtyThreeAE_113 : Nat.Prime 113 := by norm_num
private theorem prime_thirtyThreeAE_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_thirtyThreeAE_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_thirtyThreeAE_179 : Nat.Prime 179 := by norm_num
private theorem prime_thirtyThreeAE_271 : Nat.Prime 271 := by norm_num
private theorem prime_thirtyThreeAE_367 : Nat.Prime 367 := by norm_num
private theorem prime_thirtyThreeAE_439 : Nat.Prime 439 := by norm_num
private theorem prime_thirtyThreeAE_175303 : Nat.Prime 175303 := by norm_num
private theorem prime_thirtyThreeAE_2740136831843303 : Nat.Prime 2740136831843303 := by
  apply lucas_primality 2740136831843303 (5 : ZMod 2740136831843303)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (179, 1), (271, 1), (367, 1), (439, 1), (175303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (179, 1), (271, 1), (367, 1), (439, 1), (175303, 1)] : List FactorBlock).map factorBlockValue).prod = 2740136831843303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_179
      · exact prime_thirtyThreeAE_271
      · exact prime_thirtyThreeAE_367
      · exact prime_thirtyThreeAE_439
      · exact prime_thirtyThreeAE_175303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2740136831843303) ^ 1370068415921651 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2740136831843303) ^ 15308026993538 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2740136831843303) ^ 10111206021562 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2740136831843303) ^ 7466312893306 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2740136831843303) ^ 6241769548618 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2740136831843303) ^ 15630861034 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_580909008350780237 : Nat.Prime 580909008350780237 := by
  apply lucas_primality 580909008350780237 (2 : ZMod 580909008350780237)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (53, 1), (2740136831843303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (53, 1), (2740136831843303, 1)] : List FactorBlock).map factorBlockValue).prod = 580909008350780237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_2740136831843303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 580909008350780237) ^ 290454504175390118 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 580909008350780237) ^ 10960547327373212 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 580909008350780237) ^ 212 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_55813737522342965170961 : Nat.Prime 55813737522342965170961 := by
  apply lucas_primality 55813737522342965170961 (3 : ZMod 55813737522342965170961)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (1201, 1), (580909008350780237, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (1201, 1), (580909008350780237, 1)] : List FactorBlock).map factorBlockValue).prod = 55813737522342965170961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_1201
      · exact prime_thirtyThreeAE_580909008350780237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 55813737522342965170961) ^ 27906868761171482585480 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55813737522342965170961) ^ 11162747504468593034192 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55813737522342965170961) ^ 46472720668062418960 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55813737522342965170961) ^ 96080 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_334882425134057791025767 : Nat.Prime 334882425134057791025767 := by
  apply lucas_primality 334882425134057791025767 (3 : ZMod 334882425134057791025767)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (55813737522342965170961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (55813737522342965170961, 1)] : List FactorBlock).map factorBlockValue).prod = 334882425134057791025767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_55813737522342965170961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 334882425134057791025767) ^ 167441212567028895512883 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 334882425134057791025767) ^ 111627475044685930341922 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 334882425134057791025767) ^ 6 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_19507403587696567413937466401 : Nat.Prime 19507403587696567413937466401 := by
  apply lucas_primality 19507403587696567413937466401 (146 : ZMod 19507403587696567413937466401)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 19507403587696567413937466401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_59
      · exact prime_thirtyThreeAE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (146 : ZMod 19507403587696567413937466401) ^ 9753701793848283706968733200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 6502467862565522471312488800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 3901480717539313482787493280 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 2786771941099509630562495200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 1773400326154233401267042400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 1500569506745889801072112800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 1147494328688033377290439200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 1026705451984029863891445600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 848147982073763800605976800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 672669089230916117721981600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 629271083474082819804434400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 527227123991799119295607200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 475790331407233351559450400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 453660548551082963114824800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 415051140163756753488031200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 368064218635784290829008800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 330633959113501142609109600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (146 : ZMod 19507403587696567413937466401) ^ 319793501437648646130122400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_83 : Nat.Prime 83 := by norm_num
private theorem prime_thirtyThreeAE_895529 : Nat.Prime 895529 := by norm_num
private theorem prime_thirtyThreeAE_401 : Nat.Prime 401 := by norm_num
private theorem prime_thirtyThreeAE_514793 : Nat.Prime 514793 := by norm_num
private theorem prime_thirtyThreeAE_2064319931 : Nat.Prime 2064319931 := by
  apply lucas_primality 2064319931 (2 : ZMod 2064319931)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (401, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (401, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod = 2064319931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_401
      · exact prime_thirtyThreeAE_514793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2064319931) ^ 1032159965 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 412863986 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 5147930 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2064319931) ^ 4010 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_8917991 : Nat.Prime 8917991 := by norm_num
private theorem prime_thirtyThreeAE_963143029 : Nat.Prime 963143029 := by
  apply lucas_primality 963143029 (2 : ZMod 963143029)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (8917991, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (8917991, 1)] : List FactorBlock).map factorBlockValue).prod = 963143029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_8917991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 963143029) ^ 481571514 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 963143029) ^ 321047676 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 963143029) ^ 108 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_84756586553 : Nat.Prime 84756586553 := by
  apply lucas_primality 84756586553 (3 : ZMod 84756586553)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (963143029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (963143029, 1)] : List FactorBlock).map factorBlockValue).prod = 84756586553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_963143029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 84756586553) ^ 42378293276 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 84756586553) ^ 7705144232 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 84756586553) ^ 88 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_7687 : Nat.Prime 7687 := by norm_num
private theorem prime_thirtyThreeAE_35803 : Nat.Prime 35803 := by norm_num
private theorem prime_thirtyThreeAE_106033 : Nat.Prime 106033 := by norm_num
private theorem prime_thirtyThreeAE_581873 : Nat.Prime 581873 := by norm_num
private theorem prime_thirtyThreeAE_5099 : Nat.Prime 5099 := by norm_num
private theorem prime_thirtyThreeAE_28163 : Nat.Prime 28163 := by norm_num
private theorem prime_thirtyThreeAE_574412549 : Nat.Prime 574412549 := by
  apply lucas_primality 574412549 (2 : ZMod 574412549)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5099, 1), (28163, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5099, 1), (28163, 1)] : List FactorBlock).map factorBlockValue).prod = 574412549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5099
      · exact prime_thirtyThreeAE_28163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 574412549) ^ 287206274 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 574412549) ^ 112652 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 574412549) ^ 20396 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_7802961435078626965574986561 : Nat.Prime 7802961435078626965574986561 := by
  apply lucas_primality 7802961435078626965574986561 (113 : ZMod 7802961435078626965574986561)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 1), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 1), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 7802961435078626965574986561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_59
      · exact prime_thirtyThreeAE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 7802961435078626965574986561) ^ 3901480717539313482787493280 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 2600987145026208988524995520 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 1560592287015725393114997312 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 1114708776439803852224998080 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 709360130461693360506816960 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 600227802698355920428845120 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 458997731475213350916175680 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 410682180793611945556578240 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 339259192829505520242390720 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 269067635692366447088792640 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 251708433389633127921773760 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 210890849596719647718242880 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 190316132562893340623780160 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 181464219420433185245929920 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 166020456065502701395212480 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 147225687454313716331603520 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 132253583645400457043643840 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (113 : ZMod 7802961435078626965574986561) ^ 127917400575059458452048960 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_11218483 : Nat.Prime 11218483 := by norm_num
private theorem prime_thirtyThreeAE_9257 : Nat.Prime 9257 := by norm_num
private theorem prime_thirtyThreeAE_22511 : Nat.Prime 22511 := by norm_num
private theorem prime_thirtyThreeAE_15837208853 : Nat.Prime 15837208853 := by
  apply lucas_primality 15837208853 (2 : ZMod 15837208853)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (9257, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (9257, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod = 15837208853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_9257
      · exact prime_thirtyThreeAE_22511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15837208853) ^ 7918604426 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 833537308 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 1710836 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 15837208853) ^ 703532 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_19804481 : Nat.Prime 19804481 := by norm_num
private theorem prime_thirtyThreeAE_118826887 : Nat.Prime 118826887 := by
  apply lucas_primality 118826887 (6 : ZMod 118826887)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19804481, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19804481, 1)] : List FactorBlock).map factorBlockValue).prod = 118826887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_19804481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 118826887) ^ 59413443 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 118826887) ^ 39608962 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 118826887) ^ 6 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_18299340599 : Nat.Prime 18299340599 := by
  apply lucas_primality 18299340599 (7 : ZMod 18299340599)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (11, 1), (118826887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (11, 1), (118826887, 1)] : List FactorBlock).map factorBlockValue).prod = 18299340599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_118826887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 18299340599) ^ 9149670299 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 2614191514 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 1663576418 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 18299340599) ^ 154 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_36598681199 : Nat.Prime 36598681199 := by
  apply lucas_primality 36598681199 (11 : ZMod 36598681199)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (18299340599, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (18299340599, 1)] : List FactorBlock).map factorBlockValue).prod = 36598681199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_18299340599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 36598681199) ^ 18299340599 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 36598681199) ^ 2 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_thirtyThreeAE_433 : Nat.Prime 433 := by norm_num
private theorem prime_thirtyThreeAE_283 : Nat.Prime 283 := by norm_num
private theorem prime_thirtyThreeAE_4523 : Nat.Prime 4523 := by norm_num
private theorem prime_thirtyThreeAE_64000451 : Nat.Prime 64000451 := by
  apply lucas_primality 64000451 (2 : ZMod 64000451)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (283, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (283, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod = 64000451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_283
      · exact prime_thirtyThreeAE_4523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 64000451) ^ 32000225 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 64000451) ^ 12800090 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 64000451) ^ 226150 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 64000451) ^ 14150 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_720517077359 : Nat.Prime 720517077359 := by
  apply lucas_primality 720517077359 (7 : ZMod 720517077359)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (433, 1), (64000451, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (433, 1), (64000451, 1)] : List FactorBlock).map factorBlockValue).prod = 720517077359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_433
      · exact prime_thirtyThreeAE_64000451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 720517077359) ^ 360258538679 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 720517077359) ^ 55424390566 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 720517077359) ^ 1664011726 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 720517077359) ^ 11258 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_67 : Nat.Prime 67 := by norm_num
private theorem prime_thirtyThreeAE_714443 : Nat.Prime 714443 := by norm_num
private theorem prime_thirtyThreeAE_95735363 : Nat.Prime 95735363 := by
  apply lucas_primality 95735363 (2 : ZMod 95735363)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (67, 1), (714443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (67, 1), (714443, 1)] : List FactorBlock).map factorBlockValue).prod = 95735363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_67
      · exact prime_thirtyThreeAE_714443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 95735363) ^ 47867681 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 95735363) ^ 1428886 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 95735363) ^ 134 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_12637067917 : Nat.Prime 12637067917 := by
  apply lucas_primality 12637067917 (5 : ZMod 12637067917)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (95735363, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (95735363, 1)] : List FactorBlock).map factorBlockValue).prod = 12637067917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_95735363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12637067917) ^ 6318533958 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 12637067917) ^ 4212355972 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 12637067917) ^ 1148824356 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 12637067917) ^ 132 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_7051483897687 : Nat.Prime 7051483897687 := by
  apply lucas_primality 7051483897687 (5 : ZMod 7051483897687)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (31, 1), (12637067917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (31, 1), (12637067917, 1)] : List FactorBlock).map factorBlockValue).prod = 7051483897687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_12637067917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7051483897687) ^ 3525741948843 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7051483897687) ^ 2350494632562 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7051483897687) ^ 227467222506 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7051483897687) ^ 558 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_459913 : Nat.Prime 459913 := by norm_num
private theorem prime_thirtyThreeAE_1210409 : Nat.Prime 1210409 := by norm_num
private theorem prime_thirtyThreeAE_3340097006503 : Nat.Prime 3340097006503 := by
  apply lucas_primality 3340097006503 (3 : ZMod 3340097006503)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (459913, 1), (1210409, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (459913, 1), (1210409, 1)] : List FactorBlock).map factorBlockValue).prod = 3340097006503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_459913
      · exact prime_thirtyThreeAE_1210409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3340097006503) ^ 1670048503251 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3340097006503) ^ 1113365668834 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3340097006503) ^ 7262454 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3340097006503) ^ 2759478 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_53441552104049 : Nat.Prime 53441552104049 := by
  apply lucas_primality 53441552104049 (3 : ZMod 53441552104049)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3340097006503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3340097006503, 1)] : List FactorBlock).map factorBlockValue).prod = 53441552104049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3340097006503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 53441552104049) ^ 26720776052024 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 53441552104049) ^ 16 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_409 : Nat.Prime 409 := by norm_num
private theorem prime_thirtyThreeAE_17321 : Nat.Prime 17321 := by norm_num
private theorem prime_thirtyThreeAE_1610179 : Nat.Prime 1610179 := by norm_num
private theorem prime_thirtyThreeAE_91255787021849 : Nat.Prime 91255787021849 := by
  apply lucas_primality 91255787021849 (3 : ZMod 91255787021849)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (409, 1), (17321, 1), (1610179, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (409, 1), (17321, 1), (1610179, 1)] : List FactorBlock).map factorBlockValue).prod = 91255787021849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_409
      · exact prime_thirtyThreeAE_17321
      · exact prime_thirtyThreeAE_1610179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 91255787021849) ^ 45627893510924 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 91255787021849) ^ 223119283672 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 91255787021849) ^ 5268505688 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 91255787021849) ^ 56674312 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_thirtyThreeAE_233 : Nat.Prime 233 := by norm_num
private theorem prime_thirtyThreeAE_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_thirtyThreeAE_6529 : Nat.Prime 6529 := by norm_num
private theorem prime_thirtyThreeAE_11503777 : Nat.Prime 11503777 := by norm_num
private theorem prime_thirtyThreeAE_30492110377557209 : Nat.Prime 30492110377557209 := by
  apply lucas_primality 30492110377557209 (3 : ZMod 30492110377557209)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (1637, 1), (6529, 1), (11503777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (1637, 1), (6529, 1), (11503777, 1)] : List FactorBlock).map factorBlockValue).prod = 30492110377557209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_1637
      · exact prime_thirtyThreeAE_6529
      · exact prime_thirtyThreeAE_11503777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30492110377557209) ^ 15246055188778604 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 983616463792168 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 18626823688184 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 4670257371352 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 30492110377557209) ^ 2650617304 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_28418646871883318789 : Nat.Prime 28418646871883318789 := by
  apply lucas_primality 28418646871883318789 (2 : ZMod 28418646871883318789)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (233, 1), (30492110377557209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (233, 1), (30492110377557209, 1)] : List FactorBlock).map factorBlockValue).prod = 28418646871883318789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_233
      · exact prime_thirtyThreeAE_30492110377557209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28418646871883318789) ^ 14209323435941659394 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28418646871883318789) ^ 121968441510228836 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28418646871883318789) ^ 932 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2554495330019847759305633 : Nat.Prime 2554495330019847759305633 := by
  apply lucas_primality 2554495330019847759305633 (3 : ZMod 2554495330019847759305633)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (53, 2), (28418646871883318789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (53, 2), (28418646871883318789, 1)] : List FactorBlock).map factorBlockValue).prod = 2554495330019847759305633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_28418646871883318789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2554495330019847759305633) ^ 1277247665009923879652816 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554495330019847759305633) ^ 48198025094714108666144 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554495330019847759305633) ^ 89888 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2971 : Nat.Prime 2971 := by norm_num
private theorem prime_thirtyThreeAE_768197 : Nat.Prime 768197 := by norm_num
private theorem prime_thirtyThreeAE_313 : Nat.Prime 313 := by norm_num
private theorem prime_thirtyThreeAE_776899 : Nat.Prime 776899 := by norm_num
private theorem prime_thirtyThreeAE_73 : Nat.Prime 73 := by norm_num
private theorem prime_thirtyThreeAE_131 : Nat.Prime 131 := by norm_num
private theorem prime_thirtyThreeAE_5569 : Nat.Prime 5569 := by norm_num
private theorem prime_thirtyThreeAE_319538083 : Nat.Prime 319538083 := by
  apply lucas_primality 319538083 (2 : ZMod 319538083)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (73, 1), (131, 1), (5569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (73, 1), (131, 1), (5569, 1)] : List FactorBlock).map factorBlockValue).prod = 319538083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_73
      · exact prime_thirtyThreeAE_131
      · exact prime_thirtyThreeAE_5569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 319538083) ^ 159769041 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 319538083) ^ 106512694 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 319538083) ^ 4377234 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 319538083) ^ 2439222 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 319538083) ^ 57378 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1709441354857832663 : Nat.Prime 1709441354857832663 := by
  apply lucas_primality 1709441354857832663 (5 : ZMod 1709441354857832663)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (313, 1), (776899, 1), (319538083, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (313, 1), (776899, 1), (319538083, 1)] : List FactorBlock).map factorBlockValue).prod = 1709441354857832663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_313
      · exact prime_thirtyThreeAE_776899
      · exact prime_thirtyThreeAE_319538083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1709441354857832663) ^ 854720677428916331 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1709441354857832663) ^ 155403759532530242 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1709441354857832663) ^ 5461473977181574 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1709441354857832663) ^ 2200339239538 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1709441354857832663) ^ 5349726514 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_71 : Nat.Prime 71 := by norm_num
private theorem prime_thirtyThreeAE_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_thirtyThreeAE_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_71
      · exact prime_thirtyThreeAE_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_thirtyThreeAE_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_thirtyThreeAE_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_81047
      · exact prime_thirtyThreeAE_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_4211 : Nat.Prime 4211 := by norm_num
private theorem prime_thirtyThreeAE_27077 : Nat.Prime 27077 := by norm_num
private theorem prime_thirtyThreeAE_75111599 : Nat.Prime 75111599 := by
  apply lucas_primality 75111599 (17 : ZMod 75111599)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (73, 1), (27077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (73, 1), (27077, 1)] : List FactorBlock).map factorBlockValue).prod = 75111599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_73
      · exact prime_thirtyThreeAE_27077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 75111599) ^ 37555799 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 3953242 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 1028926 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (17 : ZMod 75111599) ^ 2774 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_347 : Nat.Prime 347 := by norm_num
private theorem prime_thirtyThreeAE_827 : Nat.Prime 827 := by norm_num
private theorem prime_thirtyThreeAE_28687 : Nat.Prime 28687 := by norm_num
private theorem prime_thirtyThreeAE_104053 : Nat.Prime 104053 := by norm_num
private theorem prime_thirtyThreeAE_10279120799235109 : Nat.Prime 10279120799235109 := by
  apply lucas_primality 10279120799235109 (6 : ZMod 10279120799235109)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (347, 1), (827, 1), (28687, 1), (104053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (347, 1), (827, 1), (28687, 1), (104053, 1)] : List FactorBlock).map factorBlockValue).prod = 10279120799235109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_347
      · exact prime_thirtyThreeAE_827
      · exact prime_thirtyThreeAE_28687
      · exact prime_thirtyThreeAE_104053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10279120799235109) ^ 5139560399617554 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 3426373599745036 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 29622826510764 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 12429408463404 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 358319824284 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 10279120799235109) ^ 98787356436 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1521011 : Nat.Prime 1521011 := by norm_num
private theorem prime_thirtyThreeAE_197 : Nat.Prime 197 := by norm_num
private theorem prime_thirtyThreeAE_88789 : Nat.Prime 88789 := by norm_num
private theorem prime_thirtyThreeAE_34982867 : Nat.Prime 34982867 := by
  apply lucas_primality 34982867 (2 : ZMod 34982867)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (197, 1), (88789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (197, 1), (88789, 1)] : List FactorBlock).map factorBlockValue).prod = 34982867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_197
      · exact prime_thirtyThreeAE_88789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34982867) ^ 17491433 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 34982867) ^ 177578 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 34982867) ^ 394 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_16927 : Nat.Prime 16927 := by norm_num
private theorem prime_thirtyThreeAE_190711 : Nat.Prime 190711 := by norm_num
private theorem prime_thirtyThreeAE_12912660389 : Nat.Prime 12912660389 := by
  apply lucas_primality 12912660389 (2 : ZMod 12912660389)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (16927, 1), (190711, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (16927, 1), (190711, 1)] : List FactorBlock).map factorBlockValue).prod = 12912660389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_16927
      · exact prime_thirtyThreeAE_190711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12912660389) ^ 6456330194 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12912660389) ^ 762844 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12912660389) ^ 67708 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_25825320779 : Nat.Prime 25825320779 := by
  apply lucas_primality 25825320779 (2 : ZMod 25825320779)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (12912660389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (12912660389, 1)] : List FactorBlock).map factorBlockValue).prod = 25825320779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_12912660389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 25825320779) ^ 12912660389 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25825320779) ^ 2 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_19238070599306279500924523 : Nat.Prime 19238070599306279500924523 := by
  apply lucas_primality 19238070599306279500924523 (2 : ZMod 19238070599306279500924523)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (1521011, 1), (34982867, 1), (25825320779, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (1521011, 1), (34982867, 1), (25825320779, 1)] : List FactorBlock).map factorBlockValue).prod = 19238070599306279500924523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_1521011
      · exact prime_thirtyThreeAE_34982867
      · exact prime_thirtyThreeAE_25825320779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19238070599306279500924523) ^ 9619035299653139750462261 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19238070599306279500924523) ^ 2748295799900897071560646 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19238070599306279500924523) ^ 12648212668617307502 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19238070599306279500924523) ^ 549928357767425966 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19238070599306279500924523) ^ 744930557259518 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_230856847191675354011094277 : Nat.Prime 230856847191675354011094277 := by
  apply lucas_primality 230856847191675354011094277 (2 : ZMod 230856847191675354011094277)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19238070599306279500924523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19238070599306279500924523, 1)] : List FactorBlock).map factorBlockValue).prod = 230856847191675354011094277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_19238070599306279500924523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 230856847191675354011094277) ^ 115428423595837677005547138 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 230856847191675354011094277) ^ 76952282397225118003698092 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 230856847191675354011094277) ^ 12 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_5527 : Nat.Prime 5527 := by norm_num
private theorem prime_thirtyThreeAE_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_thirtyThreeAE_5399 : Nat.Prime 5399 := by norm_num
private theorem prime_thirtyThreeAE_27841908737 : Nat.Prime 27841908737 := by
  apply lucas_primality 27841908737 (3 : ZMod 27841908737)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 12), (1259, 1), (5399, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 12), (1259, 1), (5399, 1)] : List FactorBlock).map factorBlockValue).prod = 27841908737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_1259
      · exact prime_thirtyThreeAE_5399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 27841908737) ^ 13920954368 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 27841908737) ^ 22114304 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 27841908737) ^ 5156864 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_4503977 : Nat.Prime 4503977 := by norm_num
private theorem prime_thirtyThreeAE_135119311 : Nat.Prime 135119311 := by
  apply lucas_primality 135119311 (3 : ZMod 135119311)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (4503977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (4503977, 1)] : List FactorBlock).map factorBlockValue).prod = 135119311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_4503977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 135119311) ^ 67559655 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 135119311) ^ 45039770 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 135119311) ^ 27023862 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 135119311) ^ 30 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1006098389707 : Nat.Prime 1006098389707 := by
  apply lucas_primality 1006098389707 (2 : ZMod 1006098389707)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (73, 1), (135119311, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (73, 1), (135119311, 1)] : List FactorBlock).map factorBlockValue).prod = 1006098389707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_73
      · exact prime_thirtyThreeAE_135119311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1006098389707) ^ 503049194853 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006098389707) ^ 335366129902 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006098389707) ^ 59182258218 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006098389707) ^ 13782169722 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006098389707) ^ 7446 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_504210591839969175061063 : Nat.Prime 504210591839969175061063 := by
  apply lucas_primality 504210591839969175061063 (3 : ZMod 504210591839969175061063)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (27841908737, 1), (1006098389707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (27841908737, 1), (1006098389707, 1)] : List FactorBlock).map factorBlockValue).prod = 504210591839969175061063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_27841908737
      · exact prime_thirtyThreeAE_1006098389707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 504210591839969175061063) ^ 252105295919984587530531 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 504210591839969175061063) ^ 168070197279989725020354 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 504210591839969175061063) ^ 18109771014726 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 504210591839969175061063) ^ 501154357266 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_631 : Nat.Prime 631 := by norm_num
private theorem prime_thirtyThreeAE_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_thirtyThreeAE_3446959 : Nat.Prime 3446959 := by norm_num
private theorem prime_thirtyThreeAE_1883407 : Nat.Prime 1883407 := by norm_num
private theorem prime_thirtyThreeAE_134406001 : Nat.Prime 134406001 := by
  apply lucas_primality 134406001 (17 : ZMod 134406001)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (5, 3), (19, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (5, 3), (19, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod = 134406001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 134406001) ^ 67203000 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 44802000 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 26881200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 7074000 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (17 : ZMod 134406001) ^ 1026000 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1012564812501629 : Nat.Prime 1012564812501629 := by
  apply lucas_primality 1012564812501629 (2 : ZMod 1012564812501629)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1883407, 1), (134406001, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1883407, 1), (134406001, 1)] : List FactorBlock).map factorBlockValue).prod = 1012564812501629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_1883407
      · exact prime_thirtyThreeAE_134406001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1012564812501629) ^ 506282406250814 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012564812501629) ^ 537624004 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012564812501629) ^ 7533628 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1237 : Nat.Prime 1237 := by norm_num
private theorem prime_thirtyThreeAE_331 : Nat.Prime 331 := by norm_num
private theorem prime_thirtyThreeAE_4787 : Nat.Prime 4787 := by norm_num
private theorem prime_thirtyThreeAE_31689941 : Nat.Prime 31689941 := by
  apply lucas_primality 31689941 (2 : ZMod 31689941)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (331, 1), (4787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (331, 1), (4787, 1)] : List FactorBlock).map factorBlockValue).prod = 31689941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_331
      · exact prime_thirtyThreeAE_4787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31689941) ^ 15844970 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 31689941) ^ 6337988 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 31689941) ^ 95740 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 31689941) ^ 6620 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_757 : Nat.Prime 757 := by norm_num
private theorem prime_thirtyThreeAE_261013 : Nat.Prime 261013 := by norm_num
private theorem prime_thirtyThreeAE_73083641 : Nat.Prime 73083641 := by
  apply lucas_primality 73083641 (3 : ZMod 73083641)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (7, 1), (261013, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (7, 1), (261013, 1)] : List FactorBlock).map factorBlockValue).prod = 73083641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_261013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 73083641) ^ 36541820 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73083641) ^ 14616728 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73083641) ^ 10440520 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73083641) ^ 280 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_8916204203 : Nat.Prime 8916204203 := by
  apply lucas_primality 8916204203 (2 : ZMod 8916204203)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (61, 1), (73083641, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (61, 1), (73083641, 1)] : List FactorBlock).map factorBlockValue).prod = 8916204203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_61
      · exact prime_thirtyThreeAE_73083641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8916204203) ^ 4458102101 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8916204203) ^ 146167282 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8916204203) ^ 122 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_13499133163343 : Nat.Prime 13499133163343 := by
  apply lucas_primality 13499133163343 (5 : ZMod 13499133163343)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (757, 1), (8916204203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (757, 1), (8916204203, 1)] : List FactorBlock).map factorBlockValue).prod = 13499133163343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_757
      · exact prime_thirtyThreeAE_8916204203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 13499133163343) ^ 6749566581671 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 13499133163343) ^ 17832408406 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 13499133163343) ^ 1514 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1295916783680929 : Nat.Prime 1295916783680929 := by
  apply lucas_primality 1295916783680929 (37 : ZMod 1295916783680929)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (13499133163343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (13499133163343, 1)] : List FactorBlock).map factorBlockValue).prod = 1295916783680929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_13499133163343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (37 : ZMod 1295916783680929) ^ 647958391840464 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (37 : ZMod 1295916783680929) ^ 431972261226976 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (37 : ZMod 1295916783680929) ^ 96 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1971241267956403336089073 : Nat.Prime 1971241267956403336089073 := by
  apply lucas_primality 1971241267956403336089073 (5 : ZMod 1971241267956403336089073)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (31689941, 1), (1295916783680929, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (31689941, 1), (1295916783680929, 1)] : List FactorBlock).map factorBlockValue).prod = 1971241267956403336089073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_31689941
      · exact prime_thirtyThreeAE_1295916783680929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1971241267956403336089073) ^ 985620633978201668044536 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1971241267956403336089073) ^ 657080422652134445363024 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1971241267956403336089073) ^ 62204005616684592 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1971241267956403336089073) ^ 1521117168 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_167 : Nat.Prime 167 := by norm_num
private theorem prime_thirtyThreeAE_13995151 : Nat.Prime 13995151 := by norm_num
private theorem prime_thirtyThreeAE_282142244161 : Nat.Prime 282142244161 := by
  apply lucas_primality 282142244161 (13 : ZMod 282142244161)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 1), (7, 1), (13995151, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 1), (7, 1), (13995151, 1)] : List FactorBlock).map factorBlockValue).prod = 282142244161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_13995151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 282142244161) ^ 141071122080 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 282142244161) ^ 94047414720 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 282142244161) ^ 56428448832 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 282142244161) ^ 40306034880 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 282142244161) ^ 20160 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1218731 : Nat.Prime 1218731 := by norm_num
private theorem prime_thirtyThreeAE_19982881 : Nat.Prime 19982881 := by norm_num
private theorem prime_thirtyThreeAE_48707513088023 : Nat.Prime 48707513088023 := by
  apply lucas_primality 48707513088023 (5 : ZMod 48707513088023)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1218731, 1), (19982881, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1218731, 1), (19982881, 1)] : List FactorBlock).map factorBlockValue).prod = 48707513088023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_1218731
      · exact prime_thirtyThreeAE_19982881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 48707513088023) ^ 24353756544011 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 48707513088023) ^ 39965762 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 48707513088023) ^ 2437462 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_643 : Nat.Prime 643 := by norm_num
private theorem prime_thirtyThreeAE_977 : Nat.Prime 977 := by norm_num
private theorem prime_thirtyThreeAE_60308257 : Nat.Prime 60308257 := by
  apply lucas_primality 60308257 (5 : ZMod 60308257)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (643, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (643, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod = 60308257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_643
      · exact prime_thirtyThreeAE_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 60308257) ^ 30154128 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 20102752 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 93792 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 60308257) ^ 61728 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_5789592673 : Nat.Prime 5789592673 := by
  apply lucas_primality 5789592673 (10 : ZMod 5789592673)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (60308257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (60308257, 1)] : List FactorBlock).map factorBlockValue).prod = 5789592673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_60308257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 5789592673) ^ 2894796336 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 5789592673) ^ 1929864224 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 5789592673) ^ 96 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_35569 : Nat.Prime 35569 := by norm_num
private theorem prime_thirtyThreeAE_89 : Nat.Prime 89 := by norm_num
private theorem prime_thirtyThreeAE_27361 : Nat.Prime 27361 := by norm_num
private theorem prime_thirtyThreeAE_34091807 : Nat.Prime 34091807 := by
  apply lucas_primality 34091807 (5 : ZMod 34091807)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (89, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (89, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod = 34091807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_89
      · exact prime_thirtyThreeAE_27361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 34091807) ^ 17045903 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 4870258 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 383054 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34091807) ^ 1246 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_54819625657 : Nat.Prime 54819625657 := by
  apply lucas_primality 54819625657 (7 : ZMod 54819625657)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (67, 1), (34091807, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (67, 1), (34091807, 1)] : List FactorBlock).map factorBlockValue).prod = 54819625657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_67
      · exact prime_thirtyThreeAE_34091807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 54819625657) ^ 27409812828 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 18273208552 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 818203368 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 54819625657) ^ 1608 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_374376818878815937 : Nat.Prime 374376818878815937 := by
  apply lucas_primality 374376818878815937 (5 : ZMod 374376818878815937)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (35569, 1), (54819625657, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (35569, 1), (54819625657, 1)] : List FactorBlock).map factorBlockValue).prod = 374376818878815937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_35569
      · exact prime_thirtyThreeAE_54819625657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 374376818878815937) ^ 187188409439407968 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 124792272959605312 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 10525368126144 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 374376818878815937) ^ 6829248 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_79 : Nat.Prime 79 := by norm_num
private theorem prime_thirtyThreeAE_151 : Nat.Prime 151 := by norm_num
private theorem prime_thirtyThreeAE_389 : Nat.Prime 389 := by norm_num
private theorem prime_thirtyThreeAE_173 : Nat.Prime 173 := by norm_num
private theorem prime_thirtyThreeAE_3137370571 : Nat.Prime 3137370571 := by
  apply lucas_primality 3137370571 (3 : ZMod 3137370571)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (5, 1), (17, 1), (173, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (5, 1), (17, 1), (173, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod = 3137370571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_173
      · exact prime_thirtyThreeAE_439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3137370571) ^ 1568685285 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3137370571) ^ 1045790190 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3137370571) ^ 627474114 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3137370571) ^ 184551210 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3137370571) ^ 18135090 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3137370571) ^ 7146630 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_15077 : Nat.Prime 15077 := by norm_num
private theorem prime_thirtyThreeAE_141044581151 : Nat.Prime 141044581151 := by
  apply lucas_primality 141044581151 (11 : ZMod 141044581151)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (11, 1), (73, 1), (233, 1), (15077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (11, 1), (73, 1), (233, 1), (15077, 1)] : List FactorBlock).map factorBlockValue).prod = 141044581151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_73
      · exact prime_thirtyThreeAE_233
      · exact prime_thirtyThreeAE_15077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 141044581151) ^ 70522290575 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 141044581151) ^ 28208916230 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 141044581151) ^ 12822234650 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 141044581151) ^ 1932117550 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 141044581151) ^ 605341550 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 141044581151) ^ 9354950 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_319027 : Nat.Prime 319027 := by norm_num
private theorem prime_thirtyThreeAE_357613 : Nat.Prime 357613 := by norm_num
private theorem prime_thirtyThreeAE_4117523 : Nat.Prime 4117523 := by norm_num
private theorem prime_thirtyThreeAE_935880037717 : Nat.Prime 935880037717 := by
  apply lucas_primality 935880037717 (2 : ZMod 935880037717)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (31, 1), (47, 1), (4117523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (31, 1), (47, 1), (4117523, 1)] : List FactorBlock).map factorBlockValue).prod = 935880037717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_4117523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 935880037717) ^ 467940018858 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 935880037717) ^ 311960012572 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 935880037717) ^ 71990772132 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 935880037717) ^ 30189678636 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 935880037717) ^ 19912341228 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 935880037717) ^ 227292 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_17098528289089591 : Nat.Prime 17098528289089591 := by
  apply lucas_primality 17098528289089591 (3 : ZMod 17098528289089591)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (7, 1), (29, 1), (935880037717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (7, 1), (29, 1), (935880037717, 1)] : List FactorBlock).map factorBlockValue).prod = 17098528289089591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_935880037717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17098528289089591) ^ 8549264144544795 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17098528289089591) ^ 5699509429696530 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17098528289089591) ^ 3419705657817918 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17098528289089591) ^ 2442646898441370 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17098528289089591) ^ 589604423761710 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17098528289089591) ^ 18270 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_32531 : Nat.Prime 32531 := by norm_num
private theorem prime_thirtyThreeAE_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_thirtyThreeAE_21160721 : Nat.Prime 21160721 := by
  apply lucas_primality 21160721 (12 : ZMod 21160721)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (7, 1), (29, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (7, 1), (29, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod = 21160721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_1303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 21160721) ^ 10580360 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (12 : ZMod 21160721) ^ 4232144 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (12 : ZMod 21160721) ^ 3022960 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (12 : ZMod 21160721) ^ 729680 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (12 : ZMod 21160721) ^ 16240 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_thirtyThreeAE_154807 : Nat.Prime 154807 := by norm_num
private theorem prime_thirtyThreeAE_4819414370321 : Nat.Prime 4819414370321 := by
  apply lucas_primality 4819414370321 (3 : ZMod 4819414370321)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (11, 1), (17, 1), (2081, 1), (154807, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (11, 1), (17, 1), (2081, 1), (154807, 1)] : List FactorBlock).map factorBlockValue).prod = 4819414370321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_2081
      · exact prime_thirtyThreeAE_154807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4819414370321) ^ 2409707185160 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 963882874064 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 438128579120 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 283494962960 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 2315912720 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4819414370321) ^ 31131760 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_269887204737977 : Nat.Prime 269887204737977 := by
  apply lucas_primality 269887204737977 (3 : ZMod 269887204737977)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (4819414370321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (4819414370321, 1)] : List FactorBlock).map factorBlockValue).prod = 269887204737977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_4819414370321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 269887204737977) ^ 134943602368988 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 269887204737977) ^ 38555314962568 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 269887204737977) ^ 56 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_57110078409302094014171 : Nat.Prime 57110078409302094014171 := by
  apply lucas_primality 57110078409302094014171 (6 : ZMod 57110078409302094014171)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (21160721, 1), (269887204737977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (21160721, 1), (269887204737977, 1)] : List FactorBlock).map factorBlockValue).prod = 57110078409302094014171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_21160721
      · exact prime_thirtyThreeAE_269887204737977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 57110078409302094014171) ^ 28555039204651047007085 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 11422015681860418802834 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 2698872047379770 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 57110078409302094014171) ^ 211607210 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_thirtyThreeAE_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_thirtyThreeAE_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_thirtyThreeAE_149 : Nat.Prime 149 := by norm_num
private theorem prime_thirtyThreeAE_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_thirtyThreeAE_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_thirtyThreeAE_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_149
      · exact prime_thirtyThreeAE_1429
      · exact prime_thirtyThreeAE_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_587 : Nat.Prime 587 := by norm_num
private theorem prime_thirtyThreeAE_419 : Nat.Prime 419 := by norm_num
private theorem prime_thirtyThreeAE_60758353 : Nat.Prime 60758353 := by
  apply lucas_primality 60758353 (5 : ZMod 60758353)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (19, 1), (53, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (19, 1), (53, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod = 60758353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 60758353) ^ 30379176 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 60758353) ^ 20252784 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 60758353) ^ 3197808 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 60758353) ^ 1146384 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 60758353) ^ 145008 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_673 : Nat.Prime 673 := by norm_num
private theorem prime_thirtyThreeAE_1014161 : Nat.Prime 1014161 := by norm_num
private theorem prime_thirtyThreeAE_40850405081 : Nat.Prime 40850405081 := by
  apply lucas_primality 40850405081 (6 : ZMod 40850405081)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (19, 1), (53, 1), (1014161, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (19, 1), (53, 1), (1014161, 1)] : List FactorBlock).map factorBlockValue).prod = 40850405081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_1014161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 40850405081) ^ 20425202540 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 40850405081) ^ 8170081016 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 40850405081) ^ 2150021320 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 40850405081) ^ 770762360 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 40850405081) ^ 40280 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_47561718131757491 : Nat.Prime 47561718131757491 := by
  apply lucas_primality 47561718131757491 (2 : ZMod 47561718131757491)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (173, 1), (673, 1), (40850405081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (173, 1), (673, 1), (40850405081, 1)] : List FactorBlock).map factorBlockValue).prod = 47561718131757491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_173
      · exact prime_thirtyThreeAE_673
      · exact prime_thirtyThreeAE_40850405081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47561718131757491) ^ 23780859065878745 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 47561718131757491) ^ 9512343626351498 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 47561718131757491) ^ 274923226195130 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 47561718131757491) ^ 70671200790130 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 47561718131757491) ^ 1164290 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_857 : Nat.Prime 857 := by norm_num
private theorem prime_thirtyThreeAE_32869 : Nat.Prime 32869 := by norm_num
private theorem prime_thirtyThreeAE_47659 : Nat.Prime 47659 := by norm_num
private theorem prime_thirtyThreeAE_55379759 : Nat.Prime 55379759 := by
  apply lucas_primality 55379759 (7 : ZMod 55379759)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (83, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (83, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod = 55379759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_83
      · exact prime_thirtyThreeAE_47659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 55379759) ^ 27689879 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 7911394 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 667226 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 55379759) ^ 1162 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_25439 : Nat.Prime 25439 := by norm_num
private theorem prime_thirtyThreeAE_512047 : Nat.Prime 512047 := by norm_num
private theorem prime_thirtyThreeAE_260519272661 : Nat.Prime 260519272661 := by
  apply lucas_primality 260519272661 (3 : ZMod 260519272661)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (25439, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (25439, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod = 260519272661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_25439
      · exact prime_thirtyThreeAE_512047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 260519272661) ^ 130259636330 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 52103854532 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 10240940 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 260519272661) ^ 508780 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_57709978139285874797 : Nat.Prime 57709978139285874797 := by
  apply lucas_primality 57709978139285874797 (2 : ZMod 57709978139285874797)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (55379759, 1), (260519272661, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (55379759, 1), (260519272661, 1)] : List FactorBlock).map factorBlockValue).prod = 57709978139285874797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_55379759
      · exact prime_thirtyThreeAE_260519272661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57709978139285874797) ^ 28854989069642937398 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 57709978139285874797) ^ 1042077090644 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 57709978139285874797) ^ 221519036 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_11969 : Nat.Prime 11969 := by norm_num
private theorem prime_thirtyThreeAE_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_thirtyThreeAE_87739 : Nat.Prime 87739 := by norm_num
private theorem prime_thirtyThreeAE_7039 : Nat.Prime 7039 := by norm_num
private theorem prime_thirtyThreeAE_81173749 : Nat.Prime 81173749 := by
  apply lucas_primality 81173749 (2 : ZMod 81173749)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (31, 2), (7039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (31, 2), (7039, 1)] : List FactorBlock).map factorBlockValue).prod = 81173749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_7039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 81173749) ^ 40586874 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 81173749) ^ 27057916 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 81173749) ^ 2618508 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 81173749) ^ 11532 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_4259017930979579 : Nat.Prime 4259017930979579 := by
  apply lucas_primality 4259017930979579 (6 : ZMod 4259017930979579)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (23, 1), (87739, 1), (81173749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (23, 1), (87739, 1), (81173749, 1)] : List FactorBlock).map factorBlockValue).prod = 4259017930979579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_87739
      · exact prime_thirtyThreeAE_81173749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4259017930979579) ^ 2129508965489789 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 4259017930979579) ^ 327616763921506 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 4259017930979579) ^ 185174692651286 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 4259017930979579) ^ 48541901902 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 4259017930979579) ^ 52467922 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_130386188237590892565377 : Nat.Prime 130386188237590892565377 := by
  apply lucas_primality 130386188237590892565377 (3 : ZMod 130386188237590892565377)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (11, 1), (17, 1), (1279, 1), (4259017930979579, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (11, 1), (17, 1), (1279, 1), (4259017930979579, 1)] : List FactorBlock).map factorBlockValue).prod = 130386188237590892565377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_1279
      · exact prime_thirtyThreeAE_4259017930979579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 130386188237590892565377) ^ 65193094118795446282688 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 130386188237590892565377) ^ 11853289839780990233216 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 130386188237590892565377) ^ 7669775778681817209728 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 130386188237590892565377) ^ 101943853195927202944 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 130386188237590892565377) ^ 30614144 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_thirtyThreeAE_599 : Nat.Prime 599 := by norm_num
private theorem prime_thirtyThreeAE_1571 : Nat.Prime 1571 := by norm_num
private theorem prime_thirtyThreeAE_169385221 : Nat.Prime 169385221 := by
  apply lucas_primality 169385221 (2 : ZMod 169385221)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (599, 1), (1571, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (599, 1), (1571, 1)] : List FactorBlock).map factorBlockValue).prod = 169385221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_599
      · exact prime_thirtyThreeAE_1571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 169385221) ^ 84692610 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 169385221) ^ 56461740 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 169385221) ^ 33877044 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 169385221) ^ 282780 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 169385221) ^ 107820 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_128055227077 : Nat.Prime 128055227077 := by
  apply lucas_primality 128055227077 (5 : ZMod 128055227077)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (7, 1), (169385221, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (7, 1), (169385221, 1)] : List FactorBlock).map factorBlockValue).prod = 128055227077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_169385221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 128055227077) ^ 64027613538 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 128055227077) ^ 42685075692 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 128055227077) ^ 18293603868 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 128055227077) ^ 756 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_139 : Nat.Prime 139 := by norm_num
private theorem prime_thirtyThreeAE_15299 : Nat.Prime 15299 := by norm_num
private theorem prime_thirtyThreeAE_1171921 : Nat.Prime 1171921 := by norm_num
private theorem prime_thirtyThreeAE_4984322987363 : Nat.Prime 4984322987363 := by
  apply lucas_primality 4984322987363 (2 : ZMod 4984322987363)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (139, 1), (15299, 1), (1171921, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (139, 1), (15299, 1), (1171921, 1)] : List FactorBlock).map factorBlockValue).prod = 4984322987363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_139
      · exact prime_thirtyThreeAE_15299
      · exact prime_thirtyThreeAE_1171921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4984322987363) ^ 2492161493681 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4984322987363) ^ 35858438758 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4984322987363) ^ 325794038 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4984322987363) ^ 4253122 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_101 : Nat.Prime 101 := by norm_num
private theorem prime_thirtyThreeAE_2152009 : Nat.Prime 2152009 := by norm_num
private theorem prime_thirtyThreeAE_25824109 : Nat.Prime 25824109 := by
  apply lucas_primality 25824109 (2 : ZMod 25824109)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2152009, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2152009, 1)] : List FactorBlock).map factorBlockValue).prod = 25824109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_2152009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25824109) ^ 12912054 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25824109) ^ 8608036 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25824109) ^ 12 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_10691 : Nat.Prime 10691 := by norm_num
private theorem prime_thirtyThreeAE_157 : Nat.Prime 157 := by norm_num
private theorem prime_thirtyThreeAE_39113 : Nat.Prime 39113 := by norm_num
private theorem prime_thirtyThreeAE_19748623057 : Nat.Prime 19748623057 := by
  apply lucas_primality 19748623057 (10 : ZMod 19748623057)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (67, 1), (157, 1), (39113, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (67, 1), (157, 1), (39113, 1)] : List FactorBlock).map factorBlockValue).prod = 19748623057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_67
      · exact prime_thirtyThreeAE_157
      · exact prime_thirtyThreeAE_39113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 19748623057) ^ 9874311528 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 6582874352 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 294755568 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 125787408 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 19748623057) ^ 504912 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_554011756364663489 : Nat.Prime 554011756364663489 := by
  apply lucas_primality 554011756364663489 (3 : ZMod 554011756364663489)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (41, 1), (10691, 1), (19748623057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (41, 1), (10691, 1), (19748623057, 1)] : List FactorBlock).map factorBlockValue).prod = 554011756364663489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_10691
      · exact prime_thirtyThreeAE_19748623057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 554011756364663489) ^ 277005878182331744 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 13512481862552768 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 51820386901568 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 554011756364663489) ^ 28053184 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_10529 : Nat.Prime 10529 := by norm_num
private theorem prime_thirtyThreeAE_37831 : Nat.Prime 37831 := by norm_num
private theorem prime_thirtyThreeAE_230230462223 : Nat.Prime 230230462223 := by
  apply lucas_primality 230230462223 (5 : ZMod 230230462223)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 2), (10529, 1), (37831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 2), (10529, 1), (37831, 1)] : List FactorBlock).map factorBlockValue).prod = 230230462223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_10529
      · exact prime_thirtyThreeAE_37831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 230230462223) ^ 115115231111 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 230230462223) ^ 13542968366 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 230230462223) ^ 21866318 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 230230462223) ^ 6085762 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_109 : Nat.Prime 109 := by norm_num
private theorem prime_thirtyThreeAE_193 : Nat.Prime 193 := by norm_num
private theorem prime_thirtyThreeAE_199 : Nat.Prime 199 := by norm_num
private theorem prime_thirtyThreeAE_359 : Nat.Prime 359 := by norm_num
private theorem prime_thirtyThreeAE_1158201493 : Nat.Prime 1158201493 := by
  apply lucas_primality 1158201493 (5 : ZMod 1158201493)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (193, 1), (199, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (193, 1), (199, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod = 1158201493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_193
      · exact prime_thirtyThreeAE_199
      · exact prime_thirtyThreeAE_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1158201493) ^ 579100746 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1158201493) ^ 386067164 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1158201493) ^ 165457356 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1158201493) ^ 6001044 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1158201493) ^ 5820108 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1158201493) ^ 3226188 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1633064105131 : Nat.Prime 1633064105131 := by
  apply lucas_primality 1633064105131 (2 : ZMod 1633064105131)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (47, 1), (1158201493, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (47, 1), (1158201493, 1)] : List FactorBlock).map factorBlockValue).prod = 1633064105131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_1158201493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1633064105131) ^ 816532052565 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633064105131) ^ 544354701710 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633064105131) ^ 326612821026 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633064105131) ^ 34746044790 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1633064105131) ^ 1410 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_6052135573615487 : Nat.Prime 6052135573615487 := by
  apply lucas_primality 6052135573615487 (5 : ZMod 6052135573615487)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (109, 1), (1633064105131, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (109, 1), (1633064105131, 1)] : List FactorBlock).map factorBlockValue).prod = 6052135573615487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_109
      · exact prime_thirtyThreeAE_1633064105131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6052135573615487) ^ 3026067786807743 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6052135573615487) ^ 356007974918558 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6052135573615487) ^ 55524179574454 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6052135573615487) ^ 3706 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_thirtyThreeAE_8271049 : Nat.Prime 8271049 := by norm_num
private theorem prime_thirtyThreeAE_24749 : Nat.Prime 24749 := by norm_num
private theorem prime_thirtyThreeAE_84449 : Nat.Prime 84449 := by norm_num
private theorem prime_thirtyThreeAE_336302273857309 : Nat.Prime 336302273857309 := by
  apply lucas_primality 336302273857309 (2 : ZMod 336302273857309)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (23, 1), (53, 1), (24749, 1), (84449, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (23, 1), (53, 1), (24749, 1), (84449, 1)] : List FactorBlock).map factorBlockValue).prod = 336302273857309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_24749
      · exact prime_thirtyThreeAE_84449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 336302273857309) ^ 168151136928654 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 336302273857309) ^ 112100757952436 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 336302273857309) ^ 30572933987028 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 336302273857309) ^ 14621837993796 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 336302273857309) ^ 6345325921836 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 336302273857309) ^ 13588519692 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 336302273857309) ^ 3982312092 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_37967 : Nat.Prime 37967 := by norm_num
private theorem prime_thirtyThreeAE_834527 : Nat.Prime 834527 := by norm_num
private theorem prime_thirtyThreeAE_3072847 : Nat.Prime 3072847 := by norm_num
private theorem prime_thirtyThreeAE_810913 : Nat.Prime 810913 := by norm_num
private theorem prime_thirtyThreeAE_188131817 : Nat.Prime 188131817 := by
  apply lucas_primality 188131817 (3 : ZMod 188131817)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (29, 1), (810913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (29, 1), (810913, 1)] : List FactorBlock).map factorBlockValue).prod = 188131817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_810913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 188131817) ^ 94065908 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 188131817) ^ 6487304 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 188131817) ^ 232 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_941 : Nat.Prime 941 := by norm_num
private theorem prime_thirtyThreeAE_293 : Nat.Prime 293 := by norm_num
private theorem prime_thirtyThreeAE_31509221 : Nat.Prime 31509221 := by
  apply lucas_primality 31509221 (2 : ZMod 31509221)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (19, 1), (283, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (19, 1), (283, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod = 31509221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_283
      · exact prime_thirtyThreeAE_293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31509221) ^ 15754610 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 31509221) ^ 6301844 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 31509221) ^ 1658380 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 31509221) ^ 111340 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 31509221) ^ 107540 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_10650116699 : Nat.Prime 10650116699 := by
  apply lucas_primality 10650116699 (2 : ZMod 10650116699)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 2), (31509221, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 2), (31509221, 1)] : List FactorBlock).map factorBlockValue).prod = 10650116699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_31509221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10650116699) ^ 5325058349 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10650116699) ^ 819239746 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10650116699) ^ 338 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_353 : Nat.Prime 353 := by norm_num
private theorem prime_thirtyThreeAE_373 : Nat.Prime 373 := by norm_num
private theorem prime_thirtyThreeAE_2064421 : Nat.Prime 2064421 := by norm_num
private theorem prime_thirtyThreeAE_125580954875839 : Nat.Prime 125580954875839 := by
  apply lucas_primality 125580954875839 (3 : ZMod 125580954875839)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 1), (353, 1), (373, 1), (2064421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 1), (353, 1), (373, 1), (2064421, 1)] : List FactorBlock).map factorBlockValue).prod = 125580954875839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_353
      · exact prime_thirtyThreeAE_373
      · exact prime_thirtyThreeAE_2064421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 125580954875839) ^ 62790477437919 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125580954875839) ^ 41860318291946 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125580954875839) ^ 17940136410834 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125580954875839) ^ 11416450443258 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125580954875839) ^ 355753413246 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125580954875839) ^ 336678163206 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125580954875839) ^ 60831078 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_9851 : Nat.Prime 9851 := by norm_num
private theorem prime_thirtyThreeAE_14699 : Nat.Prime 14699 := by norm_num
private theorem prime_thirtyThreeAE_69193 : Nat.Prime 69193 := by norm_num
private theorem prime_thirtyThreeAE_227 : Nat.Prime 227 := by norm_num
private theorem prime_thirtyThreeAE_487 : Nat.Prime 487 := by norm_num
private theorem prime_thirtyThreeAE_201827 : Nat.Prime 201827 := by norm_num
private theorem prime_thirtyThreeAE_121688410067443 : Nat.Prime 121688410067443 := by
  apply lucas_primality 121688410067443 (2 : ZMod 121688410067443)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (101, 1), (227, 1), (487, 1), (201827, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (101, 1), (227, 1), (487, 1), (201827, 1)] : List FactorBlock).map factorBlockValue).prod = 121688410067443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_101
      · exact prime_thirtyThreeAE_227
      · exact prime_thirtyThreeAE_487
      · exact prime_thirtyThreeAE_201827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 121688410067443) ^ 60844205033721 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 121688410067443) ^ 40562803355814 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 121688410067443) ^ 1204835743242 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 121688410067443) ^ 536072291046 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 121688410067443) ^ 249873531966 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 121688410067443) ^ 602934246 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_103 : Nat.Prime 103 := by norm_num
private theorem prime_thirtyThreeAE_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_thirtyThreeAE_107 : Nat.Prime 107 := by norm_num
private theorem prime_thirtyThreeAE_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_thirtyThreeAE_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_thirtyThreeAE_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_thirtyThreeAE_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_35279
      · exact prime_thirtyThreeAE_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_61717
      · exact prime_thirtyThreeAE_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_107
      · exact prime_thirtyThreeAE_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_thirtyThreeAE_28111 : Nat.Prime 28111 := by norm_num
private theorem prime_thirtyThreeAE_36469 : Nat.Prime 36469 := by norm_num
private theorem prime_thirtyThreeAE_8547941 : Nat.Prime 8547941 := by norm_num
private theorem prime_thirtyThreeAE_1231352698299551 : Nat.Prime 1231352698299551 := by
  apply lucas_primality 1231352698299551 (7 : ZMod 1231352698299551)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (79, 1), (36469, 1), (8547941, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (79, 1), (36469, 1), (8547941, 1)] : List FactorBlock).map factorBlockValue).prod = 1231352698299551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_79
      · exact prime_thirtyThreeAE_36469
      · exact prime_thirtyThreeAE_8547941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1231352698299551) ^ 615676349149775 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1231352698299551) ^ 246270539659910 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1231352698299551) ^ 15586743016450 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1231352698299551) ^ 33764366950 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1231352698299551) ^ 144052550 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_13335549722584137331 : Nat.Prime 13335549722584137331 := by
  apply lucas_primality 13335549722584137331 (2 : ZMod 13335549722584137331)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (19, 2), (1231352698299551, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (19, 2), (1231352698299551, 1)] : List FactorBlock).map factorBlockValue).prod = 13335549722584137331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_1231352698299551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13335549722584137331) ^ 6667774861292068665 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13335549722584137331) ^ 4445183240861379110 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13335549722584137331) ^ 2667109944516827466 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13335549722584137331) ^ 701871038030744070 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13335549722584137331) ^ 10830 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1114708776439803852224998081 : Nat.Prime 1114708776439803852224998081 := by
  apply lucas_primality 1114708776439803852224998081 (79 : ZMod 1114708776439803852224998081)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 1), (7, 1), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 1), (7, 1), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 1114708776439803852224998081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_59
      · exact prime_thirtyThreeAE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 1114708776439803852224998081) ^ 557354388219901926112499040 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 371569592146601284074999360 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 222941755287960770444999616 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 159244110919971978889285440 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 101337161494527622929545280 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 85746828956907988632692160 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 65571104496459050130882240 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 58668882970515992222368320 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 48465598975643645748912960 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 38438233670338063869827520 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 35958347627090446845967680 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 30127264228102806816891840 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 27188018937556191517682880 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 25923459917204740749418560 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 23717208009357528770744640 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 21032241064901959475943360 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 18893369092200065291949120 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 1114708776439803852224998081) ^ 18273914367865636921721280 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_257 : Nat.Prime 257 := by norm_num
private theorem prime_thirtyThreeAE_5426387 : Nat.Prime 5426387 := by norm_num
private theorem prime_thirtyThreeAE_727 : Nat.Prime 727 := by norm_num
private theorem prime_thirtyThreeAE_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_thirtyThreeAE_17749 : Nat.Prime 17749 := by norm_num
private theorem prime_thirtyThreeAE_190507613573 : Nat.Prime 190507613573 := by
  apply lucas_primality 190507613573 (2 : ZMod 190507613573)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (727, 1), (3691, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (727, 1), (3691, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod = 190507613573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_727
      · exact prime_thirtyThreeAE_3691
      · exact prime_thirtyThreeAE_17749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 190507613573) ^ 95253806786 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 262046236 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 51614092 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 190507613573) ^ 10733428 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1143045681439 : Nat.Prime 1143045681439 := by
  apply lucas_primality 1143045681439 (6 : ZMod 1143045681439)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (190507613573, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (190507613573, 1)] : List FactorBlock).map factorBlockValue).prod = 1143045681439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_190507613573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1143045681439) ^ 571522840719 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143045681439) ^ 381015227146 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1143045681439) ^ 6 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_558234740355005780371 : Nat.Prime 558234740355005780371 := by
  apply lucas_primality 558234740355005780371 (2 : ZMod 558234740355005780371)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (5426387, 1), (1143045681439, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (5426387, 1), (1143045681439, 1)] : List FactorBlock).map factorBlockValue).prod = 558234740355005780371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_5426387
      · exact prime_thirtyThreeAE_1143045681439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 558234740355005780371) ^ 279117370177502890185 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 186078246785001926790 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 111646948071001156074 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 102874111329510 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 558234740355005780371) ^ 488374830 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_3349408442130034682227 : Nat.Prime 3349408442130034682227 := by
  apply lucas_primality 3349408442130034682227 (2 : ZMod 3349408442130034682227)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (558234740355005780371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (558234740355005780371, 1)] : List FactorBlock).map factorBlockValue).prod = 3349408442130034682227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_558234740355005780371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3349408442130034682227) ^ 1674704221065017341113 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3349408442130034682227) ^ 1116469480710011560742 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3349408442130034682227) ^ 6 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1054454247983598238591214401 : Nat.Prime 1054454247983598238591214401 := by
  apply lucas_primality 1054454247983598238591214401 (97 : ZMod 1054454247983598238591214401)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 1054454247983598238591214401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_59
      · exact prime_thirtyThreeAE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 1054454247983598238591214401) ^ 527227123991799119295607200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 351484749327866079530404800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 210890849596719647718242880 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 150636321140514034084459200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 95859477089418021690110400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 81111865229507556814708800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 62026720469623425799483200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 55497591999136749399537600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 45845836868852097330052800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 36360491309779249606593600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 34014653160761233502942400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 25718396292282883868078400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 24522191813572052060260800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 22435196765608473161515200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 19895363169501853558324800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 17872105898027088789681600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (97 : ZMod 1054454247983598238591214401) ^ 17286135212845872763790400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_487601 : Nat.Prime 487601 := by norm_num
private theorem prime_thirtyThreeAE_444692113 : Nat.Prime 444692113 := by
  apply lucas_primality 444692113 (5 : ZMod 444692113)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (19, 1), (487601, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (19, 1), (487601, 1)] : List FactorBlock).map factorBlockValue).prod = 444692113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_487601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 444692113) ^ 222346056 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 444692113) ^ 148230704 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 444692113) ^ 23404848 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 444692113) ^ 912 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_971 : Nat.Prime 971 := by norm_num
private theorem prime_thirtyThreeAE_14869 : Nat.Prime 14869 := by norm_num
private theorem prime_thirtyThreeAE_1601 : Nat.Prime 1601 := by norm_num
private theorem prime_thirtyThreeAE_57803 : Nat.Prime 57803 := by norm_num
private theorem prime_thirtyThreeAE_555255619 : Nat.Prime 555255619 := by
  apply lucas_primality 555255619 (2 : ZMod 555255619)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1601, 1), (57803, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1601, 1), (57803, 1)] : List FactorBlock).map factorBlockValue).prod = 555255619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_1601
      · exact prime_thirtyThreeAE_57803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 555255619) ^ 277627809 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 555255619) ^ 185085206 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 555255619) ^ 346818 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 555255619) ^ 9606 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_48100014124455487 : Nat.Prime 48100014124455487 := by
  apply lucas_primality 48100014124455487 (3 : ZMod 48100014124455487)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (971, 1), (14869, 1), (555255619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (971, 1), (14869, 1), (555255619, 1)] : List FactorBlock).map factorBlockValue).prod = 48100014124455487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_971
      · exact prime_thirtyThreeAE_14869
      · exact prime_thirtyThreeAE_555255619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48100014124455487) ^ 24050007062227743 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 48100014124455487) ^ 16033338041485162 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 48100014124455487) ^ 49536574793466 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 48100014124455487) ^ 3234919236294 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 48100014124455487) ^ 86626794 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2308800677973863377 : Nat.Prime 2308800677973863377 := by
  apply lucas_primality 2308800677973863377 (7 : ZMod 2308800677973863377)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (48100014124455487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (48100014124455487, 1)] : List FactorBlock).map factorBlockValue).prod = 2308800677973863377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_48100014124455487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2308800677973863377) ^ 1154400338986931688 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2308800677973863377) ^ 769600225991287792 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2308800677973863377) ^ 48 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_thirtyThreeAE_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_thirtyThreeAE_32843 : Nat.Prime 32843 := by norm_num
private theorem prime_thirtyThreeAE_29304298123 : Nat.Prime 29304298123 := by
  apply lucas_primality 29304298123 (2 : ZMod 29304298123)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 2), (1229, 1), (32843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 2), (1229, 1), (32843, 1)] : List FactorBlock).map factorBlockValue).prod = 29304298123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_1229
      · exact prime_thirtyThreeAE_32843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29304298123) ^ 14652149061 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 9768099374 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 2664027102 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 23844018 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29304298123) ^ 892254 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_967 : Nat.Prime 967 := by norm_num
private theorem prime_thirtyThreeAE_6379 : Nat.Prime 6379 := by norm_num
private theorem prime_thirtyThreeAE_98695889 : Nat.Prime 98695889 := by
  apply lucas_primality 98695889 (3 : ZMod 98695889)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (967, 1), (6379, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (967, 1), (6379, 1)] : List FactorBlock).map factorBlockValue).prod = 98695889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_967
      · exact prime_thirtyThreeAE_6379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 98695889) ^ 49347944 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 98695889) ^ 102064 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 98695889) ^ 15472 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_3496992739049 : Nat.Prime 3496992739049 := by
  apply lucas_primality 3496992739049 (3 : ZMod 3496992739049)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (43, 1), (103, 1), (98695889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (43, 1), (103, 1), (98695889, 1)] : List FactorBlock).map factorBlockValue).prod = 3496992739049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_103
      · exact prime_thirtyThreeAE_98695889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3496992739049) ^ 1748496369524 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 81325412536 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 33951385816 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3496992739049) ^ 35432 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_614861506554349437030163 : Nat.Prime 614861506554349437030163 := by
  apply lucas_primality 614861506554349437030163 (3 : ZMod 614861506554349437030163)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29304298123, 1), (3496992739049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29304298123, 1), (3496992739049, 1)] : List FactorBlock).map factorBlockValue).prod = 614861506554349437030163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_29304298123
      · exact prime_thirtyThreeAE_3496992739049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 614861506554349437030163) ^ 307430753277174718515081 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 204953835518116479010054 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 20981956434294 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 614861506554349437030163) ^ 175825788738 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_14449 : Nat.Prime 14449 := by norm_num
private theorem prime_thirtyThreeAE_594571 : Nat.Prime 594571 := by norm_num
private theorem prime_thirtyThreeAE_660521 : Nat.Prime 660521 := by norm_num
private theorem prime_thirtyThreeAE_203051 : Nat.Prime 203051 := by norm_num
private theorem prime_thirtyThreeAE_423259 : Nat.Prime 423259 := by norm_num
private theorem prime_thirtyThreeAE_171886326419 : Nat.Prime 171886326419 := by
  apply lucas_primality 171886326419 (2 : ZMod 171886326419)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (203051, 1), (423259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (203051, 1), (423259, 1)] : List FactorBlock).map factorBlockValue).prod = 171886326419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_203051
      · exact prime_thirtyThreeAE_423259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 171886326419) ^ 85943163209 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 171886326419) ^ 846518 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 171886326419) ^ 406102 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_457 : Nat.Prime 457 := by norm_num
private theorem prime_thirtyThreeAE_463 : Nat.Prime 463 := by norm_num
private theorem prime_thirtyThreeAE_304903 : Nat.Prime 304903 := by norm_num
private theorem prime_thirtyThreeAE_129278873 : Nat.Prime 129278873 := by
  apply lucas_primality 129278873 (3 : ZMod 129278873)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (53, 1), (304903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (53, 1), (304903, 1)] : List FactorBlock).map factorBlockValue).prod = 129278873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_304903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 129278873) ^ 64639436 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 129278873) ^ 2439224 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 129278873) ^ 424 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_12410771809 : Nat.Prime 12410771809 := by
  apply lucas_primality 12410771809 (33 : ZMod 12410771809)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (129278873, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (129278873, 1)] : List FactorBlock).map factorBlockValue).prod = 12410771809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_129278873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (33 : ZMod 12410771809) ^ 6205385904 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (33 : ZMod 12410771809) ^ 4136923936 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (33 : ZMod 12410771809) ^ 96 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_829 : Nat.Prime 829 := by norm_num
private theorem prime_thirtyThreeAE_1550051 : Nat.Prime 1550051 := by norm_num
private theorem prime_thirtyThreeAE_362367822679 : Nat.Prime 362367822679 := by
  apply lucas_primality 362367822679 (3 : ZMod 362367822679)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (47, 1), (829, 1), (1550051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (47, 1), (829, 1), (1550051, 1)] : List FactorBlock).map factorBlockValue).prod = 362367822679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_829
      · exact prime_thirtyThreeAE_1550051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 362367822679) ^ 181183911339 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 362367822679) ^ 120789274226 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 362367822679) ^ 7709953674 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 362367822679) ^ 437114382 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 362367822679) ^ 233778 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_163 : Nat.Prime 163 := by norm_num
private theorem prime_thirtyThreeAE_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_thirtyThreeAE_18217 : Nat.Prime 18217 := by norm_num
private theorem prime_thirtyThreeAE_12721 : Nat.Prime 12721 := by norm_num
private theorem prime_thirtyThreeAE_7088013991 : Nat.Prime 7088013991 := by
  apply lucas_primality 7088013991 (11 : ZMod 7088013991)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (41, 1), (151, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (41, 1), (151, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod = 7088013991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_151
      · exact prime_thirtyThreeAE_12721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7088013991) ^ 3544006995 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 2362671330 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 1417602798 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 172878390 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 46940490 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 7088013991) ^ 557190 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_974357259695558663 : Nat.Prime 974357259695558663 := by
  apply lucas_primality 974357259695558663 (5 : ZMod 974357259695558663)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 3), (11, 1), (18217, 1), (7088013991, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 3), (11, 1), (18217, 1), (7088013991, 1)] : List FactorBlock).map factorBlockValue).prod = 974357259695558663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_18217
      · exact prime_thirtyThreeAE_7088013991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 974357259695558663) ^ 487178629847779331 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 139193894242222666 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 88577932699596242 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 53486153576086 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 974357259695558663) ^ 137465482 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_5698920124947872455138027 : Nat.Prime 5698920124947872455138027 := by
  apply lucas_primality 5698920124947872455138027 (2 : ZMod 5698920124947872455138027)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (89, 1), (1217, 1), (974357259695558663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (89, 1), (1217, 1), (974357259695558663, 1)] : List FactorBlock).map factorBlockValue).prod = 5698920124947872455138027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_89
      · exact prime_thirtyThreeAE_1217
      · exact prime_thirtyThreeAE_974357259695558663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5698920124947872455138027) ^ 2849460062473936227569013 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 1899640041649290818379342 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 64032810392672724215034 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 4682760990096854934378 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5698920124947872455138027) ^ 5848902 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_976457 : Nat.Prime 976457 := by norm_num
private theorem prime_thirtyThreeAE_16401349 : Nat.Prime 16401349 := by norm_num
private theorem prime_thirtyThreeAE_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_thirtyThreeAE_2356381 : Nat.Prime 2356381 := by norm_num
private theorem prime_thirtyThreeAE_56653704915557 : Nat.Prime 56653704915557 := by
  apply lucas_primality 56653704915557 (3 : ZMod 56653704915557)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (19, 1), (43, 1), (1051, 1), (2356381, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (19, 1), (43, 1), (1051, 1), (2356381, 1)] : List FactorBlock).map factorBlockValue).prod = 56653704915557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_1051
      · exact prime_thirtyThreeAE_2356381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56653704915557) ^ 28326852457778 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 56653704915557) ^ 8093386416508 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 56653704915557) ^ 2981773942924 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 56653704915557) ^ 1317528021292 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 56653704915557) ^ 53904571756 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 56653704915557) ^ 24042676 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_769 : Nat.Prime 769 := by norm_num
private theorem prime_thirtyThreeAE_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_thirtyThreeAE_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_thirtyThreeAE_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_thirtyThreeAE_223 : Nat.Prime 223 := by norm_num
private theorem prime_thirtyThreeAE_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_thirtyThreeAE_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_89
      · exact prime_thirtyThreeAE_223
      · exact prime_thirtyThreeAE_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_4493 : Nat.Prime 4493 := by norm_num
private theorem prime_thirtyThreeAE_31159 : Nat.Prime 31159 := by norm_num
private theorem prime_thirtyThreeAE_222419 : Nat.Prime 222419 := by norm_num
private theorem prime_thirtyThreeAE_940573 : Nat.Prime 940573 := by norm_num
private theorem prime_thirtyThreeAE_281 : Nat.Prime 281 := by norm_num
private theorem prime_thirtyThreeAE_8779 : Nat.Prime 8779 := by norm_num
private theorem prime_thirtyThreeAE_29602789 : Nat.Prime 29602789 := by
  apply lucas_primality 29602789 (6 : ZMod 29602789)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (281, 1), (8779, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (281, 1), (8779, 1)] : List FactorBlock).map factorBlockValue).prod = 29602789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_281
      · exact prime_thirtyThreeAE_8779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 29602789) ^ 14801394 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 29602789) ^ 9867596 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 29602789) ^ 105348 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 29602789) ^ 3372 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_647 : Nat.Prime 647 := by norm_num
private theorem prime_thirtyThreeAE_4253 : Nat.Prime 4253 := by norm_num
private theorem prime_thirtyThreeAE_397 : Nat.Prime 397 := by norm_num
private theorem prime_thirtyThreeAE_12731599 : Nat.Prime 12731599 := by norm_num
private theorem prime_thirtyThreeAE_409561662387091 : Nat.Prime 409561662387091 := by
  apply lucas_primality 409561662387091 (3 : ZMod 409561662387091)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (37, 1), (73, 1), (397, 1), (12731599, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (37, 1), (73, 1), (397, 1), (12731599, 1)] : List FactorBlock).map factorBlockValue).prod = 409561662387091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_73
      · exact prime_thirtyThreeAE_397
      · exact prime_thirtyThreeAE_12731599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 409561662387091) ^ 204780831193545 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 409561662387091) ^ 136520554129030 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 409561662387091) ^ 81912332477418 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 409561662387091) ^ 11069234118570 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 409561662387091) ^ 5610433731330 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 409561662387091) ^ 1031641466970 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 409561662387091) ^ 32168910 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2457369974322547 : Nat.Prime 2457369974322547 := by
  apply lucas_primality 2457369974322547 (2 : ZMod 2457369974322547)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (409561662387091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (409561662387091, 1)] : List FactorBlock).map factorBlockValue).prod = 2457369974322547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_409561662387091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2457369974322547) ^ 1228684987161273 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2457369974322547) ^ 819123324774182 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2457369974322547) ^ 6 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_308227915879277070211 : Nat.Prime 308227915879277070211 := by
  apply lucas_primality 308227915879277070211 (13 : ZMod 308227915879277070211)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (37, 1), (113, 1), (2457369974322547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (37, 1), (113, 1), (2457369974322547, 1)] : List FactorBlock).map factorBlockValue).prod = 308227915879277070211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_113
      · exact prime_thirtyThreeAE_2457369974322547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 308227915879277070211) ^ 154113957939638535105 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 308227915879277070211) ^ 102742638626425690070 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 308227915879277070211) ^ 61645583175855414042 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 308227915879277070211) ^ 8330484212953434330 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 308227915879277070211) ^ 2727680671498027170 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 308227915879277070211) ^ 125430 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_thirtyThreeAE_15121 : Nat.Prime 15121 := by norm_num
private theorem prime_thirtyThreeAE_2670539 : Nat.Prime 2670539 := by norm_num
private theorem prime_thirtyThreeAE_528426641 : Nat.Prime 528426641 := by
  apply lucas_primality 528426641 (3 : ZMod 528426641)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (7, 1), (17, 1), (47, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (7, 1), (17, 1), (47, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod = 528426641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_1181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 528426641) ^ 264213320 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 528426641) ^ 105685328 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 528426641) ^ 75489520 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 528426641) ^ 31083920 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 528426641) ^ 11243120 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 528426641) ^ 447440 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_6341119693 : Nat.Prime 6341119693 := by
  apply lucas_primality 6341119693 (6 : ZMod 6341119693)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (528426641, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (528426641, 1)] : List FactorBlock).map factorBlockValue).prod = 6341119693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_528426641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 6341119693) ^ 3170559846 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 6341119693) ^ 2113706564 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 6341119693) ^ 12 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_460911871364527210980601 : Nat.Prime 460911871364527210980601 := by
  apply lucas_primality 460911871364527210980601 (13 : ZMod 460911871364527210980601)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 2), (15121, 1), (2670539, 1), (6341119693, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 2), (15121, 1), (2670539, 1), (6341119693, 1)] : List FactorBlock).map factorBlockValue).prod = 460911871364527210980601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_15121
      · exact prime_thirtyThreeAE_2670539
      · exact prime_thirtyThreeAE_6341119693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 460911871364527210980601) ^ 230455935682263605490300 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 460911871364527210980601) ^ 153637290454842403660200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 460911871364527210980601) ^ 92182374272905442196120 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 460911871364527210980601) ^ 30481573398884148600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 460911871364527210980601) ^ 172591327580135400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 460911871364527210980601) ^ 72686196394200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_181 : Nat.Prime 181 := by norm_num
private theorem prime_thirtyThreeAE_1899647 : Nat.Prime 1899647 := by norm_num
private theorem prime_thirtyThreeAE_191 : Nat.Prime 191 := by norm_num
private theorem prime_thirtyThreeAE_11540831 : Nat.Prime 11540831 := by norm_num
private theorem prime_thirtyThreeAE_2909674311721 : Nat.Prime 2909674311721 := by
  apply lucas_primality 2909674311721 (13 : ZMod 2909674311721)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (11540831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (11540831, 1)] : List FactorBlock).map factorBlockValue).prod = 2909674311721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_191
      · exact prime_thirtyThreeAE_11540831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2909674311721) ^ 1454837155860 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 969891437240 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 581934862344 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 264515846520 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 15233896920 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2909674311721) ^ 252120 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_67024695540586320517363 : Nat.Prime 67024695540586320517363 := by
  apply lucas_primality 67024695540586320517363 (3 : ZMod 67024695540586320517363)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (43, 1), (47, 1), (1899647, 1), (2909674311721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (43, 1), (47, 1), (1899647, 1), (2909674311721, 1)] : List FactorBlock).map factorBlockValue).prod = 67024695540586320517363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_1899647
      · exact prime_thirtyThreeAE_2909674311721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67024695540586320517363) ^ 33512347770293160258681 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 22341565180195440172454 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 1558713849781077221334 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 1426057351927368521646 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 35282710703928846 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 67024695540586320517363) ^ 23035119522 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2924413 : Nat.Prime 2924413 := by norm_num
private theorem prime_thirtyThreeAE_312029 : Nat.Prime 312029 := by norm_num
private theorem prime_thirtyThreeAE_1132597 : Nat.Prime 1132597 := by norm_num
private theorem prime_thirtyThreeAE_41906540702335541 : Nat.Prime 41906540702335541 := by
  apply lucas_primality 41906540702335541 (13 : ZMod 41906540702335541)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 2), (11, 2), (312029, 1), (1132597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 2), (11, 2), (312029, 1), (1132597, 1)] : List FactorBlock).map factorBlockValue).prod = 41906540702335541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_312029
      · exact prime_thirtyThreeAE_1132597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 41906540702335541) ^ 20953270351167770 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 41906540702335541) ^ 8381308140467108 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 41906540702335541) ^ 5986648671762220 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 41906540702335541) ^ 3809685518394140 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 41906540702335541) ^ 134303352260 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 41906540702335541) ^ 37000398820 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2210353 : Nat.Prime 2210353 := by norm_num
private theorem prime_thirtyThreeAE_541 : Nat.Prime 541 := by norm_num
private theorem prime_thirtyThreeAE_26632349 : Nat.Prime 26632349 := by
  apply lucas_primality 26632349 (2 : ZMod 26632349)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (397, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (397, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod = 26632349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_397
      · exact prime_thirtyThreeAE_541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26632349) ^ 13316174 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26632349) ^ 859108 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26632349) ^ 67084 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26632349) ^ 49228 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_4951 : Nat.Prime 4951 := by norm_num
private theorem prime_thirtyThreeAE_57184051 : Nat.Prime 57184051 := by
  apply lucas_primality 57184051 (3 : ZMod 57184051)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (7, 1), (11, 1), (4951, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (7, 1), (11, 1), (4951, 1)] : List FactorBlock).map factorBlockValue).prod = 57184051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_4951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 57184051) ^ 28592025 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 57184051) ^ 19061350 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 57184051) ^ 11436810 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 57184051) ^ 8169150 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 57184051) ^ 5198550 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 57184051) ^ 11550 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_34882271111 : Nat.Prime 34882271111 := by
  apply lucas_primality 34882271111 (7 : ZMod 34882271111)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (61, 1), (57184051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (61, 1), (57184051, 1)] : List FactorBlock).map factorBlockValue).prod = 34882271111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_61
      · exact prime_thirtyThreeAE_57184051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 34882271111) ^ 17441135555 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 34882271111) ^ 6976454222 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 34882271111) ^ 571840510 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 34882271111) ^ 610 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_13255263022181 : Nat.Prime 13255263022181 := by
  apply lucas_primality 13255263022181 (2 : ZMod 13255263022181)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (19, 1), (34882271111, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (19, 1), (34882271111, 1)] : List FactorBlock).map factorBlockValue).prod = 13255263022181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_34882271111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13255263022181) ^ 6627631511090 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13255263022181) ^ 2651052604436 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13255263022181) ^ 697645422220 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13255263022181) ^ 380 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_3707213 : Nat.Prime 3707213 := by norm_num
private theorem prime_thirtyThreeAE_74144261 : Nat.Prime 74144261 := by
  apply lucas_primality 74144261 (2 : ZMod 74144261)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (3707213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (3707213, 1)] : List FactorBlock).map factorBlockValue).prod = 74144261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_3707213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 74144261) ^ 37072130 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 74144261) ^ 14828852 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 74144261) ^ 20 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_889731133 : Nat.Prime 889731133 := by
  apply lucas_primality 889731133 (2 : ZMod 889731133)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (74144261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (74144261, 1)] : List FactorBlock).map factorBlockValue).prod = 889731133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_74144261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 889731133) ^ 444865566 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 889731133) ^ 296577044 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 889731133) ^ 12 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1231171 : Nat.Prime 1231171 := by norm_num
private theorem prime_thirtyThreeAE_2871090773 : Nat.Prime 2871090773 := by
  apply lucas_primality 2871090773 (2 : ZMod 2871090773)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (53, 1), (1231171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (53, 1), (1231171, 1)] : List FactorBlock).map factorBlockValue).prod = 2871090773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_1231171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2871090773) ^ 1435545386 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 261008252 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 54171524 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871090773) ^ 2332 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_56020723162777 : Nat.Prime 56020723162777 := by
  apply lucas_primality 56020723162777 (5 : ZMod 56020723162777)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (271, 1), (2871090773, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (271, 1), (2871090773, 1)] : List FactorBlock).map factorBlockValue).prod = 56020723162777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_271
      · exact prime_thirtyThreeAE_2871090773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 56020723162777) ^ 28010361581388 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 18673574387592 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 206718535656 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 56020723162777) ^ 19512 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_859806059102301397 : Nat.Prime 859806059102301397 := by
  apply lucas_primality 859806059102301397 (2 : ZMod 859806059102301397)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1279, 1), (56020723162777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1279, 1), (56020723162777, 1)] : List FactorBlock).map factorBlockValue).prod = 859806059102301397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_1279
      · exact prime_thirtyThreeAE_56020723162777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 859806059102301397) ^ 429903029551150698 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 286602019700767132 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 672248677953324 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 859806059102301397) ^ 15348 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_750284753372944900536056401 : Nat.Prime 750284753372944900536056401 := by
  apply lucas_primality 750284753372944900536056401 (73 : ZMod 750284753372944900536056401)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 4), (5, 2), (7, 2), (11, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 4), (5, 2), (7, 2), (11, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 750284753372944900536056401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_59
      · exact prime_thirtyThreeAE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 750284753372944900536056401) ^ 375142376686472450268028200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 250094917790981633512018800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 150056950674588980107211280 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 107183536196134985790865200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 68207704852085900048732400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 44134397257232052972709200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 39488671230154994765055600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 32621076233606300023306800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 25871888047342927604691600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 24202733979772416146324400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 20277966307376889203677200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 18299628131047436598440400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 17448482636580113965954800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 15963505390913721288001200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 14156316101376318878038800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 12716690735134659331119600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (73 : ZMod 750284753372944900536056401) ^ 12299750055294178697312400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_9091 : Nat.Prime 9091 := by norm_num
private theorem prime_thirtyThreeAE_19181 : Nat.Prime 19181 := by norm_num
private theorem prime_thirtyThreeAE_25981 : Nat.Prime 25981 := by norm_num
private theorem prime_thirtyThreeAE_35334161 : Nat.Prime 35334161 := by
  apply lucas_primality 35334161 (3 : ZMod 35334161)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (17, 1), (25981, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (17, 1), (25981, 1)] : List FactorBlock).map factorBlockValue).prod = 35334161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_25981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35334161) ^ 17667080 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 35334161) ^ 7066832 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 35334161) ^ 2078480 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 35334161) ^ 1360 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1464530305129 : Nat.Prime 1464530305129 := by
  apply lucas_primality 1464530305129 (14 : ZMod 1464530305129)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (157, 1), (35334161, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (157, 1), (35334161, 1)] : List FactorBlock).map factorBlockValue).prod = 1464530305129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_157
      · exact prime_thirtyThreeAE_35334161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1464530305129) ^ 732265152564 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (14 : ZMod 1464530305129) ^ 488176768376 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (14 : ZMod 1464530305129) ^ 133139118648 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (14 : ZMod 1464530305129) ^ 9328218504 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (14 : ZMod 1464530305129) ^ 41448 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_5730595779666587197 : Nat.Prime 5730595779666587197 := by
  apply lucas_primality 5730595779666587197 (14 : ZMod 5730595779666587197)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (19181, 1), (1464530305129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (19181, 1), (1464530305129, 1)] : List FactorBlock).map factorBlockValue).prod = 5730595779666587197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_19181
      · exact prime_thirtyThreeAE_1464530305129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 5730595779666587197) ^ 2865297889833293598 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (14 : ZMod 5730595779666587197) ^ 1910198593222195732 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (14 : ZMod 5730595779666587197) ^ 337093869392152188 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (14 : ZMod 5730595779666587197) ^ 298764182246316 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (14 : ZMod 5730595779666587197) ^ 3912924 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_80973318366688877093611 : Nat.Prime 80973318366688877093611 := by
  apply lucas_primality 80973318366688877093611 (2 : ZMod 80973318366688877093611)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (157, 1), (5730595779666587197, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (157, 1), (5730595779666587197, 1)] : List FactorBlock).map factorBlockValue).prod = 80973318366688877093611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_157
      · exact prime_thirtyThreeAE_5730595779666587197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 80973318366688877093611) ^ 40486659183344438546805 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 80973318366688877093611) ^ 26991106122229625697870 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 80973318366688877093611) ^ 16194663673337775418722 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 80973318366688877093611) ^ 515753620169992847730 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 80973318366688877093611) ^ 14130 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_67901 : Nat.Prime 67901 := by norm_num
private theorem prime_thirtyThreeAE_9392503 : Nat.Prime 9392503 := by norm_num
private theorem prime_thirtyThreeAE_5225593 : Nat.Prime 5225593 := by norm_num
private theorem prime_thirtyThreeAE_11339536811 : Nat.Prime 11339536811 := by
  apply lucas_primality 11339536811 (6 : ZMod 11339536811)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (31, 1), (5225593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (31, 1), (5225593, 1)] : List FactorBlock).map factorBlockValue).prod = 11339536811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_5225593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11339536811) ^ 5669768405 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 2267907362 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 1619933830 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 365791510 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11339536811) ^ 2170 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_362865177953 : Nat.Prime 362865177953 := by
  apply lucas_primality 362865177953 (3 : ZMod 362865177953)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (11339536811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (11339536811, 1)] : List FactorBlock).map factorBlockValue).prod = 362865177953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_11339536811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 362865177953) ^ 181432588976 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 362865177953) ^ 32 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1132865085569267 : Nat.Prime 1132865085569267 := by
  apply lucas_primality 1132865085569267 (2 : ZMod 1132865085569267)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (223, 1), (362865177953, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (223, 1), (362865177953, 1)] : List FactorBlock).map factorBlockValue).prod = 1132865085569267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_223
      · exact prime_thirtyThreeAE_362865177953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1132865085569267) ^ 566432542784633 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 161837869367038 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 5080112491342 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132865085569267) ^ 3122 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_739 : Nat.Prime 739 := by norm_num
private theorem prime_thirtyThreeAE_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_thirtyThreeAE_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_thirtyThreeAE_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2593 : Nat.Prime 2593 := by norm_num
private theorem prime_thirtyThreeAE_10098437 : Nat.Prime 10098437 := by norm_num
private theorem prime_thirtyThreeAE_229 : Nat.Prime 229 := by norm_num
private theorem prime_thirtyThreeAE_588773 : Nat.Prime 588773 := by norm_num
private theorem prime_thirtyThreeAE_315582329 : Nat.Prime 315582329 := by
  apply lucas_primality 315582329 (3 : ZMod 315582329)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (67, 1), (588773, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (67, 1), (588773, 1)] : List FactorBlock).map factorBlockValue).prod = 315582329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_67
      · exact prime_thirtyThreeAE_588773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 315582329) ^ 157791164 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 315582329) ^ 4710184 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 315582329) ^ 536 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_111716144467 : Nat.Prime 111716144467 := by
  apply lucas_primality 111716144467 (2 : ZMod 111716144467)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (59, 1), (315582329, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (59, 1), (315582329, 1)] : List FactorBlock).map factorBlockValue).prod = 111716144467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_59
      · exact prime_thirtyThreeAE_315582329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 111716144467) ^ 55858072233 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 111716144467) ^ 37238714822 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 111716144467) ^ 1893493974 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 111716144467) ^ 354 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_446864577869 : Nat.Prime 446864577869 := by
  apply lucas_primality 446864577869 (2 : ZMod 446864577869)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (111716144467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (111716144467, 1)] : List FactorBlock).map factorBlockValue).prod = 446864577869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_111716144467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 446864577869) ^ 223432288934 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 446864577869) ^ 4 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_26606316966320261 : Nat.Prime 26606316966320261 := by
  apply lucas_primality 26606316966320261 (3 : ZMod 26606316966320261)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (13, 1), (229, 1), (446864577869, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (13, 1), (229, 1), (446864577869, 1)] : List FactorBlock).map factorBlockValue).prod = 26606316966320261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_229
      · exact prime_thirtyThreeAE_446864577869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26606316966320261) ^ 13303158483160130 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 26606316966320261) ^ 5321263393264052 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 26606316966320261) ^ 2046639766640020 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 26606316966320261) ^ 116184790245940 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 26606316966320261) ^ 59540 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_241 : Nat.Prime 241 := by norm_num
private theorem prime_thirtyThreeAE_641 : Nat.Prime 641 := by norm_num
private theorem prime_thirtyThreeAE_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_thirtyThreeAE_80744533 : Nat.Prime 80744533 := by
  apply lucas_primality 80744533 (6 : ZMod 80744533)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (151, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (151, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod = 80744533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_151
      · exact prime_thirtyThreeAE_4051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 80744533) ^ 40372266 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 26914844 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 7340412 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 534732 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 80744533) ^ 19932 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_thirtyThreeAE_198251 : Nat.Prime 198251 := by norm_num
private theorem prime_thirtyThreeAE_5118840821 : Nat.Prime 5118840821 := by
  apply lucas_primality 5118840821 (2 : ZMod 5118840821)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (1291, 1), (198251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (1291, 1), (198251, 1)] : List FactorBlock).map factorBlockValue).prod = 5118840821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_1291
      · exact prime_thirtyThreeAE_198251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5118840821) ^ 2559420410 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 1023768164 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 3965020 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118840821) ^ 25820 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_826636823185963187 : Nat.Prime 826636823185963187 := by
  apply lucas_primality 826636823185963187 (2 : ZMod 826636823185963187)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (80744533, 1), (5118840821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (80744533, 1), (5118840821, 1)] : List FactorBlock).map factorBlockValue).prod = 826636823185963187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_80744533
      · exact prime_thirtyThreeAE_5118840821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 826636823185963187) ^ 413318411592981593 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 826636823185963187) ^ 10237681642 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 826636823185963187) ^ 161489066 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_4430773372276762682321 : Nat.Prime 4430773372276762682321 := by
  apply lucas_primality 4430773372276762682321 (3 : ZMod 4430773372276762682321)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (67, 1), (826636823185963187, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (67, 1), (826636823185963187, 1)] : List FactorBlock).map factorBlockValue).prod = 4430773372276762682321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_67
      · exact prime_thirtyThreeAE_826636823185963187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4430773372276762682321) ^ 2215386686138381341160 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 886154674455352536464 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 66130945854877054960 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4430773372276762682321) ^ 5360 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_200371 : Nat.Prime 200371 := by norm_num
private theorem prime_thirtyThreeAE_65089 : Nat.Prime 65089 := by norm_num
private theorem prime_thirtyThreeAE_33195391 : Nat.Prime 33195391 := by
  apply lucas_primality 33195391 (11 : ZMod 33195391)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (17, 1), (65089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (17, 1), (65089, 1)] : List FactorBlock).map factorBlockValue).prod = 33195391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_65089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 33195391) ^ 16597695 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 33195391) ^ 11065130 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 33195391) ^ 6639078 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 33195391) ^ 1952670 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 33195391) ^ 510 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_787 : Nat.Prime 787 := by norm_num
private theorem prime_thirtyThreeAE_491149 : Nat.Prime 491149 := by norm_num
private theorem prime_thirtyThreeAE_291446834303 : Nat.Prime 291446834303 := by
  apply lucas_primality 291446834303 (5 : ZMod 291446834303)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (29, 1), (787, 1), (491149, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (29, 1), (787, 1), (491149, 1)] : List FactorBlock).map factorBlockValue).prod = 291446834303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_787
      · exact prime_thirtyThreeAE_491149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 291446834303) ^ 145723417151 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 291446834303) ^ 22418987254 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 291446834303) ^ 10049890838 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 291446834303) ^ 370326346 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 291446834303) ^ 593398 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_thirtyThreeAE_10627 : Nat.Prime 10627 := by norm_num
private theorem prime_thirtyThreeAE_48395359 : Nat.Prime 48395359 := by
  apply lucas_primality 48395359 (3 : ZMod 48395359)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (23, 1), (10627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (23, 1), (10627, 1)] : List FactorBlock).map factorBlockValue).prod = 48395359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_10627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48395359) ^ 24197679 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 48395359) ^ 16131786 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 48395359) ^ 4399578 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 48395359) ^ 2104146 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 48395359) ^ 4554 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_8663 : Nat.Prime 8663 := by norm_num
private theorem prime_thirtyThreeAE_13291 : Nat.Prime 13291 := by norm_num
private theorem prime_thirtyThreeAE_34721 : Nat.Prime 34721 := by norm_num
private theorem prime_thirtyThreeAE_119933208410791 : Nat.Prime 119933208410791 := by
  apply lucas_primality 119933208410791 (3 : ZMod 119933208410791)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (8663, 1), (13291, 1), (34721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (8663, 1), (13291, 1), (34721, 1)] : List FactorBlock).map factorBlockValue).prod = 119933208410791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_8663
      · exact prime_thirtyThreeAE_13291
      · exact prime_thirtyThreeAE_34721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 119933208410791) ^ 59966604205395 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 119933208410791) ^ 39977736136930 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 119933208410791) ^ 23986641682158 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 119933208410791) ^ 13844304330 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 119933208410791) ^ 9023640690 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 119933208410791) ^ 3454197990 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_269 : Nat.Prime 269 := by norm_num
private theorem prime_thirtyThreeAE_1127981 : Nat.Prime 1127981 := by norm_num
private theorem prime_thirtyThreeAE_19841 : Nat.Prime 19841 := by norm_num
private theorem prime_thirtyThreeAE_74687 : Nat.Prime 74687 := by norm_num
private theorem prime_thirtyThreeAE_279180007 : Nat.Prime 279180007 := by
  apply lucas_primality 279180007 (3 : ZMod 279180007)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (89, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (89, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod = 279180007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_89
      · exact prime_thirtyThreeAE_74687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 279180007) ^ 139590003 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 93060002 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 39882858 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 3136854 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 279180007) ^ 3738 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_110784210377741 : Nat.Prime 110784210377741 := by
  apply lucas_primality 110784210377741 (7 : ZMod 110784210377741)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (19841, 1), (279180007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (19841, 1), (279180007, 1)] : List FactorBlock).map factorBlockValue).prod = 110784210377741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_19841
      · exact prime_thirtyThreeAE_279180007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 110784210377741) ^ 55392105188870 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 22156842075548 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 5583600140 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 110784210377741) ^ 396820 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_89292073564459247 : Nat.Prime 89292073564459247 := by
  apply lucas_primality 89292073564459247 (5 : ZMod 89292073564459247)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (31, 1), (110784210377741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (31, 1), (110784210377741, 1)] : List FactorBlock).map factorBlockValue).prod = 89292073564459247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_110784210377741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 89292073564459247) ^ 44646036782229623 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 6868621043419942 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 2880389469821266 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 89292073564459247) ^ 806 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2143009765547021929 : Nat.Prime 2143009765547021929 := by
  apply lucas_primality 2143009765547021929 (7 : ZMod 2143009765547021929)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (89292073564459247, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (89292073564459247, 1)] : List FactorBlock).map factorBlockValue).prod = 2143009765547021929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_89292073564459247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2143009765547021929) ^ 1071504882773510964 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2143009765547021929) ^ 714336588515673976 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2143009765547021929) ^ 24 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_97 : Nat.Prime 97 := by norm_num
private theorem prime_thirtyThreeAE_456623 : Nat.Prime 456623 := by norm_num
private theorem prime_thirtyThreeAE_25171 : Nat.Prime 25171 := by norm_num
private theorem prime_thirtyThreeAE_864737 : Nat.Prime 864737 := by norm_num
private theorem prime_thirtyThreeAE_8879119517 : Nat.Prime 8879119517 := by
  apply lucas_primality 8879119517 (2 : ZMod 8879119517)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (151, 1), (864737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (151, 1), (864737, 1)] : List FactorBlock).map factorBlockValue).prod = 8879119517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_151
      · exact prime_thirtyThreeAE_864737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8879119517) ^ 4439559758 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8879119517) ^ 522301148 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8879119517) ^ 58802116 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8879119517) ^ 10268 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_14440097064785116271 : Nat.Prime 14440097064785116271 := by
  apply lucas_primality 14440097064785116271 (7 : ZMod 14440097064785116271)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (13, 1), (71, 1), (25171, 1), (8879119517, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (13, 1), (71, 1), (25171, 1), (8879119517, 1)] : List FactorBlock).map factorBlockValue).prod = 14440097064785116271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_71
      · exact prime_thirtyThreeAE_25171
      · exact prime_thirtyThreeAE_8879119517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14440097064785116271) ^ 7220048532392558135 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14440097064785116271) ^ 2888019412957023254 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14440097064785116271) ^ 2062871009255016610 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14440097064785116271) ^ 1110776697291162790 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14440097064785116271) ^ 203381648799790370 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14440097064785116271) ^ 573679911993370 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14440097064785116271) ^ 1626298310 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_629271083474082819804434401 : Nat.Prime 629271083474082819804434401 := by
  apply lucas_primality 629271083474082819804434401 (79 : ZMod 629271083474082819804434401)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 629271083474082819804434401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_59
      · exact prime_thirtyThreeAE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 629271083474082819804434401) ^ 314635541737041409902217200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 209757027824694273268144800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 125854216694816563960886880 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 89895869067726117114919200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 57206462134007529073130400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 48405467959544832292648800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 37015946086710754106143200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 33119530709162253673917600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 27359612324960122600192800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 21699002878416648958773600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 17007326580380616751471200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 15348075206684946824498400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 14634211243583321390800800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 13388746456895379144775200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 11873039310831751317064800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 10665611584306488471261600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (79 : ZMod 629271083474082819804434401) ^ 10315919401214472455810400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_383 : Nat.Prime 383 := by norm_num
private theorem prime_thirtyThreeAE_2848589311 : Nat.Prime 2848589311 := by
  apply lucas_primality 2848589311 (6 : ZMod 2848589311)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (107, 1), (331, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (107, 1), (331, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod = 2848589311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_107
      · exact prime_thirtyThreeAE_331
      · exact prime_thirtyThreeAE_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2848589311) ^ 1424294655 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 949529770 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 569717862 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 406941330 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 26622330 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 8606010 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2848589311) ^ 7437570 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_14681717 : Nat.Prime 14681717 := by norm_num
private theorem prime_thirtyThreeAE_21846394897 : Nat.Prime 21846394897 := by
  apply lucas_primality 21846394897 (5 : ZMod 21846394897)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (31, 1), (14681717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (31, 1), (14681717, 1)] : List FactorBlock).map factorBlockValue).prod = 21846394897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_14681717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21846394897) ^ 10923197448 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 21846394897) ^ 7282131632 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 21846394897) ^ 704722416 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 21846394897) ^ 1488 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_12146595562733 : Nat.Prime 12146595562733 := by
  apply lucas_primality 12146595562733 (2 : ZMod 12146595562733)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (139, 1), (21846394897, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (139, 1), (21846394897, 1)] : List FactorBlock).map factorBlockValue).prod = 12146595562733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_139
      · exact prime_thirtyThreeAE_21846394897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12146595562733) ^ 6073297781366 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12146595562733) ^ 87385579588 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12146595562733) ^ 556 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1384711894151563 : Nat.Prime 1384711894151563 := by
  apply lucas_primality 1384711894151563 (2 : ZMod 1384711894151563)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (12146595562733, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (12146595562733, 1)] : List FactorBlock).map factorBlockValue).prod = 1384711894151563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_12146595562733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1384711894151563) ^ 692355947075781 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384711894151563) ^ 461570631383854 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384711894151563) ^ 72879573376398 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384711894151563) ^ 114 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_thirtyThreeAE_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_thirtyThreeAE_455550499 : Nat.Prime 455550499 := by
  apply lucas_primality 455550499 (15 : ZMod 455550499)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (13, 1), (19, 1), (79, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (13, 1), (19, 1), (79, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod = 455550499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_79
      · exact prime_thirtyThreeAE_1297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 455550499) ^ 227775249 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 455550499) ^ 151850166 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 455550499) ^ 35042346 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 455550499) ^ 23976342 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 455550499) ^ 5766462 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 455550499) ^ 351234 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_141991 : Nat.Prime 141991 := by norm_num
private theorem prime_thirtyThreeAE_321679 : Nat.Prime 321679 := by norm_num
private theorem prime_thirtyThreeAE_413272131099673 : Nat.Prime 413272131099673 := by
  apply lucas_primality 413272131099673 (7 : ZMod 413272131099673)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (13, 1), (29, 1), (141991, 1), (321679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (13, 1), (29, 1), (141991, 1), (321679, 1)] : List FactorBlock).map factorBlockValue).prod = 413272131099673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_141991
      · exact prime_thirtyThreeAE_321679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 413272131099673) ^ 206636065549836 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 413272131099673) ^ 137757377033224 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 413272131099673) ^ 31790163930744 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 413272131099673) ^ 14250763141368 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 413272131099673) ^ 2910551592 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 413272131099673) ^ 1284734568 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1993 : Nat.Prime 1993 := by norm_num
private theorem prime_thirtyThreeAE_28766963 : Nat.Prime 28766963 := by
  apply lucas_primality 28766963 (2 : ZMod 28766963)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (1031, 1), (1993, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (1031, 1), (1993, 1)] : List FactorBlock).map factorBlockValue).prod = 28766963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_1031
      · exact prime_thirtyThreeAE_1993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28766963) ^ 14383481 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28766963) ^ 4109566 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28766963) ^ 27902 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28766963) ^ 14434 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_100799438353 : Nat.Prime 100799438353 := by
  apply lucas_primality 100799438353 (15 : ZMod 100799438353)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (73, 1), (28766963, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (73, 1), (28766963, 1)] : List FactorBlock).map factorBlockValue).prod = 100799438353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_73
      · exact prime_thirtyThreeAE_28766963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 100799438353) ^ 50399719176 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 100799438353) ^ 33599812784 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 100799438353) ^ 1380814224 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 100799438353) ^ 3504 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_11717 : Nat.Prime 11717 := by norm_num
private theorem prime_thirtyThreeAE_273896593 : Nat.Prime 273896593 := by
  apply lucas_primality 273896593 (10 : ZMod 273896593)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (487, 1), (11717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (487, 1), (11717, 1)] : List FactorBlock).map factorBlockValue).prod = 273896593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_487
      · exact prime_thirtyThreeAE_11717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 273896593) ^ 136948296 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 273896593) ^ 91298864 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 273896593) ^ 562416 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 273896593) ^ 23376 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_5954674078603057 : Nat.Prime 5954674078603057 := by
  apply lucas_primality 5954674078603057 (5 : ZMod 5954674078603057)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (673, 2), (273896593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (673, 2), (273896593, 1)] : List FactorBlock).map factorBlockValue).prod = 5954674078603057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_673
      · exact prime_thirtyThreeAE_273896593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5954674078603057) ^ 2977337039301528 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 5954674078603057) ^ 1984891359534352 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 5954674078603057) ^ 8847955540272 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 5954674078603057) ^ 21740592 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_thirtyThreeAE_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_113
      · exact prime_thirtyThreeAE_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_thirtyThreeAE_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_thirtyThreeAE_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_397
      · exact prime_thirtyThreeAE_2531
      · exact prime_thirtyThreeAE_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_69821 : Nat.Prime 69821 := by norm_num
private theorem prime_thirtyThreeAE_38119 : Nat.Prime 38119 := by norm_num
private theorem prime_thirtyThreeAE_131510551 : Nat.Prime 131510551 := by
  apply lucas_primality 131510551 (3 : ZMod 131510551)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (23, 1), (38119, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (23, 1), (38119, 1)] : List FactorBlock).map factorBlockValue).prod = 131510551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_38119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 131510551) ^ 65755275 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 131510551) ^ 43836850 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 131510551) ^ 26302110 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 131510551) ^ 5717850 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 131510551) ^ 3450 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_14076353 : Nat.Prime 14076353 := by norm_num
private theorem prime_thirtyThreeAE_4700178724819 : Nat.Prime 4700178724819 := by
  apply lucas_primality 4700178724819 (2 : ZMod 4700178724819)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (29, 1), (101, 1), (14076353, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (29, 1), (101, 1), (14076353, 1)] : List FactorBlock).map factorBlockValue).prod = 4700178724819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_101
      · exact prime_thirtyThreeAE_14076353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4700178724819) ^ 2350089362409 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4700178724819) ^ 1566726241606 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4700178724819) ^ 247377827622 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4700178724819) ^ 162075128442 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4700178724819) ^ 46536423018 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4700178724819) ^ 333906 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_4248961567236377 : Nat.Prime 4248961567236377 := by
  apply lucas_primality 4248961567236377 (3 : ZMod 4248961567236377)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (113, 1), (4700178724819, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (113, 1), (4700178724819, 1)] : List FactorBlock).map factorBlockValue).prod = 4248961567236377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_113
      · exact prime_thirtyThreeAE_4700178724819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4248961567236377) ^ 2124480783618188 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4248961567236377) ^ 37601429798552 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4248961567236377) ^ 904 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_10061981 : Nat.Prime 10061981 := by norm_num
private theorem prime_thirtyThreeAE_10111 : Nat.Prime 10111 := by norm_num
private theorem prime_thirtyThreeAE_66348383 : Nat.Prime 66348383 := by
  apply lucas_primality 66348383 (10 : ZMod 66348383)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (193, 1), (10111, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (193, 1), (10111, 1)] : List FactorBlock).map factorBlockValue).prod = 66348383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_193
      · exact prime_thirtyThreeAE_10111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 66348383) ^ 33174191 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 66348383) ^ 3902846 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 66348383) ^ 343774 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 66348383) ^ 6562 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_9288773621 : Nat.Prime 9288773621 := by
  apply lucas_primality 9288773621 (2 : ZMod 9288773621)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (66348383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (66348383, 1)] : List FactorBlock).map factorBlockValue).prod = 9288773621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_66348383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9288773621) ^ 4644386810 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9288773621) ^ 1857754724 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9288773621) ^ 1326967660 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9288773621) ^ 140 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1560513968329 : Nat.Prime 1560513968329 := by
  apply lucas_primality 1560513968329 (11 : ZMod 1560513968329)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (9288773621, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (9288773621, 1)] : List FactorBlock).map factorBlockValue).prod = 1560513968329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_9288773621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1560513968329) ^ 780256984164 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1560513968329) ^ 520171322776 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1560513968329) ^ 222930566904 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1560513968329) ^ 168 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_580511196218389 : Nat.Prime 580511196218389 := by
  apply lucas_primality 580511196218389 (6 : ZMod 580511196218389)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (31, 1), (1560513968329, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (31, 1), (1560513968329, 1)] : List FactorBlock).map factorBlockValue).prod = 580511196218389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_1560513968329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 580511196218389) ^ 290255598109194 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 580511196218389) ^ 193503732072796 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 580511196218389) ^ 18726167619948 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 580511196218389) ^ 372 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_532909278128481103 : Nat.Prime 532909278128481103 := by
  apply lucas_primality 532909278128481103 (5 : ZMod 532909278128481103)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (17, 1), (580511196218389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (17, 1), (580511196218389, 1)] : List FactorBlock).map factorBlockValue).prod = 532909278128481103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_580511196218389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 532909278128481103) ^ 266454639064240551 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 532909278128481103) ^ 177636426042827034 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 532909278128481103) ^ 31347604595793006 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 532909278128481103) ^ 918 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_thirtyThreeAE_5927 : Nat.Prime 5927 := by norm_num
private theorem prime_thirtyThreeAE_3769 : Nat.Prime 3769 := by norm_num
private theorem prime_thirtyThreeAE_289278289 : Nat.Prime 289278289 := by
  apply lucas_primality 289278289 (7 : ZMod 289278289)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (13, 1), (41, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (13, 1), (41, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod = 289278289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_3769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 289278289) ^ 144639144 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 96426096 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 22252176 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 7055568 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 289278289) ^ 76752 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_thirtyThreeAE_127435031 : Nat.Prime 127435031 := by
  apply lucas_primality 127435031 (11 : ZMod 127435031)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (37, 1), (163, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (37, 1), (163, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod = 127435031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_163
      · exact prime_thirtyThreeAE_2113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 127435031) ^ 63717515 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 25487006 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 3444190 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 781810 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 127435031) ^ 60310 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_252321361381 : Nat.Prime 252321361381 := by
  apply lucas_primality 252321361381 (2 : ZMod 252321361381)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (11, 1), (127435031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (11, 1), (127435031, 1)] : List FactorBlock).map factorBlockValue).prod = 252321361381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_127435031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 252321361381) ^ 126160680690 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 84107120460 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 50464272276 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 22938305580 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 252321361381) ^ 1980 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1545017 : Nat.Prime 1545017 := by norm_num
private theorem prime_thirtyThreeAE_268832959 : Nat.Prime 268832959 := by
  apply lucas_primality 268832959 (3 : ZMod 268832959)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29, 1), (1545017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29, 1), (1545017, 1)] : List FactorBlock).map factorBlockValue).prod = 268832959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_1545017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 268832959) ^ 134416479 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 268832959) ^ 89610986 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 268832959) ^ 9270102 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 268832959) ^ 174 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_349 : Nat.Prime 349 := by norm_num
private theorem prime_thirtyThreeAE_13249 : Nat.Prime 13249 := by norm_num
private theorem prime_thirtyThreeAE_1775948957 : Nat.Prime 1775948957 := by
  apply lucas_primality 1775948957 (2 : ZMod 1775948957)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (23, 1), (31, 1), (47, 1), (13249, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (23, 1), (31, 1), (47, 1), (13249, 1)] : List FactorBlock).map factorBlockValue).prod = 1775948957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_13249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1775948957) ^ 887974478 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1775948957) ^ 77215172 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1775948957) ^ 57288676 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1775948957) ^ 37786148 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1775948957) ^ 134044 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_10655693743 : Nat.Prime 10655693743 := by
  apply lucas_primality 10655693743 (3 : ZMod 10655693743)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1775948957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1775948957, 1)] : List FactorBlock).map factorBlockValue).prod = 10655693743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_1775948957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10655693743) ^ 5327846871 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10655693743) ^ 3551897914 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10655693743) ^ 6 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_34140842752573 : Nat.Prime 34140842752573 := by
  apply lucas_primality 34140842752573 (11 : ZMod 34140842752573)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (89, 1), (10655693743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (89, 1), (10655693743, 1)] : List FactorBlock).map factorBlockValue).prod = 34140842752573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_89
      · exact prime_thirtyThreeAE_10655693743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 34140842752573) ^ 17070421376286 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 34140842752573) ^ 11380280917524 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 34140842752573) ^ 383604974748 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 34140842752573) ^ 3204 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2073236816992747999 : Nat.Prime 2073236816992747999 := by
  apply lucas_primality 2073236816992747999 (13 : ZMod 2073236816992747999)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29, 1), (349, 1), (34140842752573, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29, 1), (349, 1), (34140842752573, 1)] : List FactorBlock).map factorBlockValue).prod = 2073236816992747999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_349
      · exact prime_thirtyThreeAE_34140842752573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2073236816992747999) ^ 1036618408496373999 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2073236816992747999) ^ 691078938997582666 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2073236816992747999) ^ 71490924723887862 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2073236816992747999) ^ 5940506638947702 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2073236816992747999) ^ 60726 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_5475331 : Nat.Prime 5475331 := by norm_num
private theorem prime_thirtyThreeAE_137 : Nat.Prime 137 := by norm_num
private theorem prime_thirtyThreeAE_149497 : Nat.Prime 149497 := by norm_num
private theorem prime_thirtyThreeAE_40962179 : Nat.Prime 40962179 := by
  apply lucas_primality 40962179 (2 : ZMod 40962179)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (137, 1), (149497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (137, 1), (149497, 1)] : List FactorBlock).map factorBlockValue).prod = 40962179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_137
      · exact prime_thirtyThreeAE_149497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40962179) ^ 20481089 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40962179) ^ 298994 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40962179) ^ 274 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_225299 : Nat.Prime 225299 := by norm_num
private theorem prime_thirtyThreeAE_173954647060879 : Nat.Prime 173954647060879 := by
  apply lucas_primality 173954647060879 (3 : ZMod 173954647060879)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (67, 1), (113, 1), (739, 1), (225299, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (67, 1), (113, 1), (739, 1), (225299, 1)] : List FactorBlock).map factorBlockValue).prod = 173954647060879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_67
      · exact prime_thirtyThreeAE_113
      · exact prime_thirtyThreeAE_739
      · exact prime_thirtyThreeAE_225299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 173954647060879) ^ 86977323530439 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 173954647060879) ^ 57984882353626 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 173954647060879) ^ 7563245524386 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 173954647060879) ^ 2596338015834 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 173954647060879) ^ 1539421655406 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 173954647060879) ^ 235391944602 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 173954647060879) ^ 772105722 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_4885691 : Nat.Prime 4885691 := by norm_num
private theorem prime_thirtyThreeAE_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_thirtyThreeAE_14423 : Nat.Prime 14423 := by norm_num
private theorem prime_thirtyThreeAE_85817 : Nat.Prime 85817 := by norm_num
private theorem prime_thirtyThreeAE_22140787 : Nat.Prime 22140787 := by
  apply lucas_primality 22140787 (2 : ZMod 22140787)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (43, 1), (85817, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (43, 1), (85817, 1)] : List FactorBlock).map factorBlockValue).prod = 22140787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_85817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22140787) ^ 11070393 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22140787) ^ 7380262 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22140787) ^ 514902 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22140787) ^ 258 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_140392491357773839 : Nat.Prime 140392491357773839 := by
  apply lucas_primality 140392491357773839 (6 : ZMod 140392491357773839)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (47, 1), (1559, 1), (14423, 1), (22140787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (47, 1), (1559, 1), (14423, 1), (22140787, 1)] : List FactorBlock).map factorBlockValue).prod = 140392491357773839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_1559
      · exact prime_thirtyThreeAE_14423
      · exact prime_thirtyThreeAE_22140787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 140392491357773839) ^ 70196245678886919 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 46797497119257946 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 2987074284207954 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 90052912994082 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 9733931315106 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 140392491357773839) ^ 6340898874 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_110910068172641332811 : Nat.Prime 110910068172641332811 := by
  apply lucas_primality 110910068172641332811 (2 : ZMod 110910068172641332811)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (79, 1), (140392491357773839, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (79, 1), (140392491357773839, 1)] : List FactorBlock).map factorBlockValue).prod = 110910068172641332811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_79
      · exact prime_thirtyThreeAE_140392491357773839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 110910068172641332811) ^ 55455034086320666405 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 110910068172641332811) ^ 22182013634528266562 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 110910068172641332811) ^ 1403924913577738390 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 110910068172641332811) ^ 790 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_251 : Nat.Prime 251 := by norm_num
private theorem prime_thirtyThreeAE_4550971 : Nat.Prime 4550971 := by norm_num
private theorem prime_thirtyThreeAE_109660197217 : Nat.Prime 109660197217 := by
  apply lucas_primality 109660197217 (5 : ZMod 109660197217)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (251, 1), (4550971, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (251, 1), (4550971, 1)] : List FactorBlock).map factorBlockValue).prod = 109660197217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_251
      · exact prime_thirtyThreeAE_4550971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 109660197217) ^ 54830098608 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 109660197217) ^ 36553399072 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 109660197217) ^ 436893216 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 109660197217) ^ 24096 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_523 : Nat.Prime 523 := by norm_num
private theorem prime_thirtyThreeAE_953 : Nat.Prime 953 := by norm_num
private theorem prime_thirtyThreeAE_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_thirtyThreeAE_143113 : Nat.Prime 143113 := by norm_num
private theorem prime_thirtyThreeAE_1862717844193559 : Nat.Prime 1862717844193559 := by
  apply lucas_primality 1862717844193559 (11 : ZMod 1862717844193559)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (523, 1), (953, 1), (1187, 1), (143113, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (523, 1), (953, 1), (1187, 1), (143113, 1)] : List FactorBlock).map factorBlockValue).prod = 1862717844193559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_523
      · exact prime_thirtyThreeAE_953
      · exact prime_thirtyThreeAE_1187
      · exact prime_thirtyThreeAE_143113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1862717844193559) ^ 931358922096779 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1862717844193559) ^ 169337985835778 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1862717844193559) ^ 3561601996546 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1862717844193559) ^ 1954583257286 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1862717844193559) ^ 1569265243634 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1862717844193559) ^ 13015713766 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_527227123991799119295607201 : Nat.Prime 527227123991799119295607201 := by
  apply lucas_primality 527227123991799119295607201 (71 : ZMod 527227123991799119295607201)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 527227123991799119295607201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_59
      · exact prime_thirtyThreeAE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 527227123991799119295607201) ^ 263613561995899559647803600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 175742374663933039765202400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 105445424798359823859121440 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 75318160570257017042229600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 47929738544709010845055200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 40555932614753778407354400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 31013360234811712899741600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 27748795999568374699768800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 22922918434426048665026400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 18180245654889624803296800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 17007326580380616751471200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 12859198146141441934039200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 12261095906786026030130400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 11217598382804236580757600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 9947681584750926779162400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 8936052949013544394840800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (71 : ZMod 527227123991799119295607201) ^ 8643067606422936381895200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2719511 : Nat.Prime 2719511 := by norm_num
private theorem prime_thirtyThreeAE_277 : Nat.Prime 277 := by norm_num
private theorem prime_thirtyThreeAE_251922637 : Nat.Prime 251922637 := by
  apply lucas_primality 251922637 (2 : ZMod 251922637)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 4), (7, 1), (277, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 4), (7, 1), (277, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod = 251922637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_277
      · exact prime_thirtyThreeAE_401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 251922637) ^ 125961318 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 83974212 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 35988948 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 909468 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 251922637) ^ 628236 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_3793 : Nat.Prime 3793 := by norm_num
private theorem prime_thirtyThreeAE_6672769 : Nat.Prime 6672769 := by norm_num
private theorem prime_thirtyThreeAE_151858876903 : Nat.Prime 151858876903 := by
  apply lucas_primality 151858876903 (3 : ZMod 151858876903)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3793, 1), (6672769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3793, 1), (6672769, 1)] : List FactorBlock).map factorBlockValue).prod = 151858876903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_3793
      · exact prime_thirtyThreeAE_6672769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 151858876903) ^ 75929438451 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 151858876903) ^ 50619625634 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 151858876903) ^ 40036614 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 151858876903) ^ 22758 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_thirtyThreeAE_5215229 : Nat.Prime 5215229 := by norm_num
private theorem prime_thirtyThreeAE_41721833 : Nat.Prime 41721833 := by
  apply lucas_primality 41721833 (3 : ZMod 41721833)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5215229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5215229, 1)] : List FactorBlock).map factorBlockValue).prod = 41721833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5215229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 41721833) ^ 20860916 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 41721833) ^ 8 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_584105663 : Nat.Prime 584105663 := by
  apply lucas_primality 584105663 (5 : ZMod 584105663)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (41721833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (41721833, 1)] : List FactorBlock).map factorBlockValue).prod = 584105663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_41721833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 584105663) ^ 292052831 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 584105663) ^ 83443666 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 584105663) ^ 14 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2328653 : Nat.Prime 2328653 := by norm_num
private theorem prime_thirtyThreeAE_55887673 : Nat.Prime 55887673 := by
  apply lucas_primality 55887673 (17 : ZMod 55887673)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (2328653, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (2328653, 1)] : List FactorBlock).map factorBlockValue).prod = 55887673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_2328653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 55887673) ^ 27943836 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (17 : ZMod 55887673) ^ 18629224 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (17 : ZMod 55887673) ^ 24 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_223550693 : Nat.Prime 223550693 := by
  apply lucas_primality 223550693 (2 : ZMod 223550693)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (55887673, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (55887673, 1)] : List FactorBlock).map factorBlockValue).prod = 223550693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_55887673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 223550693) ^ 111775346 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 223550693) ^ 4 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_192253595981 : Nat.Prime 192253595981 := by
  apply lucas_primality 192253595981 (7 : ZMod 192253595981)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (43, 1), (223550693, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (43, 1), (223550693, 1)] : List FactorBlock).map factorBlockValue).prod = 192253595981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_223550693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 192253595981) ^ 96126797990 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 192253595981) ^ 38450719196 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 192253595981) ^ 4471013860 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 192253595981) ^ 860 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_144574704177713 : Nat.Prime 144574704177713 := by
  apply lucas_primality 144574704177713 (3 : ZMod 144574704177713)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (47, 1), (192253595981, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (47, 1), (192253595981, 1)] : List FactorBlock).map factorBlockValue).prod = 144574704177713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_192253595981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 144574704177713) ^ 72287352088856 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 144574704177713) ^ 3076057535696 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 144574704177713) ^ 752 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_thirtyThreeAE_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_thirtyThreeAE_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_thirtyThreeAE_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_173
      · exact prime_thirtyThreeAE_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_4159
      · exact prime_thirtyThreeAE_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_12227 : Nat.Prime 12227 := by norm_num
private theorem prime_thirtyThreeAE_43891 : Nat.Prime 43891 := by norm_num
private theorem prime_thirtyThreeAE_40627 : Nat.Prime 40627 := by norm_num
private theorem prime_thirtyThreeAE_60353 : Nat.Prime 60353 := by norm_num
private theorem prime_thirtyThreeAE_2867706713387 : Nat.Prime 2867706713387 := by
  apply lucas_primality 2867706713387 (2 : ZMod 2867706713387)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (631, 1), (1637, 1), (60353, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (631, 1), (1637, 1), (60353, 1)] : List FactorBlock).map factorBlockValue).prod = 2867706713387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_631
      · exact prime_thirtyThreeAE_1637
      · exact prime_thirtyThreeAE_60353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2867706713387) ^ 1433853356693 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2867706713387) ^ 124682900582 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2867706713387) ^ 4544701606 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2867706713387) ^ 1751806178 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2867706713387) ^ 47515562 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_932050565158189193 : Nat.Prime 932050565158189193 := by
  apply lucas_primality 932050565158189193 (3 : ZMod 932050565158189193)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (40627, 1), (2867706713387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (40627, 1), (2867706713387, 1)] : List FactorBlock).map factorBlockValue).prod = 932050565158189193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_40627
      · exact prime_thirtyThreeAE_2867706713387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 932050565158189193) ^ 466025282579094596 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 932050565158189193) ^ 22941653707096 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 932050565158189193) ^ 325016 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_12511 : Nat.Prime 12511 := by norm_num
private theorem prime_thirtyThreeAE_6166751 : Nat.Prime 6166751 := by norm_num
private theorem prime_thirtyThreeAE_5439074383 : Nat.Prime 5439074383 := by
  apply lucas_primality 5439074383 (3 : ZMod 5439074383)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 2), (6166751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 2), (6166751, 1)] : List FactorBlock).map factorBlockValue).prod = 5439074383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_6166751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5439074383) ^ 2719537191 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5439074383) ^ 1813024794 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5439074383) ^ 777010626 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5439074383) ^ 882 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_thirtyThreeAE_4021 : Nat.Prime 4021 := by norm_num
private theorem prime_thirtyThreeAE_1240996243961 : Nat.Prime 1240996243961 := by
  apply lucas_primality 1240996243961 (6 : ZMod 1240996243961)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (599, 1), (1171, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (599, 1), (1171, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod = 1240996243961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_599
      · exact prime_thirtyThreeAE_1171
      · exact prime_thirtyThreeAE_4021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1240996243961) ^ 620498121980 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1240996243961) ^ 248199248792 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1240996243961) ^ 112817840360 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1240996243961) ^ 2071780040 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1240996243961) ^ 1059774760 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1240996243961) ^ 308628760 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_573340264709983 : Nat.Prime 573340264709983 := by
  apply lucas_primality 573340264709983 (7 : ZMod 573340264709983)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 1), (1240996243961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 1), (1240996243961, 1)] : List FactorBlock).map factorBlockValue).prod = 573340264709983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_1240996243961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 573340264709983) ^ 286670132354991 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 573340264709983) ^ 191113421569994 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 573340264709983) ^ 81905752101426 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 573340264709983) ^ 52121842246362 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 573340264709983) ^ 462 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_409967 : Nat.Prime 409967 := by norm_num
private theorem prime_thirtyThreeAE_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_thirtyThreeAE_587459 : Nat.Prime 587459 := by norm_num
private theorem prime_thirtyThreeAE_40725007717 : Nat.Prime 40725007717 := by
  apply lucas_primality 40725007717 (2 : ZMod 40725007717)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (53, 1), (109, 1), (587459, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (53, 1), (109, 1), (587459, 1)] : List FactorBlock).map factorBlockValue).prod = 40725007717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_109
      · exact prime_thirtyThreeAE_587459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40725007717) ^ 20362503858 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40725007717) ^ 13575002572 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40725007717) ^ 768396372 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40725007717) ^ 373623924 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40725007717) ^ 69324 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_145632627595993 : Nat.Prime 145632627595993 := by
  apply lucas_primality 145632627595993 (5 : ZMod 145632627595993)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (149, 1), (40725007717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (149, 1), (40725007717, 1)] : List FactorBlock).map factorBlockValue).prod = 145632627595993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_149
      · exact prime_thirtyThreeAE_40725007717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 145632627595993) ^ 72816313797996 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 145632627595993) ^ 48544209198664 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 145632627595993) ^ 977400185208 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 145632627595993) ^ 3576 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_582530510383973 : Nat.Prime 582530510383973 := by
  apply lucas_primality 582530510383973 (2 : ZMod 582530510383973)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (145632627595993, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (145632627595993, 1)] : List FactorBlock).map factorBlockValue).prod = 582530510383973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_145632627595993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 582530510383973) ^ 291265255191986 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 582530510383973) ^ 4 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_3561591540487610923 : Nat.Prime 3561591540487610923 := by
  apply lucas_primality 3561591540487610923 (3 : ZMod 3561591540487610923)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1019, 1), (582530510383973, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1019, 1), (582530510383973, 1)] : List FactorBlock).map factorBlockValue).prod = 3561591540487610923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_1019
      · exact prime_thirtyThreeAE_582530510383973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3561591540487610923) ^ 1780795770243805461 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3561591540487610923) ^ 1187197180162536974 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3561591540487610923) ^ 3495183062303838 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3561591540487610923) ^ 6114 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1189571574522862048283 : Nat.Prime 1189571574522862048283 := by
  apply lucas_primality 1189571574522862048283 (2 : ZMod 1189571574522862048283)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (167, 1), (3561591540487610923, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (167, 1), (3561591540487610923, 1)] : List FactorBlock).map factorBlockValue).prod = 1189571574522862048283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_167
      · exact prime_thirtyThreeAE_3561591540487610923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1189571574522862048283) ^ 594785787261431024141 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1189571574522862048283) ^ 7123183080975221846 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1189571574522862048283) ^ 334 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_36973 : Nat.Prime 36973 := by norm_num
private theorem prime_thirtyThreeAE_4549 : Nat.Prime 4549 := by norm_num
private theorem prime_thirtyThreeAE_1304698691 : Nat.Prime 1304698691 := by
  apply lucas_primality 1304698691 (6 : ZMod 1304698691)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (23, 1), (29, 1), (43, 1), (4549, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (23, 1), (29, 1), (43, 1), (4549, 1)] : List FactorBlock).map factorBlockValue).prod = 1304698691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_4549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1304698691) ^ 652349345 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1304698691) ^ 260939738 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1304698691) ^ 56726030 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1304698691) ^ 44989610 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1304698691) ^ 30341830 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1304698691) ^ 286810 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_129281 : Nat.Prime 129281 := by norm_num
private theorem prime_thirtyThreeAE_4049080921 : Nat.Prime 4049080921 := by
  apply lucas_primality 4049080921 (11 : ZMod 4049080921)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (5, 1), (29, 1), (129281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (5, 1), (29, 1), (129281, 1)] : List FactorBlock).map factorBlockValue).prod = 4049080921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_129281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4049080921) ^ 2024540460 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 4049080921) ^ 1349693640 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 4049080921) ^ 809816184 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 4049080921) ^ 139623480 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (11 : ZMod 4049080921) ^ 31320 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_160554762038654875834876267 : Nat.Prime 160554762038654875834876267 := by
  apply lucas_primality 160554762038654875834876267 (2 : ZMod 160554762038654875834876267)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (137, 1), (36973, 1), (1304698691, 1), (4049080921, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (137, 1), (36973, 1), (1304698691, 1), (4049080921, 1)] : List FactorBlock).map factorBlockValue).prod = 160554762038654875834876267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_137
      · exact prime_thirtyThreeAE_36973
      · exact prime_thirtyThreeAE_1304698691
      · exact prime_thirtyThreeAE_4049080921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 160554762038654875834876267) ^ 80277381019327437917438133 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 160554762038654875834876267) ^ 53518254012884958611625422 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 160554762038654875834876267) ^ 1171932569625218071787418 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 160554762038654875834876267) ^ 4342486734607818565842 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 160554762038654875834876267) ^ 123058881829333326 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 160554762038654875834876267) ^ 39652149505325946 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_317 : Nat.Prime 317 := by norm_num
private theorem prime_thirtyThreeAE_11927 : Nat.Prime 11927 := by norm_num
private theorem prime_thirtyThreeAE_527347 : Nat.Prime 527347 := by norm_num
private theorem prime_thirtyThreeAE_127 : Nat.Prime 127 := by norm_num
private theorem prime_thirtyThreeAE_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_thirtyThreeAE_3851 : Nat.Prime 3851 := by norm_num
private theorem prime_thirtyThreeAE_7457249487047 : Nat.Prime 7457249487047 := by
  apply lucas_primality 7457249487047 (15 : ZMod 7457249487047)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (83, 1), (127, 1), (2963, 1), (3851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (83, 1), (127, 1), (2963, 1), (3851, 1)] : List FactorBlock).map factorBlockValue).prod = 7457249487047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_83
      · exact prime_thirtyThreeAE_127
      · exact prime_thirtyThreeAE_2963
      · exact prime_thirtyThreeAE_3851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 7457249487047) ^ 3728624743523 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 7457249487047) ^ 240556435066 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 7457249487047) ^ 89846379362 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 7457249487047) ^ 58718499898 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 7457249487047) ^ 2516790242 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (15 : ZMod 7457249487047) ^ 1936444946 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_59657995896377 : Nat.Prime 59657995896377 := by
  apply lucas_primality 59657995896377 (3 : ZMod 59657995896377)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7457249487047, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7457249487047, 1)] : List FactorBlock).map factorBlockValue).prod = 59657995896377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7457249487047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 59657995896377) ^ 29828997948188 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 59657995896377) ^ 8 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1500915871947108364540853 : Nat.Prime 1500915871947108364540853 := by
  apply lucas_primality 1500915871947108364540853 (2 : ZMod 1500915871947108364540853)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11927, 1), (527347, 1), (59657995896377, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11927, 1), (527347, 1), (59657995896377, 1)] : List FactorBlock).map factorBlockValue).prod = 1500915871947108364540853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_11927
      · exact prime_thirtyThreeAE_527347
      · exact prime_thirtyThreeAE_59657995896377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1500915871947108364540853) ^ 750457935973554182270426 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1500915871947108364540853) ^ 125841860647866887276 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1500915871947108364540853) ^ 2846163668224353916 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1500915871947108364540853) ^ 25158670676 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_32443 : Nat.Prime 32443 := by norm_num
private theorem prime_thirtyThreeAE_1336729 : Nat.Prime 1336729 := by norm_num
private theorem prime_thirtyThreeAE_40101871 : Nat.Prime 40101871 := by
  apply lucas_primality 40101871 (6 : ZMod 40101871)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (1336729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (1336729, 1)] : List FactorBlock).map factorBlockValue).prod = 40101871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_1336729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 40101871) ^ 20050935 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 40101871) ^ 13367290 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 40101871) ^ 8020374 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 40101871) ^ 30 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1306223 : Nat.Prime 1306223 := by norm_num
private theorem prime_thirtyThreeAE_73148489 : Nat.Prime 73148489 := by
  apply lucas_primality 73148489 (3 : ZMod 73148489)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (1306223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (1306223, 1)] : List FactorBlock).map factorBlockValue).prod = 73148489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_1306223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 73148489) ^ 36574244 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73148489) ^ 10449784 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73148489) ^ 56 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_215739179359349 : Nat.Prime 215739179359349 := by
  apply lucas_primality 215739179359349 (2 : ZMod 215739179359349)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (151, 1), (257, 1), (73148489, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (151, 1), (257, 1), (73148489, 1)] : List FactorBlock).map factorBlockValue).prod = 215739179359349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_151
      · exact prime_thirtyThreeAE_257
      · exact prime_thirtyThreeAE_73148489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 215739179359349) ^ 107869589679674 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 215739179359349) ^ 11354693650492 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 215739179359349) ^ 1428736287148 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 215739179359349) ^ 839452059764 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 215739179359349) ^ 2949332 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_311 : Nat.Prime 311 := by norm_num
private theorem prime_thirtyThreeAE_6133 : Nat.Prime 6133 := by norm_num
private theorem prime_thirtyThreeAE_1773847591 : Nat.Prime 1773847591 := by
  apply lucas_primality 1773847591 (3 : ZMod 1773847591)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (31, 1), (311, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (31, 1), (311, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod = 1773847591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_311
      · exact prime_thirtyThreeAE_6133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1773847591) ^ 886923795 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1773847591) ^ 591282530 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1773847591) ^ 354769518 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1773847591) ^ 57220890 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1773847591) ^ 5703690 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1773847591) ^ 289230 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_12743 : Nat.Prime 12743 := by norm_num
private theorem prime_thirtyThreeAE_1304419 : Nat.Prime 1304419 := by norm_num
private theorem prime_thirtyThreeAE_281547015287347 : Nat.Prime 281547015287347 := by
  apply lucas_primality 281547015287347 (2 : ZMod 281547015287347)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (941, 1), (12743, 1), (1304419, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (941, 1), (12743, 1), (1304419, 1)] : List FactorBlock).map factorBlockValue).prod = 281547015287347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_941
      · exact prime_thirtyThreeAE_12743
      · exact prime_thirtyThreeAE_1304419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 281547015287347) ^ 140773507643673 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 281547015287347) ^ 93849005095782 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 281547015287347) ^ 299199803706 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 281547015287347) ^ 22094249022 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 281547015287347) ^ 215840934 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_261838724217232711 : Nat.Prime 261838724217232711 := by
  apply lucas_primality 261838724217232711 (6 : ZMod 261838724217232711)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (31, 1), (281547015287347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (31, 1), (281547015287347, 1)] : List FactorBlock).map factorBlockValue).prod = 261838724217232711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_281547015287347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 261838724217232711) ^ 130919362108616355 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 261838724217232711) ^ 87279574739077570 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 261838724217232711) ^ 52367744843446542 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 261838724217232711) ^ 8446410458620410 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 261838724217232711) ^ 930 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_thirtyThreeAE_2018333 : Nat.Prime 2018333 := by norm_num
private theorem prime_thirtyThreeAE_2164039 : Nat.Prime 2164039 := by norm_num
private theorem prime_thirtyThreeAE_1823293747139 : Nat.Prime 1823293747139 := by
  apply lucas_primality 1823293747139 (2 : ZMod 1823293747139)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (43, 1), (97, 1), (101, 1), (2164039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (43, 1), (97, 1), (101, 1), (2164039, 1)] : List FactorBlock).map factorBlockValue).prod = 1823293747139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_97
      · exact prime_thirtyThreeAE_101
      · exact prime_thirtyThreeAE_2164039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1823293747139) ^ 911646873569 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1823293747139) ^ 42402180166 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1823293747139) ^ 18796842754 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1823293747139) ^ 18052413338 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1823293747139) ^ 842542 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_415710974347693 : Nat.Prime 415710974347693 := by
  apply lucas_primality 415710974347693 (5 : ZMod 415710974347693)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (1823293747139, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (1823293747139, 1)] : List FactorBlock).map factorBlockValue).prod = 415710974347693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_1823293747139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 415710974347693) ^ 207855487173846 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 415710974347693) ^ 138570324782564 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 415710974347693) ^ 21879524965668 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 415710974347693) ^ 228 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_376819 : Nat.Prime 376819 := by norm_num
private theorem prime_thirtyThreeAE_44171 : Nat.Prime 44171 := by norm_num
private theorem prime_thirtyThreeAE_433151 : Nat.Prime 433151 := by norm_num
private theorem prime_thirtyThreeAE_137742019 : Nat.Prime 137742019 := by
  apply lucas_primality 137742019 (2 : ZMod 137742019)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (53, 1), (433151, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (53, 1), (433151, 1)] : List FactorBlock).map factorBlockValue).prod = 137742019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_433151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 137742019) ^ 68871009 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 137742019) ^ 45914006 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 137742019) ^ 2598906 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 137742019) ^ 318 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_12168405442499 : Nat.Prime 12168405442499 := by
  apply lucas_primality 12168405442499 (2 : ZMod 12168405442499)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (44171, 1), (137742019, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (44171, 1), (137742019, 1)] : List FactorBlock).map factorBlockValue).prod = 12168405442499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_44171
      · exact prime_thirtyThreeAE_137742019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12168405442499) ^ 6084202721249 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12168405442499) ^ 275484038 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12168405442499) ^ 88342 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_4273486897247312594693 : Nat.Prime 4273486897247312594693 := by
  apply lucas_primality 4273486897247312594693 (2 : ZMod 4273486897247312594693)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (233, 1), (376819, 1), (12168405442499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (233, 1), (376819, 1), (12168405442499, 1)] : List FactorBlock).map factorBlockValue).prod = 4273486897247312594693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_233
      · exact prime_thirtyThreeAE_376819
      · exact prime_thirtyThreeAE_12168405442499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4273486897247312594693) ^ 2136743448623656297346 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4273486897247312594693) ^ 18341145481748122724 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4273486897247312594693) ^ 11340953872409068 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4273486897247312594693) ^ 351195308 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_432391 : Nat.Prime 432391 := by norm_num
private theorem prime_thirtyThreeAE_2395051 : Nat.Prime 2395051 := by norm_num
private theorem prime_thirtyThreeAE_4937 : Nat.Prime 4937 := by norm_num
private theorem prime_thirtyThreeAE_16073 : Nat.Prime 16073 := by norm_num
private theorem prime_thirtyThreeAE_433030813401061 : Nat.Prime 433030813401061 := by
  apply lucas_primality 433030813401061 (2 : ZMod 433030813401061)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (7, 1), (61, 1), (71, 1), (4937, 1), (16073, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (7, 1), (61, 1), (71, 1), (4937, 1), (16073, 1)] : List FactorBlock).map factorBlockValue).prod = 433030813401061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_61
      · exact prime_thirtyThreeAE_71
      · exact prime_thirtyThreeAE_4937
      · exact prime_thirtyThreeAE_16073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 433030813401061) ^ 216515406700530 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 144343604467020 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 86606162680212 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 61861544771580 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 7098865793460 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 6099025540860 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 87711325380 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 433030813401061) ^ 26941505220 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_thirtyThreeAE_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_thirtyThreeAE_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_thirtyThreeAE_17678041 : Nat.Prime 17678041 := by norm_num
private theorem prime_thirtyThreeAE_176780411 : Nat.Prime 176780411 := by
  apply lucas_primality 176780411 (2 : ZMod 176780411)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod = 176780411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176780411) ^ 88390205 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 35356082 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 10 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_3821 : Nat.Prime 3821 := by norm_num
private theorem prime_thirtyThreeAE_320291 : Nat.Prime 320291 := by norm_num
private theorem prime_thirtyThreeAE_53808889 : Nat.Prime 53808889 := by
  apply lucas_primality 53808889 (19 : ZMod 53808889)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (320291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (320291, 1)] : List FactorBlock).map factorBlockValue).prod = 53808889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_320291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 53808889) ^ 26904444 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (19 : ZMod 53808889) ^ 17936296 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (19 : ZMod 53808889) ^ 7686984 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (19 : ZMod 53808889) ^ 168 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_72503 : Nat.Prime 72503 := by norm_num
private theorem prime_thirtyThreeAE_114859 : Nat.Prime 114859 := by norm_num
private theorem prime_thirtyThreeAE_190519337877607 : Nat.Prime 190519337877607 := by
  apply lucas_primality 190519337877607 (6 : ZMod 190519337877607)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (31, 1), (41, 1), (72503, 1), (114859, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (31, 1), (41, 1), (72503, 1), (114859, 1)] : List FactorBlock).map factorBlockValue).prod = 190519337877607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_72503
      · exact prime_thirtyThreeAE_114859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 190519337877607) ^ 95259668938803 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 190519337877607) ^ 63506445959202 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 190519337877607) ^ 6145785092826 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 190519337877607) ^ 4646813118966 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 190519337877607) ^ 2627744202 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 190519337877607) ^ 1658723634 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_10210627368592812046028509 : Nat.Prime 10210627368592812046028509 := by
  apply lucas_primality 10210627368592812046028509 (2 : ZMod 10210627368592812046028509)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (83, 1), (53808889, 1), (190519337877607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (83, 1), (53808889, 1), (190519337877607, 1)] : List FactorBlock).map factorBlockValue).prod = 10210627368592812046028509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_83
      · exact prime_thirtyThreeAE_53808889
      · exact prime_thirtyThreeAE_190519337877607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10210627368592812046028509) ^ 5105313684296406023014254 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10210627368592812046028509) ^ 3403542456197604015342836 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10210627368592812046028509) ^ 123019606850515807783476 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10210627368592812046028509) ^ 189757260526096572 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10210627368592812046028509) ^ 53593653444 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_thirtyThreeAE_4457 : Nat.Prime 4457 := by norm_num
private theorem prime_thirtyThreeAE_16987 : Nat.Prime 16987 := by norm_num
private theorem prime_thirtyThreeAE_263 : Nat.Prime 263 := by norm_num
private theorem prime_thirtyThreeAE_316363 : Nat.Prime 316363 := by norm_num
private theorem prime_thirtyThreeAE_45595501013 : Nat.Prime 45595501013 := by
  apply lucas_primality 45595501013 (2 : ZMod 45595501013)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (137, 1), (263, 1), (316363, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (137, 1), (263, 1), (316363, 1)] : List FactorBlock).map factorBlockValue).prod = 45595501013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_137
      · exact prime_thirtyThreeAE_263
      · exact prime_thirtyThreeAE_316363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45595501013) ^ 22797750506 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 45595501013) ^ 332813876 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 45595501013) ^ 173366924 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 45595501013) ^ 144124 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_17782245395071 : Nat.Prime 17782245395071 := by
  apply lucas_primality 17782245395071 (6 : ZMod 17782245395071)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (13, 1), (45595501013, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (13, 1), (45595501013, 1)] : List FactorBlock).map factorBlockValue).prod = 17782245395071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_45595501013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17782245395071) ^ 8891122697535 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 17782245395071) ^ 5927415131690 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 17782245395071) ^ 3556449079014 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 17782245395071) ^ 1367865030390 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 17782245395071) ^ 390 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_887 : Nat.Prime 887 := by norm_num
private theorem prime_thirtyThreeAE_4419271 : Nat.Prime 4419271 := by norm_num
private theorem prime_thirtyThreeAE_2322707 : Nat.Prime 2322707 := by norm_num
private theorem prime_thirtyThreeAE_1175289743 : Nat.Prime 1175289743 := by
  apply lucas_primality 1175289743 (10 : ZMod 1175289743)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (23, 1), (2322707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (23, 1), (2322707, 1)] : List FactorBlock).map factorBlockValue).prod = 1175289743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_2322707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1175289743) ^ 587644871 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 1175289743) ^ 106844522 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 1175289743) ^ 51099554 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (10 : ZMod 1175289743) ^ 506 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_244138237154419 : Nat.Prime 244138237154419 := by
  apply lucas_primality 244138237154419 (2 : ZMod 244138237154419)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (89, 1), (389, 1), (1175289743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (89, 1), (389, 1), (1175289743, 1)] : List FactorBlock).map factorBlockValue).prod = 244138237154419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_89
      · exact prime_thirtyThreeAE_389
      · exact prime_thirtyThreeAE_1175289743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 244138237154419) ^ 122069118577209 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 244138237154419) ^ 81379412384806 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 244138237154419) ^ 2743126260162 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 244138237154419) ^ 627604722762 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 244138237154419) ^ 207726 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_109373930245179713 : Nat.Prime 109373930245179713 := by
  apply lucas_primality 109373930245179713 (3 : ZMod 109373930245179713)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (7, 1), (244138237154419, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (7, 1), (244138237154419, 1)] : List FactorBlock).map factorBlockValue).prod = 109373930245179713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_244138237154419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 109373930245179713) ^ 54686965122589856 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 109373930245179713) ^ 15624847177882816 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 109373930245179713) ^ 448 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_307 : Nat.Prime 307 := by norm_num
private theorem prime_thirtyThreeAE_3041 : Nat.Prime 3041 := by norm_num
private theorem prime_thirtyThreeAE_3943270783 : Nat.Prime 3943270783 := by
  apply lucas_primality 3943270783 (7 : ZMod 3943270783)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (11, 1), (37, 1), (59, 1), (3041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (11, 1), (37, 1), (59, 1), (3041, 1)] : List FactorBlock).map factorBlockValue).prod = 3943270783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_59
      · exact prime_thirtyThreeAE_3041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3943270783) ^ 1971635391 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3943270783) ^ 1314423594 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3943270783) ^ 358479162 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3943270783) ^ 106574886 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3943270783) ^ 66835098 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3943270783) ^ 1296702 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_9739 : Nat.Prime 9739 := by norm_num
private theorem prime_thirtyThreeAE_9044804081 : Nat.Prime 9044804081 := by
  apply lucas_primality 9044804081 (6 : ZMod 9044804081)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (13, 1), (19, 1), (47, 1), (9739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (13, 1), (19, 1), (47, 1), (9739, 1)] : List FactorBlock).map factorBlockValue).prod = 9044804081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_9739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9044804081) ^ 4522402040 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9044804081) ^ 1808960816 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9044804081) ^ 695754160 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9044804081) ^ 476042320 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9044804081) ^ 192442640 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9044804081) ^ 928720 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_271344122431 : Nat.Prime 271344122431 := by
  apply lucas_primality 271344122431 (3 : ZMod 271344122431)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (9044804081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (9044804081, 1)] : List FactorBlock).map factorBlockValue).prod = 271344122431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_9044804081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 271344122431) ^ 135672061215 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 271344122431) ^ 90448040810 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 271344122431) ^ 54268824486 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 271344122431) ^ 30 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_thirtyThreeAE_627787 : Nat.Prime 627787 := by norm_num
private theorem prime_thirtyThreeAE_118373 : Nat.Prime 118373 := by norm_num
private theorem prime_thirtyThreeAE_53504597 : Nat.Prime 53504597 := by
  apply lucas_primality 53504597 (2 : ZMod 53504597)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (113, 1), (118373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (113, 1), (118373, 1)] : List FactorBlock).map factorBlockValue).prod = 53504597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_113
      · exact prime_thirtyThreeAE_118373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53504597) ^ 26752298 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 53504597) ^ 473492 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 53504597) ^ 452 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_403073885242069 : Nat.Prime 403073885242069 := by
  apply lucas_primality 403073885242069 (2 : ZMod 403073885242069)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (627787, 1), (53504597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (627787, 1), (53504597, 1)] : List FactorBlock).map factorBlockValue).prod = 403073885242069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_627787
      · exact prime_thirtyThreeAE_53504597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 403073885242069) ^ 201536942621034 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 403073885242069) ^ 134357961747356 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 403073885242069) ^ 642055164 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 403073885242069) ^ 7533444 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_611866157797460743 : Nat.Prime 611866157797460743 := by
  apply lucas_primality 611866157797460743 (5 : ZMod 611866157797460743)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (23, 1), (403073885242069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (23, 1), (403073885242069, 1)] : List FactorBlock).map factorBlockValue).prod = 611866157797460743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_403073885242069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 611866157797460743) ^ 305933078898730371 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 611866157797460743) ^ 203955385932486914 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 611866157797460743) ^ 55624196163405522 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 611866157797460743) ^ 26602876425976554 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 611866157797460743) ^ 1518 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_262688826330237036027733 : Nat.Prime 262688826330237036027733 := by
  apply lucas_primality 262688826330237036027733 (5 : ZMod 262688826330237036027733)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (19, 1), (269, 1), (611866157797460743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (19, 1), (269, 1), (611866157797460743, 1)] : List FactorBlock).map factorBlockValue).prod = 262688826330237036027733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_269
      · exact prime_thirtyThreeAE_611866157797460743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 262688826330237036027733) ^ 131344413165118518013866 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 262688826330237036027733) ^ 87562942110079012009244 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 262688826330237036027733) ^ 37526975190033862289676 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 262688826330237036027733) ^ 13825727701591422948828 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 262688826330237036027733) ^ 976538387844747345828 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 262688826330237036027733) ^ 429324 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_2087 : Nat.Prime 2087 := by norm_num
private theorem prime_thirtyThreeAE_2901931 : Nat.Prime 2901931 := by norm_num
private theorem prime_thirtyThreeAE_63842483 : Nat.Prime 63842483 := by
  apply lucas_primality 63842483 (2 : ZMod 63842483)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (2901931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (2901931, 1)] : List FactorBlock).map factorBlockValue).prod = 63842483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_2901931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63842483) ^ 31921241 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 63842483) ^ 5803862 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 63842483) ^ 22 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_3947 : Nat.Prime 3947 := by norm_num
private theorem prime_thirtyThreeAE_2964881 : Nat.Prime 2964881 := by norm_num
private theorem prime_thirtyThreeAE_187238164913 : Nat.Prime 187238164913 := by
  apply lucas_primality 187238164913 (3 : ZMod 187238164913)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3947, 1), (2964881, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3947, 1), (2964881, 1)] : List FactorBlock).map factorBlockValue).prod = 187238164913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3947
      · exact prime_thirtyThreeAE_2964881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 187238164913) ^ 93619082456 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 187238164913) ^ 47438096 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 187238164913) ^ 63152 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_300869 : Nat.Prime 300869 := by norm_num
private theorem prime_thirtyThreeAE_65353 : Nat.Prime 65353 := by norm_num
private theorem prime_thirtyThreeAE_38688977 : Nat.Prime 38688977 := by
  apply lucas_primality 38688977 (3 : ZMod 38688977)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (37, 1), (65353, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (37, 1), (65353, 1)] : List FactorBlock).map factorBlockValue).prod = 38688977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_65353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38688977) ^ 19344488 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 38688977) ^ 1045648 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 38688977) ^ 592 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_31771 : Nat.Prime 31771 := by norm_num
private theorem prime_thirtyThreeAE_383983 : Nat.Prime 383983 := by norm_num
private theorem prime_thirtyThreeAE_35281023098557 : Nat.Prime 35281023098557 := by
  apply lucas_primality 35281023098557 (5 : ZMod 35281023098557)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (241, 1), (31771, 1), (383983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (241, 1), (31771, 1), (383983, 1)] : List FactorBlock).map factorBlockValue).prod = 35281023098557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_241
      · exact prime_thirtyThreeAE_31771
      · exact prime_thirtyThreeAE_383983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 35281023098557) ^ 17640511549278 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 35281023098557) ^ 11760341032852 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 35281023098557) ^ 146394286716 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 35281023098557) ^ 1110478836 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (5 : ZMod 35281023098557) ^ 91881732 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_406404241410345154457030551 : Nat.Prime 406404241410345154457030551 := by
  apply lucas_primality 406404241410345154457030551 (3 : ZMod 406404241410345154457030551)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 406404241410345154457030551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_59
      · exact prime_thirtyThreeAE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 406404241410345154457030551) ^ 203202120705172577228515275 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 135468080470115051485676850 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 81280848282069030891406110 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 58057748772906450636718650 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 36945840128213195859730050 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 31261864723872704189002350 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 23906131847667362026884150 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 21389696916333955497738450 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 17669749626536745845957850 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 14013939358977419119207950 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 13109814239043392079259050 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 10983898416495814985325150 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 9912298570984028157488550 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 9451261428147561731558850 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 8646898753411599031000650 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 7668004554912172725604350 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 6888207481531273804356450 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (3 : ZMod 406404241410345154457030551) ^ 6662364613284346794377550 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1691051 : Nat.Prime 1691051 := by norm_num
private theorem prime_thirtyThreeAE_213072427 : Nat.Prime 213072427 := by
  apply lucas_primality 213072427 (2 : ZMod 213072427)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (1691051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (1691051, 1)] : List FactorBlock).map factorBlockValue).prod = 213072427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_1691051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 213072427) ^ 106536213 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 213072427) ^ 71024142 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 213072427) ^ 30438918 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 213072427) ^ 126 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_202729 : Nat.Prime 202729 := by norm_num
private theorem prime_thirtyThreeAE_2508677 : Nat.Prime 2508677 := by norm_num
private theorem prime_thirtyThreeAE_1475102077 : Nat.Prime 1475102077 := by
  apply lucas_primality 1475102077 (2 : ZMod 1475102077)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (2508677, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (2508677, 1)] : List FactorBlock).map factorBlockValue).prod = 1475102077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_2508677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1475102077) ^ 737551038 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1475102077) ^ 491700692 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1475102077) ^ 210728868 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1475102077) ^ 588 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_38875975965857291 : Nat.Prime 38875975965857291 := by
  apply lucas_primality 38875975965857291 (2 : ZMod 38875975965857291)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (202729, 1), (1475102077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (202729, 1), (1475102077, 1)] : List FactorBlock).map factorBlockValue).prod = 38875975965857291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_202729
      · exact prime_thirtyThreeAE_1475102077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38875975965857291) ^ 19437987982928645 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 38875975965857291) ^ 7775195193171458 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 38875975965857291) ^ 2990459689681330 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 38875975965857291) ^ 191763270010 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 38875975965857291) ^ 26354770 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_183105846799187840611 : Nat.Prime 183105846799187840611 := by
  apply lucas_primality 183105846799187840611 (2 : ZMod 183105846799187840611)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (157, 1), (38875975965857291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (157, 1), (38875975965857291, 1)] : List FactorBlock).map factorBlockValue).prod = 183105846799187840611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_157
      · exact prime_thirtyThreeAE_38875975965857291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 183105846799187840611) ^ 91552923399593920305 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 183105846799187840611) ^ 61035282266395946870 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 183105846799187840611) ^ 36621169359837568122 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 183105846799187840611) ^ 1166279278975718730 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 183105846799187840611) ^ 4710 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_thirtyThreeAE_2486059 : Nat.Prime 2486059 := by norm_num
private theorem prime_thirtyThreeAE_3079 : Nat.Prime 3079 := by norm_num
private theorem prime_thirtyThreeAE_24413 : Nat.Prime 24413 := by norm_num
private theorem prime_thirtyThreeAE_11876485067 : Nat.Prime 11876485067 := by
  apply lucas_primality 11876485067 (2 : ZMod 11876485067)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (79, 1), (3079, 1), (24413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (79, 1), (3079, 1), (24413, 1)] : List FactorBlock).map factorBlockValue).prod = 11876485067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_79
      · exact prime_thirtyThreeAE_3079
      · exact prime_thirtyThreeAE_24413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11876485067) ^ 5938242533 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11876485067) ^ 150335254 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11876485067) ^ 3857254 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11876485067) ^ 486482 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_44701822880019962843 : Nat.Prime 44701822880019962843 := by
  apply lucas_primality 44701822880019962843 (2 : ZMod 44701822880019962843)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (757, 1), (2486059, 1), (11876485067, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (757, 1), (2486059, 1), (11876485067, 1)] : List FactorBlock).map factorBlockValue).prod = 44701822880019962843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_757
      · exact prime_thirtyThreeAE_2486059
      · exact prime_thirtyThreeAE_11876485067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44701822880019962843) ^ 22350911440009981421 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 44701822880019962843) ^ 59051285178361906 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 44701822880019962843) ^ 17980998391438 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (2 : ZMod 44701822880019962843) ^ 3763893326 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem prime_thirtyThreeAE_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← thirtyThreeAEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyThreeAE_2
      · exact prime_thirtyThreeAE_3
      · exact prime_thirtyThreeAE_5
      · exact prime_thirtyThreeAE_7
      · exact prime_thirtyThreeAE_11
      · exact prime_thirtyThreeAE_13
      · exact prime_thirtyThreeAE_17
      · exact prime_thirtyThreeAE_19
      · exact prime_thirtyThreeAE_23
      · exact prime_thirtyThreeAE_29
      · exact prime_thirtyThreeAE_31
      · exact prime_thirtyThreeAE_37
      · exact prime_thirtyThreeAE_41
      · exact prime_thirtyThreeAE_43
      · exact prime_thirtyThreeAE_47
      · exact prime_thirtyThreeAE_53
      · exact prime_thirtyThreeAE_59
      · exact prime_thirtyThreeAE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← thirtyThreeAEFastPow_eq_pow]
      decide

private theorem phi_thirtyThreeAE_39014807175393134827874932800 : Nat.totient 39014807175393134827874932800 = 5133855159158901099724800000 := by
  rw [← show ((([(2, 6), (3, 4), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932800 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_5, prime_thirtyThreeAE_7, prime_thirtyThreeAE_11, prime_thirtyThreeAE_13, prime_thirtyThreeAE_17, prime_thirtyThreeAE_19, prime_thirtyThreeAE_23, prime_thirtyThreeAE_29, prime_thirtyThreeAE_31, prime_thirtyThreeAE_37, prime_thirtyThreeAE_41, prime_thirtyThreeAE_43, prime_thirtyThreeAE_47, prime_thirtyThreeAE_53, prime_thirtyThreeAE_59, prime_thirtyThreeAE_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932801 : Nat.totient 39014807175393134827874932801 = 38632036563464906772732365760 := by
  rw [← show ((([(113, 1), (1031, 1), (334882425134057791025767, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_113, prime_thirtyThreeAE_1031, prime_thirtyThreeAE_334882425134057791025767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932802 : Nat.totient 39014807175393134827874932802 = 19507403587696567413937466400 := by
  rw [← show ((([(2, 1), (19507403587696567413937466401, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_19507403587696567413937466401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932803 : Nat.totient 39014807175393134827874932803 = 25696470798114530233657925120 := by
  rw [← show ((([(3, 1), (83, 1), (895529, 1), (2064319931, 1), (84756586553, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_83, prime_thirtyThreeAE_895529, prime_thirtyThreeAE_2064319931, prime_thirtyThreeAE_84756586553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932804 : Nat.totient 39014807175393134827874932804 = 19504103591908917610927054848 := by
  rw [← show ((([(2, 2), (7687, 1), (35803, 1), (106033, 1), (581873, 1), (574412549, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_7687, prime_thirtyThreeAE_35803, prime_thirtyThreeAE_106033, prime_thirtyThreeAE_581873, prime_thirtyThreeAE_574412549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932805 : Nat.totient 39014807175393134827874932805 = 31211845740314507862299946240 := by
  rw [← show ((([(5, 1), (7802961435078626965574986561, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_5, prime_thirtyThreeAE_7802961435078626965574986561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932806 : Nat.totient 39014807175393134827874932806 = 13004934564712626979387822944 := by
  rw [← show ((([(2, 1), (3, 1), (11218483, 1), (15837208853, 1), (36598681199, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_11218483, prime_thirtyThreeAE_15837208853, prime_thirtyThreeAE_36598681199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932807 : Nat.totient 39014807175393134827874932807 = 33410779005728973966217034688 := by
  rw [← show ((([(7, 1), (1097, 1), (720517077359, 1), (7051483897687, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_7, prime_thirtyThreeAE_1097, prime_thirtyThreeAE_720517077359, prime_thirtyThreeAE_7051483897687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932808 : Nat.totient 39014807175393134827874932808 = 19507403587695988624580962816 := by
  rw [← show ((([(2, 3), (53441552104049, 1), (91255787021849, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_53441552104049, prime_thirtyThreeAE_91255787021849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932809 : Nat.totient 39014807175393134827874932809 = 25994544478281970798694111232 := by
  rw [← show ((([(3, 2), (1697, 1), (2554495330019847759305633, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_1697, prime_thirtyThreeAE_2554495330019847759305633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932810 : Nat.totient 39014807175393134827874932810 = 15600649811112047321058893760 := by
  rw [← show ((([(2, 1), (5, 1), (2971, 1), (768197, 1), (1709441354857832663, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_5, prime_thirtyThreeAE_2971, prime_thirtyThreeAE_768197, prime_thirtyThreeAE_1709441354857832663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932811 : Nat.totient 39014807175393134827874932811 = 35468006521919069893387261000 := by
  rw [← show ((([(11, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_11, prime_thirtyThreeAE_30429025931, prime_thirtyThreeAE_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932812 : Nat.totient 39014807175393134827874932812 = 13001847227232470590570714560 := by
  rw [← show ((([(2, 2), (3, 1), (4211, 1), (75111599, 1), (10279120799235109, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_4211, prime_thirtyThreeAE_75111599, prime_thirtyThreeAE_10279120799235109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932813 : Nat.totient 39014807175393134827874932813 = 36013668161901355225730707056 := by
  rw [← show ((([(13, 2), (230856847191675354011094277, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_13, prime_thirtyThreeAE_230856847191675354011094277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932814 : Nat.totient 39014807175393134827874932814 = 16717606383046017968324571672 := by
  rw [← show ((([(2, 1), (7, 1), (5527, 1), (504210591839969175061063, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_7, prime_thirtyThreeAE_5527, prime_thirtyThreeAE_504210591839969175061063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932815 : Nat.totient 39014807175393134827874932815 = 20757324115310651790749452800 := by
  rw [← show ((([(3, 1), (5, 1), (631, 1), (1181, 1), (3446959, 1), (1012564812501629, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_5, prime_thirtyThreeAE_631, prime_thirtyThreeAE_1181, prime_thirtyThreeAE_3446959, prime_thirtyThreeAE_1012564812501629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932816 : Nat.totient 39014807175393134827874932816 = 19491633657552916187248743936 := by
  rw [← show ((([(2, 4), (1237, 1), (1971241267956403336089073, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_1237, prime_thirtyThreeAE_1971241267956403336089073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932817 : Nat.totient 39014807175393134827874932817 = 36499939365084454135119237120 := by
  rw [← show ((([(17, 1), (167, 1), (282142244161, 1), (48707513088023, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_17, prime_thirtyThreeAE_167, prime_thirtyThreeAE_282142244161, prime_thirtyThreeAE_48707513088023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932818 : Nat.totient 39014807175393134827874932818 = 13004935722884783994614525952 := by
  rw [← show ((([(2, 1), (3, 2), (5789592673, 1), (374376818878815937, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_5789592673, prime_thirtyThreeAE_374376818878815937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932819 : Nat.totient 39014807175393134827874932819 = 36158659053877380154820400000 := by
  rw [← show ((([(19, 1), (79, 1), (151, 1), (389, 1), (3137370571, 1), (141044581151, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_19, prime_thirtyThreeAE_79, prime_thirtyThreeAE_151, prime_thirtyThreeAE_389, prime_thirtyThreeAE_3137370571, prime_thirtyThreeAE_141044581151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932820 : Nat.totient 39014807175393134827874932820 = 15605830313908589008115648640 := by
  rw [← show ((([(2, 2), (5, 1), (319027, 1), (357613, 1), (17098528289089591, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_5, prime_thirtyThreeAE_319027, prime_thirtyThreeAE_357613, prime_thirtyThreeAE_17098528289089591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932821 : Nat.totient 39014807175393134827874932821 = 22293490207855165419371401200 := by
  rw [← show ((([(3, 1), (7, 1), (32531, 1), (57110078409302094014171, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_7, prime_thirtyThreeAE_32531, prime_thirtyThreeAE_57110078409302094014171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932822 : Nat.totient 39014807175393134827874932822 = 17731658086972419422885875200 := by
  rw [← show ((([(2, 1), (11, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_11, prime_thirtyThreeAE_8233, prime_thirtyThreeAE_93811, prime_thirtyThreeAE_8274073, prime_thirtyThreeAE_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932823 : Nat.totient 39014807175393134827874932823 = 37254935621570148201480140160 := by
  rw [← show ((([(23, 1), (587, 1), (60758353, 1), (47561718131757491, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_23, prime_thirtyThreeAE_587, prime_thirtyThreeAE_60758353, prime_thirtyThreeAE_47561718131757491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932824 : Nat.totient 39014807175393134827874932824 = 12989365573029065613379666944 := by
  rw [← show ((([(2, 3), (3, 1), (857, 1), (32869, 1), (57709978139285874797, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_857, prime_thirtyThreeAE_32869, prime_thirtyThreeAE_57709978139285874797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932825 : Nat.totient 39014807175393134827874932825 = 31209238016549756044448399360 := by
  rw [← show ((([(5, 2), (11969, 1), (130386188237590892565377, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_5, prime_thirtyThreeAE_11969, prime_thirtyThreeAE_130386188237590892565377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932826 : Nat.totient 39014807175393134827874932826 = 17999174857462845987621038400 := by
  rw [← show ((([(2, 1), (13, 1), (2351, 1), (128055227077, 1), (4984322987363, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_13, prime_thirtyThreeAE_2351, prime_thirtyThreeAE_128055227077, prime_thirtyThreeAE_4984322987363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932827 : Nat.totient 39014807175393134827874932827 = 25752346973335363135983667200 := by
  rw [← show ((([(3, 3), (101, 1), (25824109, 1), (554011756364663489, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_101, prime_thirtyThreeAE_25824109, prime_thirtyThreeAE_554011756364663489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932828 : Nat.totient 39014807175393134827874932828 = 16720631646524429393726038704 := by
  rw [← show ((([(2, 2), (7, 1), (230230462223, 1), (6052135573615487, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_7, prime_thirtyThreeAE_230230462223, prime_thirtyThreeAE_6052135573615487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932829 : Nat.totient 39014807175393134827874932829 = 37548822090946045193753370624 := by
  rw [← show ((([(29, 1), (433, 1), (1117, 1), (8271049, 1), (336302273857309, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_29, prime_thirtyThreeAE_433, prime_thirtyThreeAE_1117, prime_thirtyThreeAE_8271049, prime_thirtyThreeAE_336302273857309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932830 : Nat.totient 39014807175393134827874932830 = 10257128243015157081441346560 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (71, 1), (37967, 1), (834527, 1), (3072847, 1), (188131817, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_5, prime_thirtyThreeAE_71, prime_thirtyThreeAE_37967, prime_thirtyThreeAE_834527, prime_thirtyThreeAE_3072847, prime_thirtyThreeAE_188131817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932831 : Nat.totient 39014807175393134827874932831 = 37716141450165299775310456800 := by
  rw [← show ((([(31, 1), (941, 1), (10650116699, 1), (125580954875839, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_31, prime_thirtyThreeAE_941, prime_thirtyThreeAE_10650116699, prime_thirtyThreeAE_125580954875839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932832 : Nat.totient 39014807175393134827874932832 = 19503814472236218570714547200 := by
  rw [← show ((([(2, 5), (9851, 1), (14699, 1), (69193, 1), (121688410067443, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_9851, prime_thirtyThreeAE_14699, prime_thirtyThreeAE_69193, prime_thirtyThreeAE_121688410067443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932833 : Nat.totient 39014807175393134827874932833 = 23411096557065912790019523840 := by
  rw [← show ((([(3, 1), (11, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_11, prime_thirtyThreeAE_103, prime_thirtyThreeAE_5009, prime_thirtyThreeAE_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932834 : Nat.totient 39014807175393134827874932834 = 18353258340282091312954848000 := by
  rw [← show ((([(2, 1), (17, 1), (3061, 1), (28111, 1), (13335549722584137331, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_17, prime_thirtyThreeAE_3061, prime_thirtyThreeAE_28111, prime_thirtyThreeAE_13335549722584137331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932835 : Nat.totient 39014807175393134827874932835 = 26753010634555292453399953920 := by
  rw [← show ((([(5, 1), (7, 1), (1114708776439803852224998081, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_5, prime_thirtyThreeAE_7, prime_thirtyThreeAE_1114708776439803852224998081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932836 : Nat.totient 39014807175393134827874932836 = 12944043479653120912098226176 := by
  rw [← show ((([(2, 2), (3, 2), (257, 1), (1259, 1), (3349408442130034682227, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_257, prime_thirtyThreeAE_1259, prime_thirtyThreeAE_3349408442130034682227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932837 : Nat.totient 39014807175393134827874932837 = 37960352927409536589283718400 := by
  rw [← show ((([(37, 1), (1054454247983598238591214401, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_37, prime_thirtyThreeAE_1054454247983598238591214401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932838 : Nat.totient 39014807175393134827874932838 = 18480698094154125338512022016 := by
  rw [← show ((([(2, 1), (19, 1), (444692113, 1), (2308800677973863377, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_19, prime_thirtyThreeAE_444692113, prime_thirtyThreeAE_2308800677973863377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932839 : Nat.totient 39014807175393134827874932839 = 23994355431776932430665041888 := by
  rw [← show ((([(3, 1), (13, 1), (1627, 1), (614861506554349437030163, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_13, prime_thirtyThreeAE_1627, prime_thirtyThreeAE_614861506554349437030163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932840 : Nat.totient 39014807175393134827874932840 = 15604792930097062221538713600 := by
  rw [← show ((([(2, 3), (5, 1), (14449, 1), (594571, 1), (660521, 1), (171886326419, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_5, prime_thirtyThreeAE_14449, prime_thirtyThreeAE_594571, prime_thirtyThreeAE_660521, prime_thirtyThreeAE_171886326419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932841 : Nat.totient 39014807175393134827874932841 = 37897907071613270230935429120 := by
  rw [← show ((([(41, 1), (457, 1), (463, 1), (12410771809, 1), (362367822679, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_41, prime_thirtyThreeAE_457, prime_thirtyThreeAE_463, prime_thirtyThreeAE_12410771809, prime_thirtyThreeAE_362367822679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932842 : Nat.totient 39014807175393134827874932842 = 11078700722898664052788322544 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (163, 1), (5698920124947872455138027, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_7, prime_thirtyThreeAE_163, prime_thirtyThreeAE_5698920124947872455138027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932843 : Nat.totient 39014807175393134827874932843 = 38107444728574761159646930176 := by
  rw [← show ((([(43, 1), (976457, 1), (16401349, 1), (56653704915557, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_43, prime_thirtyThreeAE_976457, prime_thirtyThreeAE_16401349, prime_thirtyThreeAE_56653704915557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932844 : Nat.totient 39014807175393134827874932844 = 17700616604032677012676608000 := by
  rw [← show ((([(2, 2), (11, 1), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_11, prime_thirtyThreeAE_769, prime_thirtyThreeAE_2143, prime_thirtyThreeAE_8597, prime_thirtyThreeAE_9792301, prime_thirtyThreeAE_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932845 : Nat.totient 39014807175393134827874932845 = 20802481981863520335641782272 := by
  rw [← show ((([(3, 2), (5, 1), (4493, 1), (31159, 1), (222419, 1), (940573, 1), (29602789, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_5, prime_thirtyThreeAE_4493, prime_thirtyThreeAE_31159, prime_thirtyThreeAE_222419, prime_thirtyThreeAE_940573, prime_thirtyThreeAE_29602789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932846 : Nat.totient 39014807175393134827874932846 = 18626035417305166889197859040 := by
  rw [← show ((([(2, 1), (23, 1), (647, 1), (4253, 1), (308227915879277070211, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_23, prime_thirtyThreeAE_647, prime_thirtyThreeAE_4253, prime_thirtyThreeAE_308227915879277070211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932847 : Nat.totient 39014807175393134827874932847 = 38163502948982853069193680000 := by
  rw [← show ((([(47, 1), (1801, 1), (460911871364527210980601, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_47, prime_thirtyThreeAE_1801, prime_thirtyThreeAE_460911871364527210980601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932848 : Nat.totient 39014807175393134827874932848 = 12740054128354647803940168960 := by
  rw [← show ((([(2, 4), (3, 1), (67, 1), (181, 1), (67024695540586320517363, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_67, prime_thirtyThreeAE_181, prime_thirtyThreeAE_67024695540586320517363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932849 : Nat.totient 39014807175393134827874932849 = 32612555298170936629754357760 := by
  rw [← show ((([(7, 2), (73, 1), (89, 1), (2924413, 1), (41906540702335541, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_7, prime_thirtyThreeAE_73, prime_thirtyThreeAE_89, prime_thirtyThreeAE_2924413, prime_thirtyThreeAE_41906540702335541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932850 : Nat.totient 39014807175393134827874932850 = 15605915223804316091417625600 := by
  rw [← show ((([(2, 1), (5, 2), (2210353, 1), (26632349, 1), (13255263022181, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_5, prime_thirtyThreeAE_2210353, prime_thirtyThreeAE_26632349, prime_thirtyThreeAE_13255263022181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932851 : Nat.totient 39014807175393134827874932851 = 24479878984497584795784328704 := by
  rw [← show ((([(3, 1), (17, 1), (889731133, 1), (859806059102301397, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_17, prime_thirtyThreeAE_889731133, prime_thirtyThreeAE_859806059102301397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932852 : Nat.totient 39014807175393134827874932852 = 18006834080950677612865353600 := by
  rw [← show ((([(2, 2), (13, 1), (750284753372944900536056401, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_13, prime_thirtyThreeAE_750284753372944900536056401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932853 : Nat.totient 39014807175393134827874932853 = 38274468125566498424607574800 := by
  rw [← show ((([(53, 1), (9091, 1), (80973318366688877093611, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_53, prime_thirtyThreeAE_9091, prime_thirtyThreeAE_80973318366688877093611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932854 : Nat.totient 39014807175393134827874932854 = 13004742812646459397604810400 := by
  rw [← show ((([(2, 1), (3, 3), (67901, 1), (9392503, 1), (1132865085569267, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_67901, prime_thirtyThreeAE_9392503, prime_thirtyThreeAE_1132865085569267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932855 : Nat.totient 39014807175393134827874932855 = 28235169641970638323525785600 := by
  rw [← show ((([(5, 1), (11, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_5, prime_thirtyThreeAE_11, prime_thirtyThreeAE_281, prime_thirtyThreeAE_739, prime_thirtyThreeAE_3540386347, prime_thirtyThreeAE_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932856 : Nat.totient 39014807175393134827874932856 = 16714181618294817323659898880 := by
  rw [← show ((([(2, 3), (7, 1), (2593, 1), (10098437, 1), (26606316966320261, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_7, prime_thirtyThreeAE_2593, prime_thirtyThreeAE_10098437, prime_thirtyThreeAE_26606316966320261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932857 : Nat.totient 39014807175393134827874932857 = 24500404439341586928156672000 := by
  rw [← show ((([(3, 1), (19, 1), (241, 1), (641, 1), (4430773372276762682321, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_19, prime_thirtyThreeAE_241, prime_thirtyThreeAE_641, prime_thirtyThreeAE_4430773372276762682321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932858 : Nat.totient 39014807175393134827874932858 = 18780361430465905285601476800 := by
  rw [← show ((([(2, 1), (29, 1), (347, 1), (200371, 1), (33195391, 1), (291446834303, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_29, prime_thirtyThreeAE_347, prime_thirtyThreeAE_200371, prime_thirtyThreeAE_33195391, prime_thirtyThreeAE_291446834303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932859 : Nat.totient 39014807175393134827874932859 = 38333676456134828961895177200 := by
  rw [← show ((([(59, 2), (1931, 1), (48395359, 1), (119933208410791, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_59, prime_thirtyThreeAE_1931, prime_thirtyThreeAE_48395359, prime_thirtyThreeAE_119933208410791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932860 : Nat.totient 39014807175393134827874932860 = 10365263002105337358153246720 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (269, 1), (1127981, 1), (2143009765547021929, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_5, prime_thirtyThreeAE_269, prime_thirtyThreeAE_1127981, prime_thirtyThreeAE_2143009765547021929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932861 : Nat.totient 39014807175393134827874932861 = 37979516171037941921894054400 := by
  rw [← show ((([(61, 1), (97, 1), (456623, 1), (14440097064785116271, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_61, prime_thirtyThreeAE_97, prime_thirtyThreeAE_456623, prime_thirtyThreeAE_14440097064785116271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932862 : Nat.totient 39014807175393134827874932862 = 18878132504222484594133032000 := by
  rw [← show ((([(2, 1), (31, 1), (629271083474082819804434401, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_31, prime_thirtyThreeAE_629271083474082819804434401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932863 : Nat.totient 39014807175393134827874932863 = 22152174403001709641340467520 := by
  rw [← show ((([(3, 2), (7, 1), (157, 1), (2848589311, 1), (1384711894151563, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_7, prime_thirtyThreeAE_157, prime_thirtyThreeAE_2848589311, prime_thirtyThreeAE_1384711894151563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932864 : Nat.totient 39014807175393134827874932864 = 19495354500066468556090202112 := by
  rw [← show ((([(2, 7), (1619, 1), (455550499, 1), (413272131099673, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_1619, prime_thirtyThreeAE_455550499, prime_thirtyThreeAE_413272131099673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932865 : Nat.totient 39014807175393134827874932865 = 28810934529235254986438578176 := by
  rw [← show ((([(5, 1), (13, 1), (100799438353, 1), (5954674078603057, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_5, prime_thirtyThreeAE_13, prime_thirtyThreeAE_100799438353, prime_thirtyThreeAE_5954674078603057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932866 : Nat.totient 39014807175393134827874932866 = 11822668831358244907644122000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_11, prime_thirtyThreeAE_1222615931, prime_thirtyThreeAE_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932867 : Nat.totient 39014807175393134827874932867 = 39014248095453743941877976000 := by
  rw [← show ((([(69821, 1), (131510551, 1), (4248961567236377, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_69821, prime_thirtyThreeAE_131510551, prime_thirtyThreeAE_4248961567236377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932868 : Nat.totient 39014807175393134827874932868 = 18188319514380182833357048320 := by
  rw [← show ((([(2, 2), (17, 1), (107, 1), (10061981, 1), (532909278128481103, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_17, prime_thirtyThreeAE_107, prime_thirtyThreeAE_10061981, prime_thirtyThreeAE_532909278128481103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932869 : Nat.totient 39014807175393134827874932869 = 24855777827226602730477020160 := by
  rw [← show ((([(3, 1), (23, 1), (1307, 1), (5927, 1), (289278289, 1), (252321361381, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_23, prime_thirtyThreeAE_1307, prime_thirtyThreeAE_5927, prime_thirtyThreeAE_289278289, prime_thirtyThreeAE_252321361381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932870 : Nat.totient 39014807175393134827874932870 = 13376505267519962612422034016 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (268832959, 1), (2073236816992747999, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_5, prime_thirtyThreeAE_7, prime_thirtyThreeAE_268832959, prime_thirtyThreeAE_2073236816992747999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932871 : Nat.totient 39014807175393134827874932871 = 39014799097372422065040753720 := by
  rw [← show ((([(5475331, 1), (40962179, 1), (173954647060879, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_5475331, prime_thirtyThreeAE_40962179, prime_thirtyThreeAE_173954647060879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932872 : Nat.totient 39014807175393134827874932872 = 13004933063289408799115733600 := by
  rw [← show ((([(2, 3), (3, 2), (4885691, 1), (110910068172641332811, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_4885691, prime_thirtyThreeAE_110910068172641332811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932873 : Nat.totient 39014807175393134827874932873 = 38810541168885306843779560320 := by
  rw [← show ((([(191, 1), (109660197217, 1), (1862717844193559, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_191, prime_thirtyThreeAE_109660197217, prime_thirtyThreeAE_1862717844193559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932874 : Nat.totient 39014807175393134827874932874 = 18980176463704768294641859200 := by
  rw [← show ((([(2, 1), (37, 1), (527227123991799119295607201, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_37, prime_thirtyThreeAE_527227123991799119295607201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932875 : Nat.totient 39014807175393134827874932875 = 20807889426138559564908144000 := by
  rw [← show ((([(3, 1), (5, 3), (2719511, 1), (251922637, 1), (151858876903, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_5, prime_thirtyThreeAE_2719511, prime_thirtyThreeAE_251922637, prime_thirtyThreeAE_151858876903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932876 : Nat.totient 39014807175393134827874932876 = 18477658015554584802156509952 := by
  rw [← show ((([(2, 2), (19, 1), (6079, 1), (584105663, 1), (144574704177713, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_19, prime_thirtyThreeAE_6079, prime_thirtyThreeAE_584105663, prime_thirtyThreeAE_144574704177713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932877 : Nat.totient 39014807175393134827874932877 = 30359330435310118856967862080 := by
  rw [← show ((([(7, 1), (11, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_7, prime_thirtyThreeAE_11, prime_thirtyThreeAE_727, prime_thirtyThreeAE_40346827, prime_thirtyThreeAE_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932878 : Nat.totient 39014807175393134827874932878 = 12003300760809558825227877120 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (12227, 1), (43891, 1), (932050565158189193, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_13, prime_thirtyThreeAE_12227, prime_thirtyThreeAE_43891, prime_thirtyThreeAE_932050565158189193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932879 : Nat.totient 39014807175393134827874932879 = 39011688727874053566072861240 := by
  rw [← show ((([(12511, 1), (5439074383, 1), (573340264709983, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_12511, prime_thirtyThreeAE_5439074383, prime_thirtyThreeAE_573340264709983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932880 : Nat.totient 39014807175393134827874932880 = 15605884803866869199551309184 := by
  rw [← show ((([(2, 4), (5, 1), (409967, 1), (1189571574522862048283, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_5, prime_thirtyThreeAE_409967, prime_thirtyThreeAE_1189571574522862048283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932881 : Nat.totient 39014807175393134827874932881 = 26009871450262089885249955092 := by
  rw [← show ((([(3, 5), (160554762038654875834876267, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_160554762038654875834876267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932882 : Nat.totient 39014807175393134827874932882 = 18971576621411449727796369280 := by
  rw [← show ((([(2, 1), (41, 1), (317, 1), (1500915871947108364540853, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_41, prime_thirtyThreeAE_317, prime_thirtyThreeAE_1500915871947108364540853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932883 : Nat.totient 39014807175393134827874932883 = 38732930230345326306435396960 := by
  rw [← show ((([(139, 1), (32443, 1), (40101871, 1), (215739179359349, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_139, prime_thirtyThreeAE_32443, prime_thirtyThreeAE_40101871, prime_thirtyThreeAE_215739179359349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932884 : Nat.totient 39014807175393134827874932884 = 11147087758113909098464053600 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (1773847591, 1), (261838724217232711, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_7, prime_thirtyThreeAE_1773847591, prime_thirtyThreeAE_261838724217232711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932885 : Nat.totient 39014807175393134827874932885 = 29264737573490436313131847680 := by
  rw [← show ((([(5, 1), (17, 1), (311, 1), (1759, 1), (2018333, 1), (415710974347693, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_5, prime_thirtyThreeAE_17, prime_thirtyThreeAE_311, prime_thirtyThreeAE_1759, prime_thirtyThreeAE_2018333, prime_thirtyThreeAE_415710974347693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932886 : Nat.totient 39014807175393134827874932886 = 18809461981125033568280398944 := by
  rw [← show ((([(2, 1), (43, 1), (83, 1), (1279, 1), (4273486897247312594693, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_43, prime_thirtyThreeAE_83, prime_thirtyThreeAE_1279, prime_thirtyThreeAE_4273486897247312594693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932887 : Nat.totient 39014807175393134827874932887 = 25112910766619216951741520000 := by
  rw [← show ((([(3, 1), (29, 1), (432391, 1), (2395051, 1), (433030813401061, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_29, prime_thirtyThreeAE_432391, prime_thirtyThreeAE_2395051, prime_thirtyThreeAE_433030813401061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932888 : Nat.totient 39014807175393134827874932888 = 17686003571615047941478195200 := by
  rw [← show ((([(2, 3), (11, 1), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_11, prime_thirtyThreeAE_373, prime_thirtyThreeAE_55249, prime_thirtyThreeAE_157429, prime_thirtyThreeAE_773027, prime_thirtyThreeAE_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932889 : Nat.totient 39014807175393134827874932889 = 39004596548024542015828900560 := by
  rw [← show ((([(3821, 1), (10210627368592812046028509, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3821, prime_thirtyThreeAE_10210627368592812046028509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932890 : Nat.totient 39014807175393134827874932890 = 10326415827801953099726438400 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (149, 1), (2161, 1), (4457, 1), (16987, 1), (17782245395071, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_5, prime_thirtyThreeAE_149, prime_thirtyThreeAE_2161, prime_thirtyThreeAE_4457, prime_thirtyThreeAE_16987, prime_thirtyThreeAE_17782245395071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932891 : Nat.totient 39014807175393134827874932891 = 30834050028562742142478510080 := by
  rw [← show ((([(7, 1), (13, 1), (887, 1), (4419271, 1), (109373930245179713, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_7, prime_thirtyThreeAE_13, prime_thirtyThreeAE_887, prime_thirtyThreeAE_4419271, prime_thirtyThreeAE_109373930245179713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932892 : Nat.totient 39014807175393134827874932892 = 18584070010795159989546225600 := by
  rw [← show ((([(2, 2), (23, 1), (307, 1), (1291, 1), (3943270783, 1), (271344122431, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_23, prime_thirtyThreeAE_307, prime_thirtyThreeAE_1291, prime_thirtyThreeAE_3943270783, prime_thirtyThreeAE_271344122431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932893 : Nat.totient 39014807175393134827874932893 = 25155082009383498570015616320 := by
  rw [← show ((([(3, 1), (31, 1), (1597, 1), (262688826330237036027733, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_31, prime_thirtyThreeAE_1597, prime_thirtyThreeAE_262688826330237036027733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932894 : Nat.totient 39014807175393134827874932894 = 18788416193623869158745899520 := by
  rw [← show ((([(2, 1), (47, 1), (127, 1), (131, 1), (2087, 1), (63842483, 1), (187238164913, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_47, prime_thirtyThreeAE_127, prime_thirtyThreeAE_131, prime_thirtyThreeAE_2087, prime_thirtyThreeAE_63842483, prime_thirtyThreeAE_187238164913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932895 : Nat.totient 39014807175393134827874932895 = 29569017973822434080970725376 := by
  rw [← show ((([(5, 1), (19, 1), (300869, 1), (38688977, 1), (35281023098557, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932895 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_5, prime_thirtyThreeAE_19, prime_thirtyThreeAE_300869, prime_thirtyThreeAE_38688977, prime_thirtyThreeAE_35281023098557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932896 : Nat.totient 39014807175393134827874932896 = 13004935725131044942624977600 := by
  rw [← show ((([(2, 5), (3, 1), (406404241410345154457030551, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932896 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_3, prime_thirtyThreeAE_406404241410345154457030551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932897 : Nat.totient 39014807175393134827874932897 = 39014806992287288028474019860 := by
  rw [← show ((([(213072427, 1), (183105846799187840611, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932897 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_213072427, prime_thirtyThreeAE_183105846799187840611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932898 : Nat.totient 39014807175393134827874932898 = 16497409070881618896752740368 := by
  rw [← show ((([(2, 1), (7, 2), (79, 2), (1427, 1), (44701822880019962843, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932898 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_2, prime_thirtyThreeAE_7, prime_thirtyThreeAE_79, prime_thirtyThreeAE_1427, prime_thirtyThreeAE_44701822880019962843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyThreeAE_39014807175393134827874932899 : Nat.totient 39014807175393134827874932899 = 23645337682056445350227232000 := by
  rw [← show ((([(3, 2), (11, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393134827874932899 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyThreeAE_3, prime_thirtyThreeAE_11, prime_thirtyThreeAE_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64ThirtyThreeAE : certifiedKill 1 39014807175393134827874932799 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_thirtyThreeAE_39014807175393134827874932800, phi_thirtyThreeAE_39014807175393134827874932801, phi_thirtyThreeAE_39014807175393134827874932802,
    phi_thirtyThreeAE_39014807175393134827874932803, phi_thirtyThreeAE_39014807175393134827874932804, phi_thirtyThreeAE_39014807175393134827874932805,
    phi_thirtyThreeAE_39014807175393134827874932806, phi_thirtyThreeAE_39014807175393134827874932807, phi_thirtyThreeAE_39014807175393134827874932808,
    phi_thirtyThreeAE_39014807175393134827874932809, phi_thirtyThreeAE_39014807175393134827874932810, phi_thirtyThreeAE_39014807175393134827874932811,
    phi_thirtyThreeAE_39014807175393134827874932812, phi_thirtyThreeAE_39014807175393134827874932813, phi_thirtyThreeAE_39014807175393134827874932814,
    phi_thirtyThreeAE_39014807175393134827874932815, phi_thirtyThreeAE_39014807175393134827874932816, phi_thirtyThreeAE_39014807175393134827874932817,
    phi_thirtyThreeAE_39014807175393134827874932818, phi_thirtyThreeAE_39014807175393134827874932819, phi_thirtyThreeAE_39014807175393134827874932820,
    phi_thirtyThreeAE_39014807175393134827874932821, phi_thirtyThreeAE_39014807175393134827874932822, phi_thirtyThreeAE_39014807175393134827874932823,
    phi_thirtyThreeAE_39014807175393134827874932824, phi_thirtyThreeAE_39014807175393134827874932825, phi_thirtyThreeAE_39014807175393134827874932826,
    phi_thirtyThreeAE_39014807175393134827874932827, phi_thirtyThreeAE_39014807175393134827874932828, phi_thirtyThreeAE_39014807175393134827874932829,
    phi_thirtyThreeAE_39014807175393134827874932830, phi_thirtyThreeAE_39014807175393134827874932831, phi_thirtyThreeAE_39014807175393134827874932832,
    phi_thirtyThreeAE_39014807175393134827874932833, phi_thirtyThreeAE_39014807175393134827874932834, phi_thirtyThreeAE_39014807175393134827874932835,
    phi_thirtyThreeAE_39014807175393134827874932836, phi_thirtyThreeAE_39014807175393134827874932837, phi_thirtyThreeAE_39014807175393134827874932838,
    phi_thirtyThreeAE_39014807175393134827874932839, phi_thirtyThreeAE_39014807175393134827874932840, phi_thirtyThreeAE_39014807175393134827874932841,
    phi_thirtyThreeAE_39014807175393134827874932842, phi_thirtyThreeAE_39014807175393134827874932843, phi_thirtyThreeAE_39014807175393134827874932844,
    phi_thirtyThreeAE_39014807175393134827874932845, phi_thirtyThreeAE_39014807175393134827874932846, phi_thirtyThreeAE_39014807175393134827874932847,
    phi_thirtyThreeAE_39014807175393134827874932848, phi_thirtyThreeAE_39014807175393134827874932849, phi_thirtyThreeAE_39014807175393134827874932850,
    phi_thirtyThreeAE_39014807175393134827874932851, phi_thirtyThreeAE_39014807175393134827874932852, phi_thirtyThreeAE_39014807175393134827874932853,
    phi_thirtyThreeAE_39014807175393134827874932854, phi_thirtyThreeAE_39014807175393134827874932855, phi_thirtyThreeAE_39014807175393134827874932856,
    phi_thirtyThreeAE_39014807175393134827874932857, phi_thirtyThreeAE_39014807175393134827874932858, phi_thirtyThreeAE_39014807175393134827874932859,
    phi_thirtyThreeAE_39014807175393134827874932860, phi_thirtyThreeAE_39014807175393134827874932861, phi_thirtyThreeAE_39014807175393134827874932862,
    phi_thirtyThreeAE_39014807175393134827874932863, phi_thirtyThreeAE_39014807175393134827874932864, phi_thirtyThreeAE_39014807175393134827874932865,
    phi_thirtyThreeAE_39014807175393134827874932866, phi_thirtyThreeAE_39014807175393134827874932867, phi_thirtyThreeAE_39014807175393134827874932868,
    phi_thirtyThreeAE_39014807175393134827874932869, phi_thirtyThreeAE_39014807175393134827874932870, phi_thirtyThreeAE_39014807175393134827874932871,
    phi_thirtyThreeAE_39014807175393134827874932872, phi_thirtyThreeAE_39014807175393134827874932873, phi_thirtyThreeAE_39014807175393134827874932874,
    phi_thirtyThreeAE_39014807175393134827874932875, phi_thirtyThreeAE_39014807175393134827874932876, phi_thirtyThreeAE_39014807175393134827874932877,
    phi_thirtyThreeAE_39014807175393134827874932878, phi_thirtyThreeAE_39014807175393134827874932879, phi_thirtyThreeAE_39014807175393134827874932880,
    phi_thirtyThreeAE_39014807175393134827874932881, phi_thirtyThreeAE_39014807175393134827874932882, phi_thirtyThreeAE_39014807175393134827874932883,
    phi_thirtyThreeAE_39014807175393134827874932884, phi_thirtyThreeAE_39014807175393134827874932885, phi_thirtyThreeAE_39014807175393134827874932886,
    phi_thirtyThreeAE_39014807175393134827874932887, phi_thirtyThreeAE_39014807175393134827874932888, phi_thirtyThreeAE_39014807175393134827874932889,
    phi_thirtyThreeAE_39014807175393134827874932890, phi_thirtyThreeAE_39014807175393134827874932891, phi_thirtyThreeAE_39014807175393134827874932892,
    phi_thirtyThreeAE_39014807175393134827874932893, phi_thirtyThreeAE_39014807175393134827874932894, phi_thirtyThreeAE_39014807175393134827874932895,
    phi_thirtyThreeAE_39014807175393134827874932896, phi_thirtyThreeAE_39014807175393134827874932897, phi_thirtyThreeAE_39014807175393134827874932898,
    phi_thirtyThreeAE_39014807175393134827874932899]

end TotientTailPeriodKiller
end Erdos249257
