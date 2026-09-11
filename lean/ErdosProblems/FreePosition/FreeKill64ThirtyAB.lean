import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def thirtyABFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem thirtyABFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    thirtyABFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [thirtyABFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [thirtyABFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then thirtyABFastPow a n * thirtyABFastPow a n * a
        else thirtyABFastPow a n * thirtyABFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_thirtyAB_2 : Nat.Prime 2 := by norm_num
private theorem prime_thirtyAB_3 : Nat.Prime 3 := by norm_num
private theorem prime_thirtyAB_5 : Nat.Prime 5 := by norm_num
private theorem prime_thirtyAB_7 : Nat.Prime 7 := by norm_num
private theorem prime_thirtyAB_11 : Nat.Prime 11 := by norm_num
private theorem prime_thirtyAB_13 : Nat.Prime 13 := by norm_num
private theorem prime_thirtyAB_17 : Nat.Prime 17 := by norm_num
private theorem prime_thirtyAB_19 : Nat.Prime 19 := by norm_num
private theorem prime_thirtyAB_23 : Nat.Prime 23 := by norm_num
private theorem prime_thirtyAB_29 : Nat.Prime 29 := by norm_num
private theorem prime_thirtyAB_31 : Nat.Prime 31 := by norm_num
private theorem prime_thirtyAB_37 : Nat.Prime 37 := by norm_num
private theorem prime_thirtyAB_41 : Nat.Prime 41 := by norm_num
private theorem prime_thirtyAB_43 : Nat.Prime 43 := by norm_num
private theorem prime_thirtyAB_47 : Nat.Prime 47 := by norm_num
private theorem prime_thirtyAB_53 : Nat.Prime 53 := by norm_num
private theorem prime_thirtyAB_59 : Nat.Prime 59 := by norm_num
private theorem prime_thirtyAB_61 : Nat.Prime 61 := by norm_num
private theorem prime_thirtyAB_67 : Nat.Prime 67 := by norm_num
private theorem prime_thirtyAB_15937 : Nat.Prime 15937 := by norm_num
private theorem prime_thirtyAB_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_thirtyAB_19009 : Nat.Prime 19009 := by norm_num
private theorem prime_thirtyAB_1954163219 : Nat.Prime 1954163219 := by
  apply lucas_primality 1954163219 (2 : ZMod 1954163219)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 2), (1049, 1), (19009, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 2), (1049, 1), (19009, 1)] : List FactorBlock).map factorBlockValue).prod = 1954163219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_1049
      · exact prime_thirtyAB_19009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1954163219) ^ 977081609 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954163219) ^ 279166174 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954163219) ^ 1862882 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954163219) ^ 102802 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_113 : Nat.Prime 113 := by norm_num
private theorem prime_thirtyAB_42349 : Nat.Prime 42349 := by norm_num
private theorem prime_thirtyAB_47007391 : Nat.Prime 47007391 := by
  apply lucas_primality 47007391 (7 : ZMod 47007391)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (37, 1), (42349, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (37, 1), (42349, 1)] : List FactorBlock).map factorBlockValue).prod = 47007391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_42349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 47007391) ^ 23503695 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 47007391) ^ 15669130 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 47007391) ^ 9401478 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 47007391) ^ 1270470 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 47007391) ^ 1110 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_10623670367 : Nat.Prime 10623670367 := by
  apply lucas_primality 10623670367 (5 : ZMod 10623670367)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (113, 1), (47007391, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (113, 1), (47007391, 1)] : List FactorBlock).map factorBlockValue).prod = 10623670367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_113
      · exact prime_thirtyAB_47007391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10623670367) ^ 5311835183 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 10623670367) ^ 94014782 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 10623670367) ^ 226 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_84989362937 : Nat.Prime 84989362937 := by
  apply lucas_primality 84989362937 (3 : ZMod 84989362937)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (10623670367, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (10623670367, 1)] : List FactorBlock).map factorBlockValue).prod = 84989362937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_10623670367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 84989362937) ^ 42494681468 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 84989362937) ^ 8 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_16997872587401 : Nat.Prime 16997872587401 := by
  apply lucas_primality 16997872587401 (6 : ZMod 16997872587401)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 2), (84989362937, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 2), (84989362937, 1)] : List FactorBlock).map factorBlockValue).prod = 16997872587401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_84989362937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 16997872587401) ^ 8498936293700 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 16997872587401) ^ 3399574517480 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 16997872587401) ^ 200 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_883 : Nat.Prime 883 := by norm_num
private theorem prime_thirtyAB_1535377 : Nat.Prime 1535377 := by norm_num
private theorem prime_thirtyAB_2497849 : Nat.Prime 2497849 := by norm_num
private theorem prime_thirtyAB_571 : Nat.Prime 571 := by norm_num
private theorem prime_thirtyAB_129209 : Nat.Prime 129209 := by norm_num
private theorem prime_thirtyAB_1032896747 : Nat.Prime 1032896747 := by
  apply lucas_primality 1032896747 (2 : ZMod 1032896747)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (571, 1), (129209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (571, 1), (129209, 1)] : List FactorBlock).map factorBlockValue).prod = 1032896747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_571
      · exact prime_thirtyAB_129209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1032896747) ^ 516448373 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032896747) ^ 147556678 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032896747) ^ 1808926 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032896747) ^ 7994 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_13080701940447819211 : Nat.Prime 13080701940447819211 := by
  apply lucas_primality 13080701940447819211 (10 : ZMod 13080701940447819211)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (13, 2), (2497849, 1), (1032896747, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (13, 2), (2497849, 1), (1032896747, 1)] : List FactorBlock).map factorBlockValue).prod = 13080701940447819211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_2497849
      · exact prime_thirtyAB_1032896747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 13080701940447819211) ^ 6540350970223909605 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 4360233980149273070 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 2616140388089563842 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 1006207841572909170 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 5236786507290 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 13080701940447819211) ^ 12664094430 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_859 : Nat.Prime 859 := by norm_num
private theorem prime_thirtyAB_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_thirtyAB_11637001 : Nat.Prime 11637001 := by norm_num
private theorem prime_thirtyAB_269 : Nat.Prime 269 := by norm_num
private theorem prime_thirtyAB_3539743 : Nat.Prime 3539743 := by norm_num
private theorem prime_thirtyAB_17755350889 : Nat.Prime 17755350889 := by
  apply lucas_primality 17755350889 (14 : ZMod 17755350889)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (19, 1), (3539743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (19, 1), (3539743, 1)] : List FactorBlock).map factorBlockValue).prod = 17755350889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_3539743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 17755350889) ^ 8877675444 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 5918450296 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 1614122808 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 934492152 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 5016 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_296123742126743 : Nat.Prime 296123742126743 := by
  apply lucas_primality 296123742126743 (5 : ZMod 296123742126743)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (269, 1), (17755350889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (269, 1), (17755350889, 1)] : List FactorBlock).map factorBlockValue).prod = 296123742126743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_269
      · exact prime_thirtyAB_17755350889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 296123742126743) ^ 148061871063371 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 9552378778282 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 1100831755118 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 16678 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_6891984566505300835487 : Nat.Prime 6891984566505300835487 := by
  apply lucas_primality 6891984566505300835487 (5 : ZMod 6891984566505300835487)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11637001, 1), (296123742126743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11637001, 1), (296123742126743, 1)] : List FactorBlock).map factorBlockValue).prod = 6891984566505300835487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_11637001
      · exact prime_thirtyAB_296123742126743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6891984566505300835487) ^ 3445992283252650417743 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 6891984566505300835487) ^ 592247484253486 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 6891984566505300835487) ^ 23274002 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_thirtyAB_8810759 : Nat.Prime 8810759 := by norm_num
private theorem prime_thirtyAB_173 : Nat.Prime 173 := by norm_num
private theorem prime_thirtyAB_127 : Nat.Prime 127 := by norm_num
private theorem prime_thirtyAB_383 : Nat.Prime 383 := by norm_num
private theorem prime_thirtyAB_132383 : Nat.Prime 132383 := by norm_num
private theorem prime_thirtyAB_45274987 : Nat.Prime 45274987 := by
  apply lucas_primality 45274987 (2 : ZMod 45274987)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (19, 1), (132383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (19, 1), (132383, 1)] : List FactorBlock).map factorBlockValue).prod = 45274987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_132383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45274987) ^ 22637493 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 45274987) ^ 15091662 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 45274987) ^ 2382894 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 45274987) ^ 342 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_13213323856003 : Nat.Prime 13213323856003 := by
  apply lucas_primality 13213323856003 (2 : ZMod 13213323856003)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (127, 1), (383, 1), (45274987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (127, 1), (383, 1), (45274987, 1)] : List FactorBlock).map factorBlockValue).prod = 13213323856003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_127
      · exact prime_thirtyAB_383
      · exact prime_thirtyAB_45274987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13213323856003) ^ 6606661928001 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 4404441285334 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 104041920126 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 34499540094 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 13213323856003) ^ 291846 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_18287240216708153 : Nat.Prime 18287240216708153 := by
  apply lucas_primality 18287240216708153 (3 : ZMod 18287240216708153)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (173, 1), (13213323856003, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (173, 1), (13213323856003, 1)] : List FactorBlock).map factorBlockValue).prod = 18287240216708153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_173
      · exact prime_thirtyAB_13213323856003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 18287240216708153) ^ 9143620108354076 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 18287240216708153) ^ 105706590848024 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 18287240216708153) ^ 1384 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_36574480433416307 : Nat.Prime 36574480433416307 := by
  apply lucas_primality 36574480433416307 (2 : ZMod 36574480433416307)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (18287240216708153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (18287240216708153, 1)] : List FactorBlock).map factorBlockValue).prod = 36574480433416307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_18287240216708153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 36574480433416307) ^ 18287240216708153 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 36574480433416307) ^ 2 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_3866987191788559531764157 : Nat.Prime 3866987191788559531764157 := by
  apply lucas_primality 3866987191788559531764157 (5 : ZMod 3866987191788559531764157)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (8810759, 1), (36574480433416307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (8810759, 1), (36574480433416307, 1)] : List FactorBlock).map factorBlockValue).prod = 3866987191788559531764157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_8810759
      · exact prime_thirtyAB_36574480433416307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3866987191788559531764157) ^ 1933493595894279765882078 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 3866987191788559531764157) ^ 1288995730596186510588052 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 3866987191788559531764157) ^ 438893765200995684 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 3866987191788559531764157) ^ 105729108 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_115903 : Nat.Prime 115903 := by norm_num
private theorem prime_thirtyAB_131 : Nat.Prime 131 := by norm_num
private theorem prime_thirtyAB_149 : Nat.Prime 149 := by norm_num
private theorem prime_thirtyAB_9833 : Nat.Prime 9833 := by norm_num
private theorem prime_thirtyAB_32244294937 : Nat.Prime 32244294937 := by
  apply lucas_primality 32244294937 (10 : ZMod 32244294937)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod = 32244294937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_131
      · exact prime_thirtyAB_149
      · exact prime_thirtyAB_9833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32244294937) ^ 16122147468 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 10748098312 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 4606327848 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 246139656 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 216404664 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 3279192 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_457 : Nat.Prime 457 := by norm_num
private theorem prime_thirtyAB_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_thirtyAB_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_thirtyAB_1898100541591 : Nat.Prime 1898100541591 := by
  apply lucas_primality 1898100541591 (3 : ZMod 1898100541591)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod = 1898100541591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_457
      · exact prime_thirtyAB_1433
      · exact prime_thirtyAB_8783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1898100541591) ^ 949050270795 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 632700180530 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 379620108318 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 172554594690 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 4153392870 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 1324564230 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 216110730 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_143669 : Nat.Prime 143669 := by norm_num
private theorem prime_thirtyAB_349 : Nat.Prime 349 := by norm_num
private theorem prime_thirtyAB_619 : Nat.Prime 619 := by norm_num
private theorem prime_thirtyAB_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_thirtyAB_13852339783 : Nat.Prime 13852339783 := by
  apply lucas_primality 13852339783 (3 : ZMod 13852339783)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod = 13852339783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_349
      · exact prime_thirtyAB_619
      · exact prime_thirtyAB_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13852339783) ^ 6926169891 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 4617446594 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 39691518 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 22378578 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 1296186 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_761 : Nat.Prime 761 := by norm_num
private theorem prime_thirtyAB_89 : Nat.Prime 89 := by norm_num
private theorem prime_thirtyAB_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_thirtyAB_1951572421 : Nat.Prime 1951572421 := by
  apply lucas_primality 1951572421 (10 : ZMod 1951572421)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod = 1951572421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_89
      · exact prime_thirtyAB_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1951572421) ^ 975786210 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 650524140 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 390314484 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 278796060 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 21927780 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 336420 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2970293224763 : Nat.Prime 2970293224763 := by
  apply lucas_primality 2970293224763 (2 : ZMod 2970293224763)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod = 2970293224763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_761
      · exact prime_thirtyAB_1951572421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2970293224763) ^ 1485146612381 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 3903144842 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 1522 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_23827 : Nat.Prime 23827 := by norm_num
private theorem prime_thirtyAB_83 : Nat.Prime 83 := by norm_num
private theorem prime_thirtyAB_2437 : Nat.Prime 2437 := by norm_num
private theorem prime_thirtyAB_1552379 : Nat.Prime 1552379 := by norm_num
private theorem prime_thirtyAB_370919 : Nat.Prime 370919 := by norm_num
private theorem prime_thirtyAB_270029033 : Nat.Prime 270029033 := by
  apply lucas_primality 270029033 (3 : ZMod 270029033)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (13, 1), (370919, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (13, 1), (370919, 1)] : List FactorBlock).map factorBlockValue).prod = 270029033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_370919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 270029033) ^ 135014516 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 270029033) ^ 38575576 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 270029033) ^ 20771464 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 270029033) ^ 728 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_540058067 : Nat.Prime 540058067 := by
  apply lucas_primality 540058067 (2 : ZMod 540058067)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (270029033, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (270029033, 1)] : List FactorBlock).map factorBlockValue).prod = 540058067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_270029033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 540058067) ^ 270029033 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 540058067) ^ 2 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_212651952605295721092763 : Nat.Prime 212651952605295721092763 := by
  apply lucas_primality 212651952605295721092763 (11 : ZMod 212651952605295721092763)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (19, 1), (83, 1), (2437, 1), (1552379, 1), (540058067, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (19, 1), (83, 1), (2437, 1), (1552379, 1), (540058067, 1)] : List FactorBlock).map factorBlockValue).prod = 212651952605295721092763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_83
      · exact prime_thirtyAB_2437
      · exact prime_thirtyAB_1552379
      · exact prime_thirtyAB_540058067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 212651952605295721092763) ^ 106325976302647860546381 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 212651952605295721092763) ^ 70883984201765240364254 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 212651952605295721092763) ^ 19331995691390520099342 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 212651952605295721092763) ^ 11192208031857669531198 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 212651952605295721092763) ^ 2562071718136093025214 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 212651952605295721092763) ^ 87259726140868166226 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 212651952605295721092763) ^ 136984558928776878 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 212651952605295721092763) ^ 393757570897086 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_241 : Nat.Prime 241 := by norm_num
private theorem prime_thirtyAB_1701391 : Nat.Prime 1701391 := by norm_num
private theorem prime_thirtyAB_11484449 : Nat.Prime 11484449 := by norm_num
private theorem prime_thirtyAB_257 : Nat.Prime 257 := by norm_num
private theorem prime_thirtyAB_1896161 : Nat.Prime 1896161 := by norm_num
private theorem prime_thirtyAB_1831691527 : Nat.Prime 1831691527 := by
  apply lucas_primality 1831691527 (5 : ZMod 1831691527)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (23, 1), (1896161, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (23, 1), (1896161, 1)] : List FactorBlock).map factorBlockValue).prod = 1831691527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_1896161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1831691527) ^ 915845763 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 610563842 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 261670218 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 79638762 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1831691527) ^ 966 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_941489444879 : Nat.Prime 941489444879 := by
  apply lucas_primality 941489444879 (7 : ZMod 941489444879)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (257, 1), (1831691527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (257, 1), (1831691527, 1)] : List FactorBlock).map factorBlockValue).prod = 941489444879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_257
      · exact prime_thirtyAB_1831691527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 941489444879) ^ 470744722439 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 941489444879) ^ 3663383054 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 941489444879) ^ 514 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_374681 : Nat.Prime 374681 := by norm_num
private theorem prime_thirtyAB_281 : Nat.Prime 281 := by norm_num
private theorem prime_thirtyAB_27212041 : Nat.Prime 27212041 := by
  apply lucas_primality 27212041 (7 : ZMod 27212041)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 1), (269, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 1), (269, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod = 27212041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_269
      · exact prime_thirtyAB_281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 27212041) ^ 13606020 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 27212041) ^ 9070680 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 27212041) ^ 5442408 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 27212041) ^ 101160 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 27212041) ^ 96840 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_19073 : Nat.Prime 19073 := by norm_num
private theorem prime_thirtyAB_163646341 : Nat.Prime 163646341 := by
  apply lucas_primality 163646341 (7 : ZMod 163646341)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (19073, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (19073, 1)] : List FactorBlock).map factorBlockValue).prod = 163646341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_19073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 163646341) ^ 81823170 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 54548780 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 32729268 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 14876940 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 12588180 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 8580 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_219613389623 : Nat.Prime 219613389623 := by
  apply lucas_primality 219613389623 (5 : ZMod 219613389623)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (61, 1), (163646341, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (61, 1), (163646341, 1)] : List FactorBlock).map factorBlockValue).prod = 219613389623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_61
      · exact prime_thirtyAB_163646341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 219613389623) ^ 109806694811 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 19964853602 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 3600219502 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 1342 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_386519565736481 : Nat.Prime 386519565736481 := by
  apply lucas_primality 386519565736481 (3 : ZMod 386519565736481)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 1), (11, 1), (219613389623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 1), (11, 1), (219613389623, 1)] : List FactorBlock).map factorBlockValue).prod = 386519565736481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_219613389623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 386519565736481) ^ 193259782868240 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 77303913147296 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 35138142339680 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 1760 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_71 : Nat.Prime 71 := by norm_num
private theorem prime_thirtyAB_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_thirtyAB_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_71
      · exact prime_thirtyAB_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_thirtyAB_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_thirtyAB_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_81047
      · exact prime_thirtyAB_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_3224364229371333456849168001 : Nat.Prime 3224364229371333456849168001 := by
  apply lucas_primality 3224364229371333456849168001 (44 : ZMod 3224364229371333456849168001)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 4), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 4), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 3224364229371333456849168001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (44 : ZMod 3224364229371333456849168001) ^ 1612182114685666728424584000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 1074788076457111152283056000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 644872845874266691369833600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 460623461338761922407024000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 248028017643948727449936000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 189668484080666673932304000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 169703380493228076676272000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 140189749103101454645616000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 111184973426597705408592000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 104011749334559143769328000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 87144979172198201536464000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 78643029984666669679248000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 74985214636542638531376000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 68603494241943265039344000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 60837060931534593525456000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 54650241175785312827952000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (44 : ZMod 3224364229371333456849168001) ^ 52858429989693991095888000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_223 : Nat.Prime 223 := by norm_num
private theorem prime_thirtyAB_5113 : Nat.Prime 5113 := by norm_num
private theorem prime_thirtyAB_101287 : Nat.Prime 101287 := by norm_num
private theorem prime_thirtyAB_656951 : Nat.Prime 656951 := by norm_num
private theorem prime_thirtyAB_2669767 : Nat.Prime 2669767 := by norm_num
private theorem prime_thirtyAB_42716273 : Nat.Prime 42716273 := by
  apply lucas_primality 42716273 (3 : ZMod 42716273)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod = 42716273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_2669767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42716273) ^ 21358136 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 42716273) ^ 16 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_25592998416424177 : Nat.Prime 25592998416424177 := by
  apply lucas_primality 25592998416424177 (5 : ZMod 25592998416424177)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod = 25592998416424177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_656951
      · exact prime_thirtyAB_42716273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25592998416424177) ^ 12796499208212088 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 8530999472141392 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 1346999916653904 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 38957240976 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 599139312 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_173219 : Nat.Prime 173219 := by norm_num
private theorem prime_thirtyAB_67901849 : Nat.Prime 67901849 := by
  apply lucas_primality 67901849 (3 : ZMod 67901849)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 2), (173219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 2), (173219, 1)] : List FactorBlock).map factorBlockValue).prod = 67901849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_173219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 67901849) ^ 33950924 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 67901849) ^ 9700264 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 67901849) ^ 392 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2003 : Nat.Prime 2003 := by norm_num
private theorem prime_thirtyAB_158803 : Nat.Prime 158803 := by norm_num
private theorem prime_thirtyAB_282671 : Nat.Prime 282671 := by norm_num
private theorem prime_thirtyAB_322244941 : Nat.Prime 322244941 := by
  apply lucas_primality 322244941 (2 : ZMod 322244941)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (19, 1), (282671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (19, 1), (282671, 1)] : List FactorBlock).map factorBlockValue).prod = 322244941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_282671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 322244941) ^ 161122470 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 322244941) ^ 107414980 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 322244941) ^ 64448988 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 322244941) ^ 16960260 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 322244941) ^ 1140 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_40180175271566404649 : Nat.Prime 40180175271566404649 := by
  apply lucas_primality 40180175271566404649 (3 : ZMod 40180175271566404649)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 2), (2003, 1), (158803, 1), (322244941, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 2), (2003, 1), (158803, 1), (322244941, 1)] : List FactorBlock).map factorBlockValue).prod = 40180175271566404649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_2003
      · exact prime_thirtyAB_158803
      · exact prime_thirtyAB_322244941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40180175271566404649) ^ 20090087635783202324 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 40180175271566404649) ^ 5740025038795200664 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 40180175271566404649) ^ 20059997639324216 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 40180175271566404649) ^ 253018993794616 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 40180175271566404649) ^ 124688304328 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_60607 : Nat.Prime 60607 := by norm_num
private theorem prime_thirtyAB_5301391 : Nat.Prime 5301391 := by norm_num
private theorem prime_thirtyAB_275672333 : Nat.Prime 275672333 := by
  apply lucas_primality 275672333 (3 : ZMod 275672333)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (5301391, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (5301391, 1)] : List FactorBlock).map factorBlockValue).prod = 275672333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_5301391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 275672333) ^ 137836166 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 275672333) ^ 21205564 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 275672333) ^ 52 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_56779 : Nat.Prime 56779 := by norm_num
private theorem prime_thirtyAB_27481037 : Nat.Prime 27481037 := by
  apply lucas_primality 27481037 (2 : ZMod 27481037)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 2), (56779, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 2), (56779, 1)] : List FactorBlock).map factorBlockValue).prod = 27481037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_56779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27481037) ^ 13740518 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 27481037) ^ 2498276 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 27481037) ^ 484 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1157501278441 : Nat.Prime 1157501278441 := by
  apply lucas_primality 1157501278441 (11 : ZMod 1157501278441)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 4), (5, 1), (13, 1), (27481037, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 4), (5, 1), (13, 1), (27481037, 1)] : List FactorBlock).map factorBlockValue).prod = 1157501278441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_27481037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1157501278441) ^ 578750639220 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 385833759480 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 231500255688 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 89038559880 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 1157501278441) ^ 42120 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_thirtyAB_439 : Nat.Prime 439 := by norm_num
private theorem prime_thirtyAB_853 : Nat.Prime 853 := by norm_num
private theorem prime_thirtyAB_151 : Nat.Prime 151 := by norm_num
private theorem prime_thirtyAB_479 : Nat.Prime 479 := by norm_num
private theorem prime_thirtyAB_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_thirtyAB_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_151
      · exact prime_thirtyAB_479
      · exact prime_thirtyAB_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_439
      · exact prime_thirtyAB_853
      · exact prime_thirtyAB_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_211 : Nat.Prime 211 := by norm_num
private theorem prime_thirtyAB_28751 : Nat.Prime 28751 := by norm_num
private theorem prime_thirtyAB_75389 : Nat.Prime 75389 := by norm_num
private theorem prime_thirtyAB_503 : Nat.Prime 503 := by norm_num
private theorem prime_thirtyAB_13901 : Nat.Prime 13901 := by norm_num
private theorem prime_thirtyAB_13913 : Nat.Prime 13913 := by norm_num
private theorem prime_thirtyAB_66917996099 : Nat.Prime 66917996099 := by
  apply lucas_primality 66917996099 (2 : ZMod 66917996099)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (173, 1), (13901, 1), (13913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (173, 1), (13901, 1), (13913, 1)] : List FactorBlock).map factorBlockValue).prod = 66917996099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_173
      · exact prime_thirtyAB_13901
      · exact prime_thirtyAB_13913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66917996099) ^ 33458998049 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 66917996099) ^ 386809226 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 66917996099) ^ 4813898 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 66917996099) ^ 4809746 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_4847004293442769 : Nat.Prime 4847004293442769 := by
  apply lucas_primality 4847004293442769 (7 : ZMod 4847004293442769)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (503, 1), (66917996099, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (503, 1), (66917996099, 1)] : List FactorBlock).map factorBlockValue).prod = 4847004293442769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_503
      · exact prime_thirtyAB_66917996099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4847004293442769) ^ 2423502146721384 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 4847004293442769) ^ 1615668097814256 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 4847004293442769) ^ 9636191438256 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 4847004293442769) ^ 72432 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_thirtyAB_109063 : Nat.Prime 109063 := by norm_num
private theorem prime_thirtyAB_116411 : Nat.Prime 116411 := by norm_num
private theorem prime_thirtyAB_2321369 : Nat.Prime 2321369 := by norm_num
private theorem prime_thirtyAB_5405471 : Nat.Prime 5405471 := by norm_num
private theorem prime_thirtyAB_43243769 : Nat.Prime 43243769 := by
  apply lucas_primality 43243769 (3 : ZMod 43243769)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5405471, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5405471, 1)] : List FactorBlock).map factorBlockValue).prod = 43243769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5405471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 43243769) ^ 21621884 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 43243769) ^ 8 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_73 : Nat.Prime 73 := by norm_num
private theorem prime_thirtyAB_13737811 : Nat.Prime 13737811 := by norm_num
private theorem prime_thirtyAB_3439229 : Nat.Prime 3439229 := by norm_num
private theorem prime_thirtyAB_68784581 : Nat.Prime 68784581 := by
  apply lucas_primality 68784581 (3 : ZMod 68784581)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod = 68784581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68784581) ^ 34392290 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 13756916 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 20 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_15558227 : Nat.Prime 15558227 := by norm_num
private theorem prime_thirtyAB_840144259 : Nat.Prime 840144259 := by
  apply lucas_primality 840144259 (2 : ZMod 840144259)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod = 840144259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_15558227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 840144259) ^ 420072129 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 280048086 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 54 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_28564904807 : Nat.Prime 28564904807 := by
  apply lucas_primality 28564904807 (5 : ZMod 28564904807)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod = 28564904807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_840144259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28564904807) ^ 14282452403 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 1680288518 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 34 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_235441 : Nat.Prime 235441 := by norm_num
private theorem prime_thirtyAB_243916877 : Nat.Prime 243916877 := by
  apply lucas_primality 243916877 (2 : ZMod 243916877)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (37, 1), (235441, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (37, 1), (235441, 1)] : List FactorBlock).map factorBlockValue).prod = 243916877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_235441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243916877) ^ 121958438 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 243916877) ^ 34845268 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 243916877) ^ 6592348 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 243916877) ^ 1036 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_10058219 : Nat.Prime 10058219 := by norm_num
private theorem prime_thirtyAB_3701424593 : Nat.Prime 3701424593 := by
  apply lucas_primality 3701424593 (3 : ZMod 3701424593)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (23, 1), (10058219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (23, 1), (10058219, 1)] : List FactorBlock).map factorBlockValue).prod = 3701424593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_10058219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3701424593) ^ 1850712296 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 3701424593) ^ 160931504 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 3701424593) ^ 368 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_7402849187 : Nat.Prime 7402849187 := by
  apply lucas_primality 7402849187 (2 : ZMod 7402849187)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3701424593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3701424593, 1)] : List FactorBlock).map factorBlockValue).prod = 7402849187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3701424593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7402849187) ^ 3701424593 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7402849187) ^ 2 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_199654842573391 : Nat.Prime 199654842573391 := by
  apply lucas_primality 199654842573391 (3 : ZMod 199654842573391)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (7402849187, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (7402849187, 1)] : List FactorBlock).map factorBlockValue).prod = 199654842573391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_7402849187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 199654842573391) ^ 99827421286695 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 199654842573391) ^ 66551614191130 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 199654842573391) ^ 39930968514678 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 199654842573391) ^ 6884649743910 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 199654842573391) ^ 6440478792690 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 199654842573391) ^ 26970 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_7653169425523223813 : Nat.Prime 7653169425523223813 := by
  apply lucas_primality 7653169425523223813 (2 : ZMod 7653169425523223813)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (37, 2), (199654842573391, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (37, 2), (199654842573391, 1)] : List FactorBlock).map factorBlockValue).prod = 7653169425523223813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_199654842573391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7653169425523223813) ^ 3826584712761611906 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7653169425523223813) ^ 1093309917931889116 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7653169425523223813) ^ 206842416906033076 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7653169425523223813) ^ 38332 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_thirtyAB_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_thirtyAB_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_thirtyAB_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_thirtyAB_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_thirtyAB_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_149
      · exact prime_thirtyAB_1429
      · exact prime_thirtyAB_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_673 : Nat.Prime 673 := by norm_num
private theorem prime_thirtyAB_872203 : Nat.Prime 872203 := by norm_num
private theorem prime_thirtyAB_29654903 : Nat.Prime 29654903 := by
  apply lucas_primality 29654903 (10 : ZMod 29654903)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (872203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (872203, 1)] : List FactorBlock).map factorBlockValue).prod = 29654903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_872203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 29654903) ^ 14827451 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 29654903) ^ 1744406 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 29654903) ^ 34 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_889647091 : Nat.Prime 889647091 := by
  apply lucas_primality 889647091 (3 : ZMod 889647091)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (29654903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (29654903, 1)] : List FactorBlock).map factorBlockValue).prod = 889647091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_29654903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 889647091) ^ 444823545 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 296549030 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 177929418 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 30 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_317 : Nat.Prime 317 := by norm_num
private theorem prime_thirtyAB_30871 : Nat.Prime 30871 := by norm_num
private theorem prime_thirtyAB_1044397 : Nat.Prime 1044397 := by norm_num
private theorem prime_thirtyAB_1483112670203 : Nat.Prime 1483112670203 := by
  apply lucas_primality 1483112670203 (2 : ZMod 1483112670203)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (30871, 1), (1044397, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (30871, 1), (1044397, 1)] : List FactorBlock).map factorBlockValue).prod = 1483112670203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_30871
      · exact prime_thirtyAB_1044397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1483112670203) ^ 741556335101 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 64483159574 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 48042262 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 1420066 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2820880298726107 : Nat.Prime 2820880298726107 := by
  apply lucas_primality 2820880298726107 (3 : ZMod 2820880298726107)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (317, 1), (1483112670203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (317, 1), (1483112670203, 1)] : List FactorBlock).map factorBlockValue).prod = 2820880298726107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_317
      · exact prime_thirtyAB_1483112670203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2820880298726107) ^ 1410440149363053 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 940293432908702 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 8898676021218 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 1902 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_499 : Nat.Prime 499 := by norm_num
private theorem prime_thirtyAB_375101 : Nat.Prime 375101 := by norm_num
private theorem prime_thirtyAB_433 : Nat.Prime 433 := by norm_num
private theorem prime_thirtyAB_4789 : Nat.Prime 4789 := by norm_num
private theorem prime_thirtyAB_7910317 : Nat.Prime 7910317 := by norm_num
private theorem prime_thirtyAB_16744068585947 : Nat.Prime 16744068585947 := by
  apply lucas_primality 16744068585947 (2 : ZMod 16744068585947)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (17, 1), (4789, 1), (7910317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (17, 1), (4789, 1), (7910317, 1)] : List FactorBlock).map factorBlockValue).prod = 16744068585947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_4789
      · exact prime_thirtyAB_7910317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16744068585947) ^ 8372034292973 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 1288005275842 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 984945210938 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 3496360114 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744068585947) ^ 2116738 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_783019623353225509 : Nat.Prime 783019623353225509 := by
  apply lucas_primality 783019623353225509 (2 : ZMod 783019623353225509)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (433, 1), (16744068585947, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (433, 1), (16744068585947, 1)] : List FactorBlock).map factorBlockValue).prod = 783019623353225509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_433
      · exact prime_thirtyAB_16744068585947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 783019623353225509) ^ 391509811676612754 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 783019623353225509) ^ 261006541117741836 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 783019623353225509) ^ 1808359407282276 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 783019623353225509) ^ 46764 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_4297 : Nat.Prime 4297 := by norm_num
private theorem prime_thirtyAB_179 : Nat.Prime 179 := by norm_num
private theorem prime_thirtyAB_23609743 : Nat.Prime 23609743 := by
  apply lucas_primality 23609743 (3 : ZMod 23609743)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (19, 1), (89, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (19, 1), (89, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod = 23609743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_89
      · exact prime_thirtyAB_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23609743) ^ 11804871 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 23609743) ^ 7869914 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 23609743) ^ 1816134 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 23609743) ^ 1242618 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 23609743) ^ 265278 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 23609743) ^ 131898 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_7101574596971 : Nat.Prime 7101574596971 := by
  apply lucas_primality 7101574596971 (2 : ZMod 7101574596971)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (4297, 1), (23609743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (4297, 1), (23609743, 1)] : List FactorBlock).map factorBlockValue).prod = 7101574596971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_4297
      · exact prime_thirtyAB_23609743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7101574596971) ^ 3550787298485 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7101574596971) ^ 1420314919394 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7101574596971) ^ 1014510656710 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7101574596971) ^ 1652682010 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7101574596971) ^ 300790 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_135601 : Nat.Prime 135601 := by norm_num
private theorem prime_thirtyAB_9461 : Nat.Prime 9461 := by norm_num
private theorem prime_thirtyAB_22876699 : Nat.Prime 22876699 := by
  apply lucas_primality 22876699 (10 : ZMod 22876699)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (31, 1), (9461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (31, 1), (9461, 1)] : List FactorBlock).map factorBlockValue).prod = 22876699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_9461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 22876699) ^ 11438349 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 22876699) ^ 7625566 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 22876699) ^ 1759746 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 22876699) ^ 737958 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 22876699) ^ 2418 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_217147228276931 : Nat.Prime 217147228276931 := by
  apply lucas_primality 217147228276931 (2 : ZMod 217147228276931)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (135601, 1), (22876699, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (135601, 1), (22876699, 1)] : List FactorBlock).map factorBlockValue).prod = 217147228276931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_135601
      · exact prime_thirtyAB_22876699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 217147228276931) ^ 108573614138465 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 217147228276931) ^ 43429445655386 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 217147228276931) ^ 31021032610990 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 217147228276931) ^ 1601368930 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 217147228276931) ^ 9492070 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1477833605128527834389202001 : Nat.Prime 1477833605128527834389202001 := by
  apply lucas_primality 1477833605128527834389202001 (107 : ZMod 1477833605128527834389202001)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 1477833605128527834389202001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1477833605128527834389202001) ^ 738916802564263917194601000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 492611201709509278129734000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 295566721025705566877840400 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 211119086446932547769886000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 134348509557138894035382000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 113679508086809833414554000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 86931388536972225552306000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 77780716059396201809958000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 64253635005588166712574000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 50959779487190614978938000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 47672051778339607560942000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 39941448787257509037546000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 36044722076305556936322000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 34368223375082042660214000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 31443268194223996476366000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 27883652926953355365834000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 25048027205568268379478000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 24226780411943079252282000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_139537 : Nat.Prime 139537 := by norm_num
private theorem prime_thirtyAB_5879 : Nat.Prime 5879 := by norm_num
private theorem prime_thirtyAB_175593973 : Nat.Prime 175593973 := by
  apply lucas_primality 175593973 (5 : ZMod 175593973)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod = 175593973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_131
      · exact prime_thirtyAB_5879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 175593973) ^ 87796986 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 58531324 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 9241788 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 1340412 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 29868 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_229 : Nat.Prime 229 := by norm_num
private theorem prime_thirtyAB_372958561 : Nat.Prime 372958561 := by
  apply lucas_primality 372958561 (11 : ZMod 372958561)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod = 372958561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 372958561) ^ 186479280 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 124319520 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 74591712 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 28689120 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 12860640 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 1628640 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_55197867029 : Nat.Prime 55197867029 := by
  apply lucas_primality 55197867029 (2 : ZMod 55197867029)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod = 55197867029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_372958561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55197867029) ^ 27598933514 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 1491834244 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 148 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_887599 : Nat.Prime 887599 := by norm_num
private theorem prime_thirtyAB_3448607 : Nat.Prime 3448607 := by norm_num
private theorem prime_thirtyAB_1779481213 : Nat.Prime 1779481213 := by
  apply lucas_primality 1779481213 (2 : ZMod 1779481213)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (43, 1), (3448607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (43, 1), (3448607, 1)] : List FactorBlock).map factorBlockValue).prod = 1779481213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_3448607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1779481213) ^ 889740606 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1779481213) ^ 593160404 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1779481213) ^ 41383284 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1779481213) ^ 516 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_6759017 : Nat.Prime 6759017 := by norm_num
private theorem prime_thirtyAB_3771531487 : Nat.Prime 3771531487 := by
  apply lucas_primality 3771531487 (3 : ZMod 3771531487)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (31, 1), (6759017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (31, 1), (6759017, 1)] : List FactorBlock).map factorBlockValue).prod = 3771531487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_6759017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3771531487) ^ 1885765743 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771531487) ^ 1257177162 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771531487) ^ 121662306 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 3771531487) ^ 558 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_thirtyAB_3509741 : Nat.Prime 3509741 := by norm_num
private theorem prime_thirtyAB_237841108607 : Nat.Prime 237841108607 := by
  apply lucas_primality 237841108607 (5 : ZMod 237841108607)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (1093, 1), (3509741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (1093, 1), (3509741, 1)] : List FactorBlock).map factorBlockValue).prod = 237841108607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_1093
      · exact prime_thirtyAB_3509741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 237841108607) ^ 118920554303 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 7672293826 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 217603942 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 67766 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_101 : Nat.Prime 101 := by norm_num
private theorem prime_thirtyAB_463 : Nat.Prime 463 := by norm_num
private theorem prime_thirtyAB_631 : Nat.Prime 631 := by norm_num
private theorem prime_thirtyAB_97387 : Nat.Prime 97387 := by norm_num
private theorem prime_thirtyAB_5523140549247743 : Nat.Prime 5523140549247743 := by
  apply lucas_primality 5523140549247743 (5 : ZMod 5523140549247743)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 2), (101, 1), (463, 1), (631, 1), (97387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 2), (101, 1), (463, 1), (631, 1), (97387, 1)] : List FactorBlock).map factorBlockValue).prod = 5523140549247743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_101
      · exact prime_thirtyAB_463
      · exact prime_thirtyAB_631
      · exact prime_thirtyAB_97387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5523140549247743) ^ 2761570274623871 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 178165824169282 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 54684559893542 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 11929029264034 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 8752996116082 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 56713324666 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_36587 : Nat.Prime 36587 := by norm_num
private theorem prime_thirtyAB_347 : Nat.Prime 347 := by norm_num
private theorem prime_thirtyAB_787 : Nat.Prime 787 := by norm_num
private theorem prime_thirtyAB_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_thirtyAB_38559853 : Nat.Prime 38559853 := by
  apply lucas_primality 38559853 (5 : ZMod 38559853)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (787, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (787, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod = 38559853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_787
      · exact prime_thirtyAB_1361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 38559853) ^ 19279926 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 38559853) ^ 12853284 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 38559853) ^ 48996 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 38559853) ^ 28332 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_107042151929 : Nat.Prime 107042151929 := by
  apply lucas_primality 107042151929 (3 : ZMod 107042151929)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (347, 1), (38559853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (347, 1), (38559853, 1)] : List FactorBlock).map factorBlockValue).prod = 107042151929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_347
      · exact prime_thirtyAB_38559853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 107042151929) ^ 53521075964 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 107042151929) ^ 308478824 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 107042151929) ^ 2776 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_thirtyAB_1610561 : Nat.Prime 1610561 := by norm_num
private theorem prime_thirtyAB_323442523387 : Nat.Prime 323442523387 := by
  apply lucas_primality 323442523387 (2 : ZMod 323442523387)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (3719, 1), (1610561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (3719, 1), (1610561, 1)] : List FactorBlock).map factorBlockValue).prod = 323442523387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_3719
      · exact prime_thirtyAB_1610561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 323442523387) ^ 161721261693 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 323442523387) ^ 107814174462 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 323442523387) ^ 86970294 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 323442523387) ^ 200826 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_97 : Nat.Prime 97 := by norm_num
private theorem prime_thirtyAB_6337 : Nat.Prime 6337 := by norm_num
private theorem prime_thirtyAB_52879 : Nat.Prime 52879 := by norm_num
private theorem prime_thirtyAB_13121 : Nat.Prime 13121 := by norm_num
private theorem prime_thirtyAB_67783087 : Nat.Prime 67783087 := by
  apply lucas_primality 67783087 (3 : ZMod 67783087)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (41, 1), (13121, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (41, 1), (13121, 1)] : List FactorBlock).map factorBlockValue).prod = 67783087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_13121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67783087) ^ 33891543 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 67783087) ^ 22594362 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 67783087) ^ 9683298 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 67783087) ^ 1653246 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 67783087) ^ 5166 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1419383535559309 : Nat.Prime 1419383535559309 := by
  apply lucas_primality 1419383535559309 (13 : ZMod 1419383535559309)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (11, 1), (52879, 1), (67783087, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (11, 1), (52879, 1), (67783087, 1)] : List FactorBlock).map factorBlockValue).prod = 1419383535559309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_52879
      · exact prime_thirtyAB_67783087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1419383535559309) ^ 709691767779654 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 1419383535559309) ^ 473127845186436 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 1419383535559309) ^ 129034866869028 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 1419383535559309) ^ 26842102452 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 1419383535559309) ^ 20940084 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_131339637853584059224067 : Nat.Prime 131339637853584059224067 := by
  apply lucas_primality 131339637853584059224067 (2 : ZMod 131339637853584059224067)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 2), (149, 1), (6337, 1), (1419383535559309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 2), (149, 1), (6337, 1), (1419383535559309, 1)] : List FactorBlock).map factorBlockValue).prod = 131339637853584059224067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_149
      · exact prime_thirtyAB_6337
      · exact prime_thirtyAB_1419383535559309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 131339637853584059224067) ^ 65669818926792029612033 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 131339637853584059224067) ^ 18762805407654865603438 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 131339637853584059224067) ^ 881474079554255431034 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 131339637853584059224067) ^ 20725838386237030018 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 131339637853584059224067) ^ 92532874 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_12608605233944069685510433 : Nat.Prime 12608605233944069685510433 := by
  apply lucas_primality 12608605233944069685510433 (5 : ZMod 12608605233944069685510433)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (131339637853584059224067, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (131339637853584059224067, 1)] : List FactorBlock).map factorBlockValue).prod = 12608605233944069685510433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_131339637853584059224067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12608605233944069685510433) ^ 6304302616972034842755216 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 12608605233944069685510433) ^ 4202868411314689895170144 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 12608605233944069685510433) ^ 96 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_103 : Nat.Prime 103 := by norm_num
private theorem prime_thirtyAB_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_thirtyAB_107 : Nat.Prime 107 := by norm_num
private theorem prime_thirtyAB_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_thirtyAB_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_thirtyAB_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_thirtyAB_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_35279
      · exact prime_thirtyAB_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_61717
      · exact prime_thirtyAB_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_107
      · exact prime_thirtyAB_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_35671 : Nat.Prime 35671 := by norm_num
private theorem prime_thirtyAB_191909981 : Nat.Prime 191909981 := by
  apply lucas_primality 191909981 (2 : ZMod 191909981)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (269, 1), (35671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (269, 1), (35671, 1)] : List FactorBlock).map factorBlockValue).prod = 191909981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_269
      · exact prime_thirtyAB_35671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 191909981) ^ 95954990 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 191909981) ^ 38381996 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 191909981) ^ 713420 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 191909981) ^ 5380 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_577 : Nat.Prime 577 := by norm_num
private theorem prime_thirtyAB_6091 : Nat.Prime 6091 := by norm_num
private theorem prime_thirtyAB_913337 : Nat.Prime 913337 := by norm_num
private theorem prime_thirtyAB_1123404511 : Nat.Prime 1123404511 := by
  apply lucas_primality 1123404511 (3 : ZMod 1123404511)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (41, 1), (913337, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (41, 1), (913337, 1)] : List FactorBlock).map factorBlockValue).prod = 1123404511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_913337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1123404511) ^ 561702255 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1123404511) ^ 374468170 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1123404511) ^ 224680902 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1123404511) ^ 27400110 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1123404511) ^ 1230 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_39482130177410771 : Nat.Prime 39482130177410771 := by
  apply lucas_primality 39482130177410771 (10 : ZMod 39482130177410771)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (577, 1), (6091, 1), (1123404511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (577, 1), (6091, 1), (1123404511, 1)] : List FactorBlock).map factorBlockValue).prod = 39482130177410771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_577
      · exact prime_thirtyAB_6091
      · exact prime_thirtyAB_1123404511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 39482130177410771) ^ 19741065088705385 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 39482130177410771) ^ 7896426035482154 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 39482130177410771) ^ 68426568765010 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 39482130177410771) ^ 6482044028470 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 39482130177410771) ^ 35145070 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_406247 : Nat.Prime 406247 := by norm_num
private theorem prime_thirtyAB_11909399 : Nat.Prime 11909399 := by norm_num
private theorem prime_thirtyAB_20101 : Nat.Prime 20101 := by norm_num
private theorem prime_thirtyAB_775937 : Nat.Prime 775937 := by norm_num
private theorem prime_thirtyAB_93582657823 : Nat.Prime 93582657823 := by
  apply lucas_primality 93582657823 (3 : ZMod 93582657823)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (20101, 1), (775937, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (20101, 1), (775937, 1)] : List FactorBlock).map factorBlockValue).prod = 93582657823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_20101
      · exact prime_thirtyAB_775937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 93582657823) ^ 46791328911 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 93582657823) ^ 31194219274 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 93582657823) ^ 4655622 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 93582657823) ^ 120606 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_19090862195893 : Nat.Prime 19090862195893 := by
  apply lucas_primality 19090862195893 (2 : ZMod 19090862195893)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (93582657823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (93582657823, 1)] : List FactorBlock).map factorBlockValue).prod = 19090862195893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_93582657823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19090862195893) ^ 9545431097946 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 19090862195893) ^ 6363620731964 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 19090862195893) ^ 1122991893876 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 19090862195893) ^ 204 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_229090346350717 : Nat.Prime 229090346350717 := by
  apply lucas_primality 229090346350717 (2 : ZMod 229090346350717)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19090862195893, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19090862195893, 1)] : List FactorBlock).map factorBlockValue).prod = 229090346350717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_19090862195893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 229090346350717) ^ 114545173175358 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 229090346350717) ^ 76363448783572 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 229090346350717) ^ 12 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1074788076457111152283056001 : Nat.Prime 1074788076457111152283056001 := by
  apply lucas_primality 1074788076457111152283056001 (67 : ZMod 1074788076457111152283056001)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 3), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 3), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 1074788076457111152283056001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 1074788076457111152283056001) ^ 537394038228555576141528000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 358262692152370384094352000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 214957615291422230456611200 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 153541153779587307469008000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 82676005881316242483312000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 63222828026888891310768000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 56567793497742692225424000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 46729916367700484881872000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 37061657808865901802864000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 34670583111519714589776000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 29048326390732733845488000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 26214343328222223226416000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 24995071545514212843792000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 22867831413981088346448000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 20279020310511531175152000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 18216747058595104275984000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 17619476663231330365296000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_42466681 : Nat.Prime 42466681 := by
  apply lucas_primality 42466681 (7 : ZMod 42466681)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 5), (5, 1), (17, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 5), (5, 1), (17, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod = 42466681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 42466681) ^ 21233340 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 14155560 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 8493336 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 2498040 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 42466681) ^ 165240 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_29811610063 : Nat.Prime 29811610063 := by
  apply lucas_primality 29811610063 (3 : ZMod 29811610063)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (13, 1), (42466681, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (13, 1), (42466681, 1)] : List FactorBlock).map factorBlockValue).prod = 29811610063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_42466681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29811610063) ^ 14905805031 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 29811610063) ^ 9937203354 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 29811610063) ^ 2293200774 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 29811610063) ^ 702 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_79 : Nat.Prime 79 := by norm_num
private theorem prime_thirtyAB_5283683 : Nat.Prime 5283683 := by norm_num
private theorem prime_thirtyAB_285318883 : Nat.Prime 285318883 := by
  apply lucas_primality 285318883 (2 : ZMod 285318883)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5283683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5283683, 1)] : List FactorBlock).map factorBlockValue).prod = 285318883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5283683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 285318883) ^ 142659441 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 285318883) ^ 95106294 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 285318883) ^ 54 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_90160767029 : Nat.Prime 90160767029 := by
  apply lucas_primality 90160767029 (2 : ZMod 90160767029)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (79, 1), (285318883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (79, 1), (285318883, 1)] : List FactorBlock).map factorBlockValue).prod = 90160767029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_79
      · exact prime_thirtyAB_285318883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90160767029) ^ 45080383514 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 90160767029) ^ 1141275532 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 90160767029) ^ 316 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2704823010871 : Nat.Prime 2704823010871 := by
  apply lucas_primality 2704823010871 (13 : ZMod 2704823010871)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (90160767029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (90160767029, 1)] : List FactorBlock).map factorBlockValue).prod = 2704823010871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_90160767029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2704823010871) ^ 1352411505435 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 2704823010871) ^ 901607670290 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 2704823010871) ^ 540964602174 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 2704823010871) ^ 30 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_331 : Nat.Prime 331 := by norm_num
private theorem prime_thirtyAB_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_thirtyAB_199 : Nat.Prime 199 := by norm_num
private theorem prime_thirtyAB_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_thirtyAB_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_thirtyAB_4121269 : Nat.Prime 4121269 := by norm_num
private theorem prime_thirtyAB_123638071 : Nat.Prime 123638071 := by
  apply lucas_primality 123638071 (7 : ZMod 123638071)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod = 123638071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_4121269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 123638071) ^ 61819035 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 41212690 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 24727614 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 30 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_741828427 : Nat.Prime 741828427 := by
  apply lucas_primality 741828427 (2 : ZMod 741828427)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod = 741828427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_123638071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 741828427) ^ 370914213 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 247276142 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 6 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_429449525106920937499 : Nat.Prime 429449525106920937499 := by
  apply lucas_primality 429449525106920937499 (2 : ZMod 429449525106920937499)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod = 429449525106920937499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_199
      · exact prime_thirtyAB_5449
      · exact prime_thirtyAB_8089
      · exact prime_thirtyAB_741828427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 429449525106920937499) ^ 214724762553460468749 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 143149841702306979166 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 39040865918810994318 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 2158037814607642902 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 78812539017603402 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 53090558178627882 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 578906805774 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_283 : Nat.Prime 283 := by norm_num
private theorem prime_thirtyAB_613 : Nat.Prime 613 := by norm_num
private theorem prime_thirtyAB_85303 : Nat.Prime 85303 := by norm_num
private theorem prime_thirtyAB_381559 : Nat.Prime 381559 := by norm_num
private theorem prime_thirtyAB_2227409 : Nat.Prime 2227409 := by norm_num
private theorem prime_thirtyAB_5099327703787 : Nat.Prime 5099327703787 := by
  apply lucas_primality 5099327703787 (3 : ZMod 5099327703787)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod = 5099327703787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_381559
      · exact prime_thirtyAB_2227409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5099327703787) ^ 2549663851893 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 1699775901262 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 13364454 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 2289354 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_66576822500643073 : Nat.Prime 66576822500643073 := by
  apply lucas_primality 66576822500643073 (5 : ZMod 66576822500643073)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod = 66576822500643073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_5099327703787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66576822500643073) ^ 33288411250321536 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 22192274166881024 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 3916283676508416 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 13056 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_958594770894180216901104001 : Nat.Prime 958594770894180216901104001 := by
  apply lucas_primality 958594770894180216901104001 (101 : ZMod 958594770894180216901104001)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 958594770894180216901104001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 958594770894180216901104001) ^ 479297385447090108450552000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 319531590298060072300368000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 191718954178836043380220800 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 136942110127740030985872000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 87144979172198201536464000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 73738059299552324377008000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 56387927699657659817712000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 50452356362851590363216000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 41678033517138270300048000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 33054992099799317824176000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 30922411964328394093584000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 23380360265711712607344000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 22292901648701865509328000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 20395633423280430146832000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 18086693790456230507568000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 16247368998206444354256000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 958594770894180216901104001) ^ 15714668375314429785264000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_thirtyAB_4871 : Nat.Prime 4871 := by norm_num
private theorem prime_thirtyAB_11119 : Nat.Prime 11119 := by norm_num
private theorem prime_thirtyAB_48179 : Nat.Prime 48179 := by norm_num
private theorem prime_thirtyAB_230969 : Nat.Prime 230969 := by norm_num
private theorem prime_thirtyAB_732923 : Nat.Prime 732923 := by norm_num
private theorem prime_thirtyAB_909436064694478667316432001 : Nat.Prime 909436064694478667316432001 := by
  apply lucas_primality 909436064694478667316432001 (26 : ZMod 909436064694478667316432001)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 909436064694478667316432001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 909436064694478667316432001) ^ 454718032347239333658216000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 303145354898159555772144000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 181887212938895733463286400 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 129919437813496952473776000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 82676005881316242483312000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 53496239099675215724496000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 47865056036551508806128000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 39540698464977333361584000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 31359864299809609217808000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 29336647248208989268272000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 24579353099850774792336000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 22181367431572650422352000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 21149675923127410867824000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 19349703504137843985456000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 17159171031971295609744000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 15414170588042011310448000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 14908787945811125693712000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_769 : Nat.Prime 769 := by norm_num
private theorem prime_thirtyAB_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_thirtyAB_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_thirtyAB_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_thirtyAB_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_thirtyAB_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_89
      · exact prime_thirtyAB_223
      · exact prime_thirtyAB_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_thirtyAB_3643 : Nat.Prime 3643 := by norm_num
private theorem prime_thirtyAB_11279 : Nat.Prime 11279 := by norm_num
private theorem prime_thirtyAB_112571 : Nat.Prime 112571 := by norm_num
private theorem prime_thirtyAB_148680174529 : Nat.Prime 148680174529 := by
  apply lucas_primality 148680174529 (7 : ZMod 148680174529)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (2293, 1), (112571, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (2293, 1), (112571, 1)] : List FactorBlock).map factorBlockValue).prod = 148680174529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_2293
      · exact prime_thirtyAB_112571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 148680174529) ^ 74340087264 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 148680174529) ^ 49560058176 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 148680174529) ^ 64840896 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 148680174529) ^ 1320768 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_19805686049008091 : Nat.Prime 19805686049008091 := by
  apply lucas_primality 19805686049008091 (6 : ZMod 19805686049008091)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (11, 1), (173, 1), (148680174529, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (11, 1), (173, 1), (148680174529, 1)] : List FactorBlock).map factorBlockValue).prod = 19805686049008091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_173
      · exact prime_thirtyAB_148680174529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 19805686049008091) ^ 9902843024504045 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 19805686049008091) ^ 3961137209801618 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 19805686049008091) ^ 2829383721286870 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 19805686049008091) ^ 1800516913546190 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 19805686049008091) ^ 114483734387330 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 19805686049008091) ^ 133210 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_54421 : Nat.Prime 54421 := by norm_num
private theorem prime_thirtyAB_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_thirtyAB_97654321 : Nat.Prime 97654321 := by
  apply lucas_primality 97654321 (17 : ZMod 97654321)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod = 97654321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 97654321) ^ 48827160 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 32551440 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 19530864 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 4245840 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 16560 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_397 : Nat.Prime 397 := by norm_num
private theorem prime_thirtyAB_977 : Nat.Prime 977 := by norm_num
private theorem prime_thirtyAB_906371 : Nat.Prime 906371 := by norm_num
private theorem prime_thirtyAB_1406212853597 : Nat.Prime 1406212853597 := by
  apply lucas_primality 1406212853597 (2 : ZMod 1406212853597)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod = 1406212853597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_397
      · exact prime_thirtyAB_977
      · exact prime_thirtyAB_906371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406212853597) ^ 703106426798 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 3542097868 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1439317148 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1551476 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_157 : Nat.Prime 157 := by norm_num
private theorem prime_thirtyAB_49927 : Nat.Prime 49927 := by norm_num
private theorem prime_thirtyAB_66107 : Nat.Prime 66107 := by norm_num
private theorem prime_thirtyAB_498931 : Nat.Prime 498931 := by norm_num
private theorem prime_thirtyAB_19955244277 : Nat.Prime 19955244277 := by
  apply lucas_primality 19955244277 (2 : ZMod 19955244277)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (11, 1), (101, 1), (498931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (11, 1), (101, 1), (498931, 1)] : List FactorBlock).map factorBlockValue).prod = 19955244277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_101
      · exact prime_thirtyAB_498931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19955244277) ^ 9977622138 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 19955244277) ^ 6651748092 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 19955244277) ^ 1814113116 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 19955244277) ^ 197576676 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 19955244277) ^ 39996 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1591789925487737 : Nat.Prime 1591789925487737 := by
  apply lucas_primality 1591789925487737 (3 : ZMod 1591789925487737)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 2), (59, 1), (19955244277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 2), (59, 1), (19955244277, 1)] : List FactorBlock).map factorBlockValue).prod = 1591789925487737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_19955244277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1591789925487737) ^ 795894962743868 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1591789925487737) ^ 122445378883672 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1591789925487737) ^ 26979490262504 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1591789925487737) ^ 79768 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_367 : Nat.Prime 367 := by norm_num
private theorem prime_thirtyAB_33641 : Nat.Prime 33641 := by norm_num
private theorem prime_thirtyAB_1877 : Nat.Prime 1877 := by norm_num
private theorem prime_thirtyAB_1589747 : Nat.Prime 1589747 := by norm_num
private theorem prime_thirtyAB_97368824257 : Nat.Prime 97368824257 := by
  apply lucas_primality 97368824257 (5 : ZMod 97368824257)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (11, 1), (29, 1), (1589747, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (11, 1), (29, 1), (1589747, 1)] : List FactorBlock).map factorBlockValue).prod = 97368824257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_1589747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97368824257) ^ 48684412128 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 32456274752 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 8851711296 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 3357545664 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 97368824257) ^ 61248 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_24490011939472127 : Nat.Prime 24490011939472127 := by
  apply lucas_primality 24490011939472127 (5 : ZMod 24490011939472127)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (67, 1), (1877, 1), (97368824257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (67, 1), (1877, 1), (97368824257, 1)] : List FactorBlock).map factorBlockValue).prod = 24490011939472127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_67
      · exact prime_thirtyAB_1877
      · exact prime_thirtyAB_97368824257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24490011939472127) ^ 12245005969736063 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 24490011939472127) ^ 365522566260778 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 24490011939472127) ^ 13047422450438 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 24490011939472127) ^ 251518 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_65290371830632690583 : Nat.Prime 65290371830632690583 := by
  apply lucas_primality 65290371830632690583 (5 : ZMod 65290371830632690583)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (43, 1), (24490011939472127, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (43, 1), (24490011939472127, 1)] : List FactorBlock).map factorBlockValue).prod = 65290371830632690583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_24490011939472127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 65290371830632690583) ^ 32645185915316345291 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 65290371830632690583) ^ 2106141026794602922 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 65290371830632690583) ^ 1518380740247271874 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 65290371830632690583) ^ 2666 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_421 : Nat.Prime 421 := by norm_num
private theorem prime_thirtyAB_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_thirtyAB_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_thirtyAB_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_thirtyAB_191 : Nat.Prime 191 := by norm_num
private theorem prime_thirtyAB_811 : Nat.Prime 811 := by norm_num
private theorem prime_thirtyAB_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_191
      · exact prime_thirtyAB_383
      · exact prime_thirtyAB_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_607 : Nat.Prime 607 := by norm_num
private theorem prime_thirtyAB_82621199 : Nat.Prime 82621199 := by
  apply lucas_primality 82621199 (11 : ZMod 82621199)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (23, 1), (269, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (23, 1), (269, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod = 82621199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_269
      · exact prime_thirtyAB_607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 82621199) ^ 41310599 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 7511018 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 3592226 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 307142 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 82621199) ^ 136114 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_325800521 : Nat.Prime 325800521 := by
  apply lucas_primality 325800521 (3 : ZMod 325800521)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (23, 2), (89, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (23, 2), (89, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod = 325800521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_89
      · exact prime_thirtyAB_173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 325800521) ^ 162900260 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 65160104 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 14165240 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 3660680 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 325800521) ^ 1883240 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_131371 : Nat.Prime 131371 := by norm_num
private theorem prime_thirtyAB_362583961 : Nat.Prime 362583961 := by
  apply lucas_primality 362583961 (14 : ZMod 362583961)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (23, 1), (131371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (23, 1), (131371, 1)] : List FactorBlock).map factorBlockValue).prod = 362583961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_131371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 362583961) ^ 181291980 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 120861320 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 72516792 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 15764520 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (14 : ZMod 362583961) ^ 2760 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_754638436661375915432784001 : Nat.Prime 754638436661375915432784001 := by
  apply lucas_primality 754638436661375915432784001 (67 : ZMod 754638436661375915432784001)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 754638436661375915432784001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 754638436661375915432784001) ^ 377319218330687957716392000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 251546145553791971810928000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 150927687332275183086556800 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 107805490951625130776112000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 68603494241943265039344000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 58049110512413531956368000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 44390496274198583260752000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 39717812455861890285936000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 32810366811364170236208000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 26022015057288824670096000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 24343175376173416626864000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 20395633423280430146832000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 18405815528326241839824000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 17549731085148277103088000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 14238461069082564442128000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 12790481977311456193776000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 754638436661375915432784001) ^ 12371121912481572384144000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1433741 : Nat.Prime 1433741 := by norm_num
private theorem prime_thirtyAB_558757 : Nat.Prime 558757 := by norm_num
private theorem prime_thirtyAB_106163831 : Nat.Prime 106163831 := by
  apply lucas_primality 106163831 (11 : ZMod 106163831)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod = 106163831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_558757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106163831) ^ 53081915 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 21232766 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 5587570 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 190 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2409709 : Nat.Prime 2409709 := by norm_num
private theorem prime_thirtyAB_7311057107 : Nat.Prime 7311057107 := by
  apply lucas_primality 7311057107 (2 : ZMod 7311057107)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod = 7311057107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_2409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7311057107) ^ 3655528553 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 197596138 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 178318466 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 3034 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_58488456857 : Nat.Prime 58488456857 := by
  apply lucas_primality 58488456857 (3 : ZMod 58488456857)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod = 58488456857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7311057107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58488456857) ^ 29244228428 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 58488456857) ^ 8 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_311 : Nat.Prime 311 := by norm_num
private theorem prime_thirtyAB_139 : Nat.Prime 139 := by norm_num
private theorem prime_thirtyAB_137 : Nat.Prime 137 := by norm_num
private theorem prime_thirtyAB_114761 : Nat.Prime 114761 := by norm_num
private theorem prime_thirtyAB_64954727 : Nat.Prime 64954727 := by
  apply lucas_primality 64954727 (5 : ZMod 64954727)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (283, 1), (114761, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (283, 1), (114761, 1)] : List FactorBlock).map factorBlockValue).prod = 64954727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_283
      · exact prime_thirtyAB_114761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 64954727) ^ 32477363 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 64954727) ^ 229522 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 64954727) ^ 566 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_249166332773 : Nat.Prime 249166332773 := by
  apply lucas_primality 249166332773 (2 : ZMod 249166332773)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (137, 1), (64954727, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (137, 1), (64954727, 1)] : List FactorBlock).map factorBlockValue).prod = 249166332773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_137
      · exact prime_thirtyAB_64954727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 249166332773) ^ 124583166386 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 249166332773) ^ 35595190396 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 249166332773) ^ 1818732356 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 249166332773) ^ 3836 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_6478324652099 : Nat.Prime 6478324652099 := by
  apply lucas_primality 6478324652099 (2 : ZMod 6478324652099)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (249166332773, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (249166332773, 1)] : List FactorBlock).map factorBlockValue).prod = 6478324652099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_249166332773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6478324652099) ^ 3239162326049 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 6478324652099) ^ 498332665546 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 6478324652099) ^ 26 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_8059035867211157 : Nat.Prime 8059035867211157 := by
  apply lucas_primality 8059035867211157 (2 : ZMod 8059035867211157)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (311, 1), (6478324652099, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (311, 1), (6478324652099, 1)] : List FactorBlock).map factorBlockValue).prod = 8059035867211157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_311
      · exact prime_thirtyAB_6478324652099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8059035867211157) ^ 4029517933605578 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 8059035867211157) ^ 25913298608396 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 8059035867211157) ^ 1244 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1740800101532813178943 : Nat.Prime 1740800101532813178943 := by
  apply lucas_primality 1740800101532813178943 (3 : ZMod 1740800101532813178943)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (37, 1), (139, 1), (8059035867211157, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (37, 1), (139, 1), (8059035867211157, 1)] : List FactorBlock).map factorBlockValue).prod = 1740800101532813178943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_139
      · exact prime_thirtyAB_8059035867211157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1740800101532813178943) ^ 870400050766406589471 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1740800101532813178943) ^ 580266700510937726314 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1740800101532813178943) ^ 248685728790401882706 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1740800101532813178943) ^ 47048651392778734566 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1740800101532813178943) ^ 12523741737646137978 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1740800101532813178943) ^ 216006 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_739 : Nat.Prime 739 := by norm_num
private theorem prime_thirtyAB_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_thirtyAB_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_thirtyAB_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_163 : Nat.Prime 163 := by norm_num
private theorem prime_thirtyAB_3371 : Nat.Prime 3371 := by norm_num
private theorem prime_thirtyAB_135170359 : Nat.Prime 135170359 := by
  apply lucas_primality 135170359 (6 : ZMod 135170359)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (41, 1), (163, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (41, 1), (163, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod = 135170359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_163
      · exact prime_thirtyAB_3371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 135170359) ^ 67585179 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 45056786 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 3296838 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 829266 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 40098 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_24330664621 : Nat.Prime 24330664621 := by
  apply lucas_primality 24330664621 (2 : ZMod 24330664621)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (135170359, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (135170359, 1)] : List FactorBlock).map factorBlockValue).prod = 24330664621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_135170359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24330664621) ^ 12165332310 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 8110221540 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 4866132924 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 180 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_14431 : Nat.Prime 14431 := by norm_num
private theorem prime_thirtyAB_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_thirtyAB_32364193 : Nat.Prime 32364193 := by
  apply lucas_primality 32364193 (15 : ZMod 32364193)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (7, 1), (17, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (7, 1), (17, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod = 32364193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_2833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 32364193) ^ 16182096 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 10788064 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 4623456 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 1903776 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 11424 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_158796207522221 : Nat.Prime 158796207522221 := by
  apply lucas_primality 158796207522221 (2 : ZMod 158796207522221)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (17, 1), (14431, 1), (32364193, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (17, 1), (14431, 1), (32364193, 1)] : List FactorBlock).map factorBlockValue).prod = 158796207522221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_14431
      · exact prime_thirtyAB_32364193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158796207522221) ^ 79398103761110 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 31759241504444 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 9340953383660 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 11003825620 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 4906540 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_28583317353999781 : Nat.Prime 28583317353999781 := by
  apply lucas_primality 28583317353999781 (2 : ZMod 28583317353999781)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (158796207522221, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (158796207522221, 1)] : List FactorBlock).map factorBlockValue).prod = 28583317353999781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_158796207522221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28583317353999781) ^ 14291658676999890 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 9527772451333260 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 5716663470799956 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 180 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_31063 : Nat.Prime 31063 := by norm_num
private theorem prime_thirtyAB_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_thirtyAB_912772537 : Nat.Prime 912772537 := by
  apply lucas_primality 912772537 (7 : ZMod 912772537)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (13, 1), (37, 2), (2137, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (13, 1), (37, 2), (2137, 1)] : List FactorBlock).map factorBlockValue).prod = 912772537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_2137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 912772537) ^ 456386268 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 304257512 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 70213272 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 24669528 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 912772537) ^ 427128 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_4567973 : Nat.Prime 4567973 := by norm_num
private theorem prime_thirtyAB_2832143261 : Nat.Prime 2832143261 := by
  apply lucas_primality 2832143261 (2 : ZMod 2832143261)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (31, 1), (4567973, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (31, 1), (4567973, 1)] : List FactorBlock).map factorBlockValue).prod = 2832143261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_4567973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2832143261) ^ 1416071630 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 2832143261) ^ 566428652 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 2832143261) ^ 91359460 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 2832143261) ^ 620 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_175592882183 : Nat.Prime 175592882183 := by
  apply lucas_primality 175592882183 (10 : ZMod 175592882183)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (2832143261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (2832143261, 1)] : List FactorBlock).map factorBlockValue).prod = 175592882183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_2832143261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 175592882183) ^ 87796441091 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 175592882183) ^ 5664286522 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 175592882183) ^ 62 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_thirtyAB_3851 : Nat.Prime 3851 := by norm_num
private theorem prime_thirtyAB_6067 : Nat.Prime 6067 := by norm_num
private theorem prime_thirtyAB_18582983 : Nat.Prime 18582983 := by norm_num
private theorem prime_thirtyAB_5746715558245802797 : Nat.Prime 5746715558245802797 := by
  apply lucas_primality 5746715558245802797 (6 : ZMod 5746715558245802797)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1103, 1), (3851, 1), (6067, 1), (18582983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1103, 1), (3851, 1), (6067, 1), (18582983, 1)] : List FactorBlock).map factorBlockValue).prod = 5746715558245802797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_1103
      · exact prime_thirtyAB_3851
      · exact prime_thirtyAB_6067
      · exact prime_thirtyAB_18582983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5746715558245802797) ^ 2873357779122901398 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 5746715558245802797) ^ 1915571852748600932 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 5746715558245802797) ^ 5210077568672532 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 5746715558245802797) ^ 1492265790248196 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 5746715558245802797) ^ 947208761866788 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 5746715558245802797) ^ 309246129012 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_8447671870621330111591 : Nat.Prime 8447671870621330111591 := by
  apply lucas_primality 8447671870621330111591 (3 : ZMod 8447671870621330111591)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 2), (5746715558245802797, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 2), (5746715558245802797, 1)] : List FactorBlock).map factorBlockValue).prod = 8447671870621330111591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_5746715558245802797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8447671870621330111591) ^ 4223835935310665055795 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 8447671870621330111591) ^ 2815890623540443370530 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 8447671870621330111591) ^ 1689534374124266022318 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 8447671870621330111591) ^ 1206810267231618587370 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 8447671870621330111591) ^ 1470 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_4105568529121966434233227 : Nat.Prime 4105568529121966434233227 := by
  apply lucas_primality 4105568529121966434233227 (2 : ZMod 4105568529121966434233227)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (8447671870621330111591, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (8447671870621330111591, 1)] : List FactorBlock).map factorBlockValue).prod = 4105568529121966434233227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_8447671870621330111591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4105568529121966434233227) ^ 2052784264560983217116613 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 4105568529121966434233227) ^ 1368522843040655478077742 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 4105568529121966434233227) ^ 486 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_569 : Nat.Prime 569 := by norm_num
private theorem prime_thirtyAB_37039 : Nat.Prime 37039 := by norm_num
private theorem prime_thirtyAB_1544987 : Nat.Prime 1544987 := by norm_num
private theorem prime_thirtyAB_9813829 : Nat.Prime 9813829 := by norm_num
private theorem prime_thirtyAB_2394574277 : Nat.Prime 2394574277 := by
  apply lucas_primality 2394574277 (2 : ZMod 2394574277)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod = 2394574277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_61
      · exact prime_thirtyAB_9813829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2394574277) ^ 1197287138 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 39255316 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 244 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_14367445663 : Nat.Prime 14367445663 := by
  apply lucas_primality 14367445663 (23 : ZMod 14367445663)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod = 14367445663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_2394574277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 14367445663) ^ 7183722831 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 4789148554 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 6 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_20171893710853 : Nat.Prime 20171893710853 := by
  apply lucas_primality 20171893710853 (5 : ZMod 20171893710853)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod = 20171893710853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_14367445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20171893710853) ^ 10085946855426 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 6723964570284 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1551684131604 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1404 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_97327 : Nat.Prime 97327 := by norm_num
private theorem prime_thirtyAB_208223 : Nat.Prime 208223 := by norm_num
private theorem prime_thirtyAB_4129087 : Nat.Prime 4129087 := by norm_num
private theorem prime_thirtyAB_1929523 : Nat.Prime 1929523 := by norm_num
private theorem prime_thirtyAB_7706514863 : Nat.Prime 7706514863 := by
  apply lucas_primality 7706514863 (5 : ZMod 7706514863)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod = 7706514863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_1997
      · exact prime_thirtyAB_1929523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7706514863) ^ 3853257431 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3859046 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3994 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_633357259340797643309658001 : Nat.Prime 633357259340797643309658001 := by
  apply lucas_primality 633357259340797643309658001 (101 : ZMod 633357259340797643309658001)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 4), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 4), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 633357259340797643309658001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 633357259340797643309658001) ^ 316678629670398821654829000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 211119086446932547769886000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 126671451868159528661931600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 90479608477256806187094000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 57577932667345240300878000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 48719789180061357177666000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 37256309372988096665274000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 33334592596884086489982000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 27537272145252071448246000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 21839905494510263562402000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 20430879333574117526118000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 17117763765967503873234000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 15447738032702381544138000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 14729238589320875425806000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 13475686368953141347014000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 11950136968694295156786000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 10734868802386400734062000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (101 : ZMod 633357259340797643309658001) ^ 10382905890832748250978000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2428859 : Nat.Prime 2428859 := by norm_num
private theorem prime_thirtyAB_6121 : Nat.Prime 6121 := by norm_num
private theorem prime_thirtyAB_167470561 : Nat.Prime 167470561 := by
  apply lucas_primality 167470561 (13 : ZMod 167470561)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (5, 1), (19, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (5, 1), (19, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod = 167470561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_6121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 167470561) ^ 83735280 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 55823520 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 33494112 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 8814240 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 27360 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_617 : Nat.Prime 617 := by norm_num
private theorem prime_thirtyAB_42337 : Nat.Prime 42337 := by norm_num
private theorem prime_thirtyAB_1529752406099 : Nat.Prime 1529752406099 := by
  apply lucas_primality 1529752406099 (2 : ZMod 1529752406099)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (47, 1), (89, 1), (617, 1), (42337, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (47, 1), (89, 1), (617, 1), (42337, 1)] : List FactorBlock).map factorBlockValue).prod = 1529752406099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_89
      · exact prime_thirtyAB_617
      · exact prime_thirtyAB_42337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1529752406099) ^ 764876203049 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 218536058014 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 32547923534 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 17188229282 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 2479339394 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 36132754 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1056241 : Nat.Prime 1056241 := by norm_num
private theorem prime_thirtyAB_3413 : Nat.Prime 3413 := by norm_num
private theorem prime_thirtyAB_3583 : Nat.Prime 3583 := by norm_num
private theorem prime_thirtyAB_3617 : Nat.Prime 3617 := by norm_num
private theorem prime_thirtyAB_21673431885071 : Nat.Prime 21673431885071 := by
  apply lucas_primality 21673431885071 (13 : ZMod 21673431885071)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 2), (3413, 1), (3583, 1), (3617, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 2), (3413, 1), (3583, 1), (3617, 1)] : List FactorBlock).map factorBlockValue).prod = 21673431885071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_3413
      · exact prime_thirtyAB_3583
      · exact prime_thirtyAB_3617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 21673431885071) ^ 10836715942535 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 4334686377014 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 3096204555010 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 6350258390 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 6048962290 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 21673431885071) ^ 5992101710 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1511635180256161967 : Nat.Prime 1511635180256161967 := by
  apply lucas_primality 1511635180256161967 (5 : ZMod 1511635180256161967)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (43, 1), (811, 1), (21673431885071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (43, 1), (811, 1), (21673431885071, 1)] : List FactorBlock).map factorBlockValue).prod = 1511635180256161967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_811
      · exact prime_thirtyAB_21673431885071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1511635180256161967) ^ 755817590128080983 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511635180256161967) ^ 35154306517585162 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511635180256161967) ^ 1863915142116106 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511635180256161967) ^ 69746 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_12893 : Nat.Prime 12893 := by norm_num
private theorem prime_thirtyAB_1939867 : Nat.Prime 1939867 := by norm_num
private theorem prime_thirtyAB_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_thirtyAB_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_thirtyAB_3331 : Nat.Prime 3331 := by norm_num
private theorem prime_thirtyAB_47431 : Nat.Prime 47431 := by norm_num
private theorem prime_thirtyAB_24035813759802671 : Nat.Prime 24035813759802671 := by
  apply lucas_primality 24035813759802671 (13 : ZMod 24035813759802671)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (1427, 1), (1523, 1), (3331, 1), (47431, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (1427, 1), (1523, 1), (3331, 1), (47431, 1)] : List FactorBlock).map factorBlockValue).prod = 24035813759802671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_1427
      · exact prime_thirtyAB_1523
      · exact prime_thirtyAB_3331
      · exact prime_thirtyAB_47431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 24035813759802671) ^ 12017906879901335 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 24035813759802671) ^ 4807162751960534 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 24035813759802671) ^ 3433687679971810 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 24035813759802671) ^ 16843597589210 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 24035813759802671) ^ 15781886907290 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 24035813759802671) ^ 7215795184570 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 24035813759802671) ^ 506753257570 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_thirtyAB_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_113
      · exact prime_thirtyAB_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_thirtyAB_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_thirtyAB_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_397
      · exact prime_thirtyAB_2531
      · exact prime_thirtyAB_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_167 : Nat.Prime 167 := by norm_num
private theorem prime_thirtyAB_1493 : Nat.Prime 1493 := by norm_num
private theorem prime_thirtyAB_142183 : Nat.Prime 142183 := by norm_num
private theorem prime_thirtyAB_87584729 : Nat.Prime 87584729 := by
  apply lucas_primality 87584729 (3 : ZMod 87584729)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (11, 1), (142183, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (11, 1), (142183, 1)] : List FactorBlock).map factorBlockValue).prod = 87584729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_142183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 87584729) ^ 43792364 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 87584729) ^ 12512104 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 87584729) ^ 7962248 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 87584729) ^ 616 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_7919 : Nat.Prime 7919 := by norm_num
private theorem prime_thirtyAB_69497 : Nat.Prime 69497 := by norm_num
private theorem prime_thirtyAB_41003231 : Nat.Prime 41003231 := by
  apply lucas_primality 41003231 (22 : ZMod 41003231)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (59, 1), (69497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (59, 1), (69497, 1)] : List FactorBlock).map factorBlockValue).prod = 41003231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_69497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 41003231) ^ 20501615 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (22 : ZMod 41003231) ^ 8200646 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (22 : ZMod 41003231) ^ 694970 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (22 : ZMod 41003231) ^ 590 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_26625776075699 : Nat.Prime 26625776075699 := by
  apply lucas_primality 26625776075699 (2 : ZMod 26625776075699)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (7919, 1), (41003231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (7919, 1), (41003231, 1)] : List FactorBlock).map factorBlockValue).prod = 26625776075699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_7919
      · exact prime_thirtyAB_41003231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26625776075699) ^ 13312888037849 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 26625776075699) ^ 649409172578 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 26625776075699) ^ 3362264942 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 26625776075699) ^ 649358 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_thirtyAB_4979131 : Nat.Prime 4979131 := by norm_num
private theorem prime_thirtyAB_1191109 : Nat.Prime 1191109 := by norm_num
private theorem prime_thirtyAB_33351053 : Nat.Prime 33351053 := by
  apply lucas_primality 33351053 (2 : ZMod 33351053)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (1191109, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (1191109, 1)] : List FactorBlock).map factorBlockValue).prod = 33351053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_1191109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33351053) ^ 16675526 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351053) ^ 4764436 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351053) ^ 28 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_541589 : Nat.Prime 541589 := by norm_num
private theorem prime_thirtyAB_228550559 : Nat.Prime 228550559 := by
  apply lucas_primality 228550559 (37 : ZMod 228550559)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (211, 1), (541589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (211, 1), (541589, 1)] : List FactorBlock).map factorBlockValue).prod = 228550559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_211
      · exact prime_thirtyAB_541589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (37 : ZMod 228550559) ^ 114275279 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (37 : ZMod 228550559) ^ 1083178 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (37 : ZMod 228550559) ^ 422 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_505097 : Nat.Prime 505097 := by norm_num
private theorem prime_thirtyAB_225273263 : Nat.Prime 225273263 := by
  apply lucas_primality 225273263 (5 : ZMod 225273263)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (223, 1), (505097, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (223, 1), (505097, 1)] : List FactorBlock).map factorBlockValue).prod = 225273263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_223
      · exact prime_thirtyAB_505097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 225273263) ^ 112636631 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 225273263) ^ 1010194 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 225273263) ^ 446 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_874459 : Nat.Prime 874459 := by norm_num
private theorem prime_thirtyAB_109 : Nat.Prime 109 := by norm_num
private theorem prime_thirtyAB_9871 : Nat.Prime 9871 := by norm_num
private theorem prime_thirtyAB_30126293 : Nat.Prime 30126293 := by
  apply lucas_primality 30126293 (2 : ZMod 30126293)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (109, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (109, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod = 30126293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_109
      · exact prime_thirtyAB_9871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30126293) ^ 15063146 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 4303756 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 276388 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 3052 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_51033940343 : Nat.Prime 51033940343 := by
  apply lucas_primality 51033940343 (10 : ZMod 51033940343)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (11, 2), (30126293, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (11, 2), (30126293, 1)] : List FactorBlock).map factorBlockValue).prod = 51033940343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_30126293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 51033940343) ^ 25516970171 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 7290562906 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 4639449122 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 1694 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_102067880687 : Nat.Prime 102067880687 := by
  apply lucas_primality 102067880687 (5 : ZMod 102067880687)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (51033940343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (51033940343, 1)] : List FactorBlock).map factorBlockValue).prod = 102067880687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_51033940343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 102067880687) ^ 51033940343 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 102067880687) ^ 2 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1249558476287426663 : Nat.Prime 1249558476287426663 := by
  apply lucas_primality 1249558476287426663 (5 : ZMod 1249558476287426663)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (874459, 1), (102067880687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (874459, 1), (102067880687, 1)] : List FactorBlock).map factorBlockValue).prod = 1249558476287426663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_874459
      · exact prime_thirtyAB_102067880687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1249558476287426663) ^ 624779238143713331 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 178508353755346666 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 1428950329618 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 12242426 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2499116952574853327 : Nat.Prime 2499116952574853327 := by
  apply lucas_primality 2499116952574853327 (5 : ZMod 2499116952574853327)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1249558476287426663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1249558476287426663, 1)] : List FactorBlock).map factorBlockValue).prod = 2499116952574853327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_1249558476287426663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2499116952574853327) ^ 1249558476287426663 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 2499116952574853327) ^ 2 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_947 : Nat.Prime 947 := by norm_num
private theorem prime_thirtyAB_1983689 : Nat.Prime 1983689 := by norm_num
private theorem prime_thirtyAB_7514213933 : Nat.Prime 7514213933 := by
  apply lucas_primality 7514213933 (2 : ZMod 7514213933)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (947, 1), (1983689, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (947, 1), (1983689, 1)] : List FactorBlock).map factorBlockValue).prod = 7514213933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_947
      · exact prime_thirtyAB_1983689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7514213933) ^ 3757106966 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7514213933) ^ 7934756 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7514213933) ^ 3788 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_12864823 : Nat.Prime 12864823 := by norm_num
private theorem prime_thirtyAB_16568887 : Nat.Prime 16568887 := by norm_num
private theorem prime_thirtyAB_73751906302452347 : Nat.Prime 73751906302452347 := by
  apply lucas_primality 73751906302452347 (2 : ZMod 73751906302452347)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (173, 1), (12864823, 1), (16568887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (173, 1), (12864823, 1), (16568887, 1)] : List FactorBlock).map factorBlockValue).prod = 73751906302452347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_173
      · exact prime_thirtyAB_12864823
      · exact prime_thirtyAB_16568887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73751906302452347) ^ 36875953151226173 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 73751906302452347) ^ 426311597124002 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 73751906302452347) ^ 5732834902 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 73751906302452347) ^ 4451228758 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_545661638816687200389859201 : Nat.Prime 545661638816687200389859201 := by
  apply lucas_primality 545661638816687200389859201 (13 : ZMod 545661638816687200389859201)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 545661638816687200389859201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 545661638816687200389859201) ^ 272830819408343600194929600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 181887212938895733463286400 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 109132327763337440077971840 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 77951662688098171484265600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 49605603528789745489987200 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 32097743459805129434697600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 28719033621930905283676800 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 23724419078986400016950400 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 18815918579885765530684800 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 17601988348925393560963200 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 14747611859910464875401600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 13308820458943590253411200 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 12689805553876446520694400 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 11609822102482706391273600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 10295502619182777365846400 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 9248502352825206786268800 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 8945272767486675416227200 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_21347 : Nat.Prime 21347 := by norm_num
private theorem prime_thirtyAB_26687336297 : Nat.Prime 26687336297 := by
  apply lucas_primality 26687336297 (3 : ZMod 26687336297)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod = 26687336297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_71
      · exact prime_thirtyAB_21347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26687336297) ^ 13343668148 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 860881816 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 375877976 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 1250168 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_thirtyAB_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_thirtyAB_13147 : Nat.Prime 13147 := by norm_num
private theorem prime_thirtyAB_283615046165023 : Nat.Prime 283615046165023 := by
  apply lucas_primality 283615046165023 (3 : ZMod 283615046165023)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod = 283615046165023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_1163
      · exact prime_thirtyAB_1663
      · exact prime_thirtyAB_13147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 283615046165023) ^ 141807523082511 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 94538348721674 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 25783186015002 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21816542012694 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 243865043994 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 170544224994 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21572605626 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_7219 : Nat.Prime 7219 := by norm_num
private theorem prime_thirtyAB_690629 : Nat.Prime 690629 := by norm_num
private theorem prime_thirtyAB_7541 : Nat.Prime 7541 := by norm_num
private theorem prime_thirtyAB_2853973 : Nat.Prime 2853973 := by norm_num
private theorem prime_thirtyAB_11805329 : Nat.Prime 11805329 := by norm_num
private theorem prime_thirtyAB_7114017466219560317 : Nat.Prime 7114017466219560317 := by
  apply lucas_primality 7114017466219560317 (2 : ZMod 7114017466219560317)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (7541, 1), (2853973, 1), (11805329, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (7541, 1), (2853973, 1), (11805329, 1)] : List FactorBlock).map factorBlockValue).prod = 7114017466219560317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_7541
      · exact prime_thirtyAB_2853973
      · exact prime_thirtyAB_11805329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7114017466219560317) ^ 3557008733109780158 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7114017466219560317) ^ 1016288209459937188 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7114017466219560317) ^ 943378526219276 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7114017466219560317) ^ 2492671607692 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7114017466219560317) ^ 602610691004 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_14266177 : Nat.Prime 14266177 := by norm_num
private theorem prime_thirtyAB_85597063 : Nat.Prime 85597063 := by
  apply lucas_primality 85597063 (5 : ZMod 85597063)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (14266177, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (14266177, 1)] : List FactorBlock).map factorBlockValue).prod = 85597063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_14266177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 85597063) ^ 42798531 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 85597063) ^ 28532354 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 85597063) ^ 6 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_4451047277 : Nat.Prime 4451047277 := by
  apply lucas_primality 4451047277 (2 : ZMod 4451047277)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (85597063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (85597063, 1)] : List FactorBlock).map factorBlockValue).prod = 4451047277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_85597063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4451047277) ^ 2225523638 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 4451047277) ^ 342388252 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 4451047277) ^ 52 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_293769120283 : Nat.Prime 293769120283 := by
  apply lucas_primality 293769120283 (7 : ZMod 293769120283)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (4451047277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (4451047277, 1)] : List FactorBlock).map factorBlockValue).prod = 293769120283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_4451047277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 293769120283) ^ 146884560141 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 293769120283) ^ 97923040094 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 293769120283) ^ 26706283662 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 293769120283) ^ 66 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2932487 : Nat.Prime 2932487 := by norm_num
private theorem prime_thirtyAB_26500063922641 : Nat.Prime 26500063922641 := by
  apply lucas_primality 26500063922641 (19 : ZMod 26500063922641)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (7, 1), (11, 1), (163, 1), (2932487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (7, 1), (11, 1), (163, 1), (2932487, 1)] : List FactorBlock).map factorBlockValue).prod = 26500063922641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_163
      · exact prime_thirtyAB_2932487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 26500063922641) ^ 13250031961320 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 8833354640880 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 5300012784528 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 3785723417520 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 2409096720240 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 162577079280 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (19 : ZMod 26500063922641) ^ 9036720 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_829 : Nat.Prime 829 := by norm_num
private theorem prime_thirtyAB_51949 : Nat.Prime 51949 := by norm_num
private theorem prime_thirtyAB_56624411 : Nat.Prime 56624411 := by
  apply lucas_primality 56624411 (2 : ZMod 56624411)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (109, 1), (51949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (109, 1), (51949, 1)] : List FactorBlock).map factorBlockValue).prod = 56624411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_109
      · exact prime_thirtyAB_51949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56624411) ^ 28312205 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 11324882 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 519490 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 1090 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_3586771 : Nat.Prime 3586771 := by norm_num
private theorem prime_thirtyAB_287801 : Nat.Prime 287801 := by norm_num
private theorem prime_thirtyAB_381624127 : Nat.Prime 381624127 := by
  apply lucas_primality 381624127 (3 : ZMod 381624127)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (17, 1), (287801, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (17, 1), (287801, 1)] : List FactorBlock).map factorBlockValue).prod = 381624127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_287801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 381624127) ^ 190812063 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 127208042 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 29355702 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 22448478 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 1326 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1526496509 : Nat.Prime 1526496509 := by
  apply lucas_primality 1526496509 (2 : ZMod 1526496509)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (381624127, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (381624127, 1)] : List FactorBlock).map factorBlockValue).prod = 1526496509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_381624127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1526496509) ^ 763248254 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1526496509) ^ 4 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_10950386820164879 : Nat.Prime 10950386820164879 := by
  apply lucas_primality 10950386820164879 (17 : ZMod 10950386820164879)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3586771, 1), (1526496509, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3586771, 1), (1526496509, 1)] : List FactorBlock).map factorBlockValue).prod = 10950386820164879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3586771
      · exact prime_thirtyAB_1526496509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 10950386820164879) ^ 5475193410082439 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (17 : ZMod 10950386820164879) ^ 3052993018 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (17 : ZMod 10950386820164879) ^ 7173542 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_727 : Nat.Prime 727 := by norm_num
private theorem prime_thirtyAB_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_thirtyAB_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_thirtyAB_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_thirtyAB_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_173
      · exact prime_thirtyAB_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_4159
      · exact prime_thirtyAB_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_487 : Nat.Prime 487 := by norm_num
private theorem prime_thirtyAB_2741 : Nat.Prime 2741 := by norm_num
private theorem prime_thirtyAB_10177 : Nat.Prime 10177 := by norm_num
private theorem prime_thirtyAB_2047819 : Nat.Prime 2047819 := by norm_num
private theorem prime_thirtyAB_12594086851 : Nat.Prime 12594086851 := by
  apply lucas_primality 12594086851 (2 : ZMod 12594086851)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (41, 1), (2047819, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (41, 1), (2047819, 1)] : List FactorBlock).map factorBlockValue).prod = 12594086851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_2047819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12594086851) ^ 6297043425 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 12594086851) ^ 4198028950 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 12594086851) ^ 2518817370 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 12594086851) ^ 307172850 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 12594086851) ^ 6150 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_25540808133829 : Nat.Prime 25540808133829 := by
  apply lucas_primality 25540808133829 (2 : ZMod 25540808133829)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 2), (12594086851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 2), (12594086851, 1)] : List FactorBlock).map factorBlockValue).prod = 25540808133829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_12594086851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25540808133829) ^ 12770404066914 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 25540808133829) ^ 8513602711276 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 25540808133829) ^ 1964677548756 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 25540808133829) ^ 2028 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_4137610917680299 : Nat.Prime 4137610917680299 := by
  apply lucas_primality 4137610917680299 (2 : ZMod 4137610917680299)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (25540808133829, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (25540808133829, 1)] : List FactorBlock).map factorBlockValue).prod = 4137610917680299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_25540808133829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4137610917680299) ^ 2068805458840149 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 4137610917680299) ^ 1379203639226766 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 4137610917680299) ^ 162 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_762563 : Nat.Prime 762563 := by norm_num
private theorem prime_thirtyAB_14719189 : Nat.Prime 14719189 := by norm_num
private theorem prime_thirtyAB_500452427 : Nat.Prime 500452427 := by
  apply lucas_primality 500452427 (2 : ZMod 500452427)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod = 500452427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_14719189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 500452427) ^ 250226213 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 29438378 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 34 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_15383 : Nat.Prime 15383 := by norm_num
private theorem prime_thirtyAB_64153 : Nat.Prime 64153 := by norm_num
private theorem prime_thirtyAB_11842387189 : Nat.Prime 11842387189 := by
  apply lucas_primality 11842387189 (2 : ZMod 11842387189)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod = 11842387189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_15383
      · exact prime_thirtyAB_64153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11842387189) ^ 5921193594 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 3947462396 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 769836 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 184596 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_4211029 : Nat.Prime 4211029 := by norm_num
private theorem prime_thirtyAB_583087 : Nat.Prime 583087 := by norm_num
private theorem prime_thirtyAB_373 : Nat.Prime 373 := by norm_num
private theorem prime_thirtyAB_137150609 : Nat.Prime 137150609 := by
  apply lucas_primality 137150609 (3 : ZMod 137150609)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 3), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 3), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod = 137150609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_67
      · exact prime_thirtyAB_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 137150609) ^ 68575304 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 137150609) ^ 19592944 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 137150609) ^ 2047024 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 137150609) ^ 367696 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_10972048721 : Nat.Prime 10972048721 := by
  apply lucas_primality 10972048721 (3 : ZMod 10972048721)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (137150609, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (137150609, 1)] : List FactorBlock).map factorBlockValue).prod = 10972048721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_137150609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10972048721) ^ 5486024360 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 10972048721) ^ 2194409744 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 10972048721) ^ 80 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_7570713617491 : Nat.Prime 7570713617491 := by
  apply lucas_primality 7570713617491 (2 : ZMod 7570713617491)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (23, 1), (10972048721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (23, 1), (10972048721, 1)] : List FactorBlock).map factorBlockValue).prod = 7570713617491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_10972048721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7570713617491) ^ 3785356808745 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7570713617491) ^ 2523571205830 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7570713617491) ^ 1514142723498 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7570713617491) ^ 329161461630 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7570713617491) ^ 690 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_8422645990584407760037 : Nat.Prime 8422645990584407760037 := by
  apply lucas_primality 8422645990584407760037 (5 : ZMod 8422645990584407760037)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (53, 1), (583087, 1), (7570713617491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (53, 1), (583087, 1), (7570713617491, 1)] : List FactorBlock).map factorBlockValue).prod = 8422645990584407760037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_583087
      · exact prime_thirtyAB_7570713617491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8422645990584407760037) ^ 4211322995292203880018 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 8422645990584407760037) ^ 2807548663528135920012 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 8422645990584407760037) ^ 158917848878951089812 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 8422645990584407760037) ^ 14444921582172828 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 8422645990584407760037) ^ 1112529996 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1211593 : Nat.Prime 1211593 := by norm_num
private theorem prime_thirtyAB_45481 : Nat.Prime 45481 := by norm_num
private theorem prime_thirtyAB_264527 : Nat.Prime 264527 := by norm_num
private theorem prime_thirtyAB_25432683889 : Nat.Prime 25432683889 := by
  apply lucas_primality 25432683889 (13 : ZMod 25432683889)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (2003, 1), (264527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (2003, 1), (264527, 1)] : List FactorBlock).map factorBlockValue).prod = 25432683889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_2003
      · exact prime_thirtyAB_264527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 25432683889) ^ 12716341944 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 25432683889) ^ 8477561296 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 25432683889) ^ 12697296 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (13 : ZMod 25432683889) ^ 96144 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_867527921966706751 : Nat.Prime 867527921966706751 := by
  apply lucas_primality 867527921966706751 (6 : ZMod 867527921966706751)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 3), (45481, 1), (25432683889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 3), (45481, 1), (25432683889, 1)] : List FactorBlock).map factorBlockValue).prod = 867527921966706751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_45481
      · exact prime_thirtyAB_25432683889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 867527921966706751) ^ 433763960983353375 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 867527921966706751) ^ 289175973988902250 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 867527921966706751) ^ 173505584393341350 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 867527921966706751) ^ 19074512916750 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 867527921966706751) ^ 34110750 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_395592732416818278457 : Nat.Prime 395592732416818278457 := by
  apply lucas_primality 395592732416818278457 (7 : ZMod 395592732416818278457)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (19, 1), (867527921966706751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (19, 1), (867527921966706751, 1)] : List FactorBlock).map factorBlockValue).prod = 395592732416818278457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_867527921966706751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 395592732416818278457) ^ 197796366208409139228 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 395592732416818278457) ^ 131864244138939426152 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 395592732416818278457) ^ 20820670127200962024 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 395592732416818278457) ^ 456 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_239 : Nat.Prime 239 := by norm_num
private theorem prime_thirtyAB_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_thirtyAB_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_thirtyAB_983 : Nat.Prime 983 := by norm_num
private theorem prime_thirtyAB_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_thirtyAB_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_983
      · exact prime_thirtyAB_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2089 : Nat.Prime 2089 := by norm_num
private theorem prime_thirtyAB_18671 : Nat.Prime 18671 := by norm_num
private theorem prime_thirtyAB_251162293 : Nat.Prime 251162293 := by
  apply lucas_primality 251162293 (2 : ZMod 251162293)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (59, 1), (18671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (59, 1), (18671, 1)] : List FactorBlock).map factorBlockValue).prod = 251162293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_18671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 251162293) ^ 125581146 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 251162293) ^ 83720764 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 251162293) ^ 13219068 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 251162293) ^ 4256988 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 251162293) ^ 13452 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_4283 : Nat.Prime 4283 := by norm_num
private theorem prime_thirtyAB_33724343 : Nat.Prime 33724343 := by
  apply lucas_primality 33724343 (5 : ZMod 33724343)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (127, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (127, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod = 33724343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_127
      · exact prime_thirtyAB_4283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33724343) ^ 16862171 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 33724343) ^ 1087882 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 33724343) ^ 265546 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 33724343) ^ 7874 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_67448687 : Nat.Prime 67448687 := by
  apply lucas_primality 67448687 (5 : ZMod 67448687)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (33724343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (33724343, 1)] : List FactorBlock).map factorBlockValue).prod = 67448687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_33724343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 67448687) ^ 33724343 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 67448687) ^ 2 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_332387129537 : Nat.Prime 332387129537 := by
  apply lucas_primality 332387129537 (3 : ZMod 332387129537)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (7, 1), (11, 1), (67448687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (7, 1), (11, 1), (67448687, 1)] : List FactorBlock).map factorBlockValue).prod = 332387129537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_67448687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 332387129537) ^ 166193564768 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 332387129537) ^ 47483875648 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 332387129537) ^ 30217011776 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 332387129537) ^ 4928 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_889467958641013 : Nat.Prime 889467958641013 := by
  apply lucas_primality 889467958641013 (2 : ZMod 889467958641013)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (223, 1), (332387129537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (223, 1), (332387129537, 1)] : List FactorBlock).map factorBlockValue).prod = 889467958641013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_223
      · exact prime_thirtyAB_332387129537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 889467958641013) ^ 444733979320506 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 889467958641013) ^ 296489319547004 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 889467958641013) ^ 3988645554444 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 889467958641013) ^ 2676 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_460623461338761922407024001 : Nat.Prime 460623461338761922407024001 := by
  apply lucas_primality 460623461338761922407024001 (11 : ZMod 460623461338761922407024001)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 4), (5, 3), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 4), (5, 3), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 460623461338761922407024001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 460623461338761922407024001) ^ 230311730669380961203512000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 153541153779587307469008000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 92124692267752384481404800 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 65803351619823131772432000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 35432573949135532492848000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 27095497725809524847472000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 24243340070461153810896000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 20027107014728779235088000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 15883567632371100772656000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 14858821333508449109904000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 12449282738885457362352000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 11234718569238095668464000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 10712173519506091218768000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 9800499177420466434192000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 8691008704504941932208000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 7807177310826473261136000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 460623461338761922407024001) ^ 7551204284241998727984000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_599 : Nat.Prime 599 := by norm_num
private theorem prime_thirtyAB_1811 : Nat.Prime 1811 := by norm_num
private theorem prime_thirtyAB_33809 : Nat.Prime 33809 := by norm_num
private theorem prime_thirtyAB_227 : Nat.Prime 227 := by norm_num
private theorem prime_thirtyAB_247757789 : Nat.Prime 247757789 := by
  apply lucas_primality 247757789 (2 : ZMod 247757789)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod = 247757789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_97
      · exact prime_thirtyAB_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 247757789) ^ 123878894 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 8543372 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 2554204 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 1091444 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_12398369604474701 : Nat.Prime 12398369604474701 := by
  apply lucas_primality 12398369604474701 (2 : ZMod 12398369604474701)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod = 12398369604474701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_67
      · exact prime_thirtyAB_97
      · exact prime_thirtyAB_247757789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12398369604474701) ^ 6199184802237350 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 2479673920894940 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1771195657782100 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1127124509497700 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 185050292604100 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 127818243345100 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 50042300 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_4679 : Nat.Prime 4679 := by norm_num
private theorem prime_thirtyAB_437819 : Nat.Prime 437819 := by norm_num
private theorem prime_thirtyAB_591091 : Nat.Prime 591091 := by norm_num
private theorem prime_thirtyAB_9060461 : Nat.Prime 9060461 := by norm_num
private theorem prime_thirtyAB_54362767 : Nat.Prime 54362767 := by
  apply lucas_primality 54362767 (5 : ZMod 54362767)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (9060461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (9060461, 1)] : List FactorBlock).map factorBlockValue).prod = 54362767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_9060461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 54362767) ^ 27181383 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 54362767) ^ 18120922 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 54362767) ^ 6 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_thirtyAB_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_thirtyAB_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_thirtyAB_17678041 : Nat.Prime 17678041 := by norm_num
private theorem prime_thirtyAB_176780411 : Nat.Prime 176780411 := by
  apply lucas_primality 176780411 (2 : ZMod 176780411)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod = 176780411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176780411) ^ 88390205 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 35356082 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 10 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_437876623741786025004208001 : Nat.Prime 437876623741786025004208001 := by
  apply lucas_primality 437876623741786025004208001 (12 : ZMod 437876623741786025004208001)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 437876623741786025004208001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 437876623741786025004208001) ^ 218938311870893012502104000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 87575324748357205000841600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 62553803391683717857744000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 39806965794707820454928000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 33682817210906617308016000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 25757448455399177941424000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 23046138091672948684432000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 19038114075729827174096000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 15099193922130552586352000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 14125052378767291129168000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 11834503344372595270384000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 10679917652238683536688000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 10183177296320605232656000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 9316523909399702659664000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 8261823089467660849136000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 7421637690538746186512000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 7178305307242393852528000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_42743 : Nat.Prime 42743 := by norm_num
private theorem prime_thirtyAB_68483 : Nat.Prime 68483 := by norm_num
private theorem prime_thirtyAB_324773 : Nat.Prime 324773 := by norm_num
private theorem prime_thirtyAB_77945521 : Nat.Prime 77945521 := by
  apply lucas_primality 77945521 (7 : ZMod 77945521)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (324773, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (324773, 1)] : List FactorBlock).map factorBlockValue).prod = 77945521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_324773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 77945521) ^ 38972760 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 77945521) ^ 25981840 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 77945521) ^ 15589104 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 77945521) ^ 240 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_243421 : Nat.Prime 243421 := by norm_num
private theorem prime_thirtyAB_1895762749 : Nat.Prime 1895762749 := by
  apply lucas_primality 1895762749 (2 : ZMod 1895762749)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (59, 1), (243421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (59, 1), (243421, 1)] : List FactorBlock).map factorBlockValue).prod = 1895762749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_243421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1895762749) ^ 947881374 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1895762749) ^ 631920916 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1895762749) ^ 172342068 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1895762749) ^ 32131572 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1895762749) ^ 7788 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_22721 : Nat.Prime 22721 := by norm_num
private theorem prime_thirtyAB_132963293 : Nat.Prime 132963293 := by
  apply lucas_primality 132963293 (2 : ZMod 132963293)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (11, 1), (19, 1), (22721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (11, 1), (19, 1), (22721, 1)] : List FactorBlock).map factorBlockValue).prod = 132963293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_22721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 132963293) ^ 66481646 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 132963293) ^ 18994756 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 132963293) ^ 12087572 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 132963293) ^ 6998068 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 132963293) ^ 5852 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1657339 : Nat.Prime 1657339 := by norm_num
private theorem prime_thirtyAB_36461459 : Nat.Prime 36461459 := by
  apply lucas_primality 36461459 (2 : ZMod 36461459)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (1657339, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (1657339, 1)] : List FactorBlock).map factorBlockValue).prod = 36461459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_1657339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36461459) ^ 18230729 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 36461459) ^ 3314678 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 36461459) ^ 22 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_12907356487 : Nat.Prime 12907356487 := by
  apply lucas_primality 12907356487 (3 : ZMod 12907356487)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (59, 1), (36461459, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (59, 1), (36461459, 1)] : List FactorBlock).map factorBlockValue).prod = 12907356487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_36461459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12907356487) ^ 6453678243 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 12907356487) ^ 4302452162 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 12907356487) ^ 218768754 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 12907356487) ^ 354 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_251 : Nat.Prime 251 := by norm_num
private theorem prime_thirtyAB_66238901 : Nat.Prime 66238901 := by
  apply lucas_primality 66238901 (2 : ZMod 66238901)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (7, 1), (13, 1), (29, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (7, 1), (13, 1), (29, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod = 66238901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66238901) ^ 33119450 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 66238901) ^ 13247780 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 66238901) ^ 9462700 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 66238901) ^ 5095300 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 66238901) ^ 2284100 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 66238901) ^ 263900 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_20666537113 : Nat.Prime 20666537113 := by
  apply lucas_primality 20666537113 (5 : ZMod 20666537113)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (13, 1), (66238901, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (13, 1), (66238901, 1)] : List FactorBlock).map factorBlockValue).prod = 20666537113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_66238901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20666537113) ^ 10333268556 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 20666537113) ^ 6888845704 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 20666537113) ^ 1589733624 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 20666537113) ^ 312 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_409 : Nat.Prime 409 := by norm_num
private theorem prime_thirtyAB_443 : Nat.Prime 443 := by norm_num
private theorem prime_thirtyAB_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_thirtyAB_1671268889 : Nat.Prime 1671268889 := by
  apply lucas_primality 1671268889 (3 : ZMod 1671268889)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod = 1671268889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_409
      · exact prime_thirtyAB_443
      · exact prime_thirtyAB_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1671268889) ^ 835634444 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 4086232 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 3772616 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 1449496 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_13421 : Nat.Prime 13421 := by norm_num
private theorem prime_thirtyAB_99611 : Nat.Prime 99611 := by norm_num
private theorem prime_thirtyAB_50261 : Nat.Prime 50261 := by norm_num
private theorem prime_thirtyAB_23622671 : Nat.Prime 23622671 := by
  apply lucas_primality 23622671 (7 : ZMod 23622671)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (47, 1), (50261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (47, 1), (50261, 1)] : List FactorBlock).map factorBlockValue).prod = 23622671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_50261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 23622671) ^ 11811335 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 4724534 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 502610 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 470 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_252645265925168009 : Nat.Prime 252645265925168009 := by
  apply lucas_primality 252645265925168009 (3 : ZMod 252645265925168009)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod = 252645265925168009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_13421
      · exact prime_thirtyAB_99611
      · exact prime_thirtyAB_23622671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 252645265925168009) ^ 126322632962584004 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 18824623047848 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 2536318939928 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 10695033848 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_thirtyAB_4969 : Nat.Prime 4969 := by norm_num
private theorem prime_thirtyAB_10103311 : Nat.Prime 10103311 := by norm_num
private theorem prime_thirtyAB_32429 : Nat.Prime 32429 := by norm_num
private theorem prime_thirtyAB_38287 : Nat.Prime 38287 := by norm_num
private theorem prime_thirtyAB_7449654739 : Nat.Prime 7449654739 := by
  apply lucas_primality 7449654739 (2 : ZMod 7449654739)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (32429, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (32429, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod = 7449654739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_32429
      · exact prime_thirtyAB_38287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7449654739) ^ 3724827369 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 2483218246 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 229722 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 7449654739) ^ 194574 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_29798618957 : Nat.Prime 29798618957 := by
  apply lucas_primality 29798618957 (2 : ZMod 29798618957)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7449654739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7449654739, 1)] : List FactorBlock).map factorBlockValue).prod = 29798618957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7449654739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 29798618957) ^ 14899309478 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 29798618957) ^ 4 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2991981134619696139127 : Nat.Prime 2991981134619696139127 := by
  apply lucas_primality 2991981134619696139127 (5 : ZMod 2991981134619696139127)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4969, 1), (10103311, 1), (29798618957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4969, 1), (10103311, 1), (29798618957, 1)] : List FactorBlock).map factorBlockValue).prod = 2991981134619696139127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_4969
      · exact prime_thirtyAB_10103311
      · exact prime_thirtyAB_29798618957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2991981134619696139127) ^ 1495990567309848069563 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 602129429386133254 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 296138675194666 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 2991981134619696139127) ^ 100406704718 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_653 : Nat.Prime 653 := by norm_num
private theorem prime_thirtyAB_911 : Nat.Prime 911 := by norm_num
private theorem prime_thirtyAB_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_thirtyAB_12073 : Nat.Prime 12073 := by norm_num
private theorem prime_thirtyAB_2069 : Nat.Prime 2069 := by norm_num
private theorem prime_thirtyAB_379235287 : Nat.Prime 379235287 := by
  apply lucas_primality 379235287 (3 : ZMod 379235287)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (17, 1), (599, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (17, 1), (599, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod = 379235287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_599
      · exact prime_thirtyAB_2069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 379235287) ^ 189617643 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 379235287) ^ 126411762 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 379235287) ^ 22307958 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 379235287) ^ 633114 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 379235287) ^ 183294 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_17444823203 : Nat.Prime 17444823203 := by
  apply lucas_primality 17444823203 (2 : ZMod 17444823203)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (379235287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (379235287, 1)] : List FactorBlock).map factorBlockValue).prod = 17444823203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_379235287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17444823203) ^ 8722411601 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 17444823203) ^ 758470574 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 17444823203) ^ 46 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2948558907417467 : Nat.Prime 2948558907417467 := by
  apply lucas_primality 2948558907417467 (2 : ZMod 2948558907417467)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (12073, 1), (17444823203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (12073, 1), (17444823203, 1)] : List FactorBlock).map factorBlockValue).prod = 2948558907417467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_12073
      · exact prime_thirtyAB_17444823203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2948558907417467) ^ 1474279453708733 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 2948558907417467) ^ 421222701059638 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 2948558907417467) ^ 244227524842 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 2948558907417467) ^ 169022 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_7343899008173092202759 : Nat.Prime 7343899008173092202759 := by
  apply lucas_primality 7343899008173092202759 (11 : ZMod 7343899008173092202759)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (911, 1), (1367, 1), (2948558907417467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (911, 1), (1367, 1), (2948558907417467, 1)] : List FactorBlock).map factorBlockValue).prod = 7343899008173092202759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_911
      · exact prime_thirtyAB_1367
      · exact prime_thirtyAB_2948558907417467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7343899008173092202759) ^ 3671949504086546101379 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 7343899008173092202759) ^ 8061360052879354778 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 7343899008173092202759) ^ 5372274329314624874 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (11 : ZMod 7343899008173092202759) ^ 2490674 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_14687798016346184405519 : Nat.Prime 14687798016346184405519 := by
  apply lucas_primality 14687798016346184405519 (7 : ZMod 14687798016346184405519)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7343899008173092202759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7343899008173092202759, 1)] : List FactorBlock).map factorBlockValue).prod = 14687798016346184405519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7343899008173092202759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 14687798016346184405519) ^ 7343899008173092202759 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (7 : ZMod 14687798016346184405519) ^ 2 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_407678235897524919831504001 : Nat.Prime 407678235897524919831504001 := by
  apply lucas_primality 407678235897524919831504001 (67 : ZMod 407678235897524919831504001)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 407678235897524919831504001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 407678235897524919831504001) ^ 203839117948762459915752000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 135892745299174973277168000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 81535647179504983966300800 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 58239747985360702833072000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 37061657808865901802864000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 31359864299809609217808000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 23981072699854407048912000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 21456749257764469464816000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 17725140691196735644848000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 13150910835404029671984000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 11018330699933105941392000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 9943371607256705361744000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 9480889206919184182128000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 8674005019096274890032000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 7692042186745753204368000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 6909800608432625759856000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 6683249768811883931664000 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_389 : Nat.Prime 389 := by norm_num
private theorem prime_thirtyAB_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_thirtyAB_305476361 : Nat.Prime 305476361 := by
  apply lucas_primality 305476361 (6 : ZMod 305476361)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (7, 1), (853, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (7, 1), (853, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod = 305476361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_853
      · exact prime_thirtyAB_1279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 305476361) ^ 152738180 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 305476361) ^ 61095272 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 305476361) ^ 43639480 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 305476361) ^ 358120 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 305476361) ^ 238840 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1698461 : Nat.Prime 1698461 := by norm_num
private theorem prime_thirtyAB_101907661 : Nat.Prime 101907661 := by
  apply lucas_primality 101907661 (6 : ZMod 101907661)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (1698461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (1698461, 1)] : List FactorBlock).map factorBlockValue).prod = 101907661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_1698461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 101907661) ^ 50953830 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 101907661) ^ 33969220 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 101907661) ^ 20381532 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (6 : ZMod 101907661) ^ 60 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_45654632129 : Nat.Prime 45654632129 := by
  apply lucas_primality 45654632129 (3 : ZMod 45654632129)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (7, 1), (101907661, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (7, 1), (101907661, 1)] : List FactorBlock).map factorBlockValue).prod = 45654632129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_101907661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 45654632129) ^ 22827316064 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 45654632129) ^ 6522090304 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 45654632129) ^ 448 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_3391773930127669 : Nat.Prime 3391773930127669 := by
  apply lucas_primality 3391773930127669 (2 : ZMod 3391773930127669)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (41, 1), (151, 1), (45654632129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (41, 1), (151, 1), (45654632129, 1)] : List FactorBlock).map factorBlockValue).prod = 3391773930127669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_151
      · exact prime_thirtyAB_45654632129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3391773930127669) ^ 1695886965063834 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 3391773930127669) ^ 1130591310042556 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 3391773930127669) ^ 82726193417748 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 3391773930127669) ^ 22462079007468 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 3391773930127669) ^ 74292 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_17239 : Nat.Prime 17239 := by norm_num
private theorem prime_thirtyAB_3169 : Nat.Prime 3169 := by norm_num
private theorem prime_thirtyAB_250693 : Nat.Prime 250693 := by norm_num
private theorem prime_thirtyAB_3177784469 : Nat.Prime 3177784469 := by
  apply lucas_primality 3177784469 (2 : ZMod 3177784469)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3169, 1), (250693, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3169, 1), (250693, 1)] : List FactorBlock).map factorBlockValue).prod = 3177784469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3169
      · exact prime_thirtyAB_250693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3177784469) ^ 1588892234 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 3177784469) ^ 1002772 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 3177784469) ^ 12676 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_997 : Nat.Prime 997 := by norm_num
private theorem prime_thirtyAB_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_thirtyAB_591827 : Nat.Prime 591827 := by norm_num
private theorem prime_thirtyAB_647441109840979 : Nat.Prime 647441109840979 := by
  apply lucas_primality 647441109840979 (2 : ZMod 647441109840979)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (47, 1), (997, 1), (1297, 1), (591827, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (47, 1), (997, 1), (1297, 1), (591827, 1)] : List FactorBlock).map factorBlockValue).prod = 647441109840979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_997
      · exact prime_thirtyAB_1297
      · exact prime_thirtyAB_591827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 647441109840979) ^ 323720554920489 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 647441109840979) ^ 215813703280326 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 647441109840979) ^ 13775342762574 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 647441109840979) ^ 649389277674 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 647441109840979) ^ 499183585074 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 647441109840979) ^ 1093970214 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_19
      · exact prime_thirtyAB_23
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_37
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_43
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_313 : Nat.Prime 313 := by norm_num
private theorem prime_thirtyAB_4078951 : Nat.Prime 4078951 := by norm_num
private theorem prime_thirtyAB_263 : Nat.Prime 263 := by norm_num
private theorem prime_thirtyAB_5953 : Nat.Prime 5953 := by norm_num
private theorem prime_thirtyAB_1281097507 : Nat.Prime 1281097507 := by
  apply lucas_primality 1281097507 (2 : ZMod 1281097507)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (31, 1), (89, 1), (5953, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (31, 1), (89, 1), (5953, 1)] : List FactorBlock).map factorBlockValue).prod = 1281097507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_89
      · exact prime_thirtyAB_5953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1281097507) ^ 640548753 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1281097507) ^ 427032502 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1281097507) ^ 98545962 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1281097507) ^ 41325726 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1281097507) ^ 14394354 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 1281097507) ^ 215202 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_39083722743557 : Nat.Prime 39083722743557 := by
  apply lucas_primality 39083722743557 (2 : ZMod 39083722743557)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (263, 1), (1281097507, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (263, 1), (1281097507, 1)] : List FactorBlock).map factorBlockValue).prod = 39083722743557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_263
      · exact prime_thirtyAB_1281097507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39083722743557) ^ 19541861371778 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 39083722743557) ^ 1347714577364 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 39083722743557) ^ 148607310812 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 39083722743557) ^ 30508 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_181 : Nat.Prime 181 := by norm_num
private theorem prime_thirtyAB_682049 : Nat.Prime 682049 := by norm_num
private theorem prime_thirtyAB_1728312167 : Nat.Prime 1728312167 := by
  apply lucas_primality 1728312167 (5 : ZMod 1728312167)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (181, 1), (682049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (181, 1), (682049, 1)] : List FactorBlock).map factorBlockValue).prod = 1728312167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_181
      · exact prime_thirtyAB_682049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1728312167) ^ 864156083 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1728312167) ^ 246901738 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1728312167) ^ 9548686 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1728312167) ^ 2534 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_4111 : Nat.Prime 4111 := by norm_num
private theorem prime_thirtyAB_616871 : Nat.Prime 616871 := by norm_num
private theorem prime_thirtyAB_6282853 : Nat.Prime 6282853 := by norm_num
private theorem prime_thirtyAB_223062602575272503 : Nat.Prime 223062602575272503 := by
  apply lucas_primality 223062602575272503 (5 : ZMod 223062602575272503)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (4111, 1), (616871, 1), (6282853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (4111, 1), (616871, 1), (6282853, 1)] : List FactorBlock).map factorBlockValue).prod = 223062602575272503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_4111
      · exact prime_thirtyAB_616871
      · exact prime_thirtyAB_6282853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 223062602575272503) ^ 111531301287636251 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 223062602575272503) ^ 31866086082181786 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 223062602575272503) ^ 54259937381482 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 223062602575272503) ^ 361603321562 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 223062602575272503) ^ 35503393534 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_609781 : Nat.Prime 609781 := by norm_num
private theorem prime_thirtyAB_260329 : Nat.Prime 260329 := by norm_num
private theorem prime_thirtyAB_21346979 : Nat.Prime 21346979 := by
  apply lucas_primality 21346979 (2 : ZMod 21346979)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (260329, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (260329, 1)] : List FactorBlock).map factorBlockValue).prod = 21346979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_260329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21346979) ^ 10673489 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 21346979) ^ 520658 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 21346979) ^ 82 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_271 : Nat.Prime 271 := by norm_num
private theorem prime_thirtyAB_9497 : Nat.Prime 9497 := by norm_num
private theorem prime_thirtyAB_161869470179 : Nat.Prime 161869470179 := by
  apply lucas_primality 161869470179 (2 : ZMod 161869470179)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (41, 1), (59, 1), (271, 1), (9497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (41, 1), (59, 1), (271, 1), (9497, 1)] : List FactorBlock).map factorBlockValue).prod = 161869470179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_13
      · exact prime_thirtyAB_41
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_271
      · exact prime_thirtyAB_9497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161869470179) ^ 80934735089 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 12451497706 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 3948035858 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 2743550342 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 597304318 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 17044274 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_401 : Nat.Prime 401 := by norm_num
private theorem prime_thirtyAB_3203 : Nat.Prime 3203 := by norm_num
private theorem prime_thirtyAB_13845864341 : Nat.Prime 13845864341 := by
  apply lucas_primality 13845864341 (2 : ZMod 13845864341)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 2), (11, 1), (401, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 2), (11, 1), (401, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod = 13845864341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_401
      · exact prime_thirtyAB_3203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13845864341) ^ 6922932170 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 13845864341) ^ 2769172868 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 13845864341) ^ 1977980620 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 13845864341) ^ 1258714940 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 13845864341) ^ 34528340 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 13845864341) ^ 4322780 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2442487 : Nat.Prime 2442487 := by norm_num
private theorem prime_thirtyAB_18186758203 : Nat.Prime 18186758203 := by
  apply lucas_primality 18186758203 (2 : ZMod 18186758203)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (73, 1), (2442487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (73, 1), (2442487, 1)] : List FactorBlock).map factorBlockValue).prod = 18186758203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_73
      · exact prime_thirtyAB_2442487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18186758203) ^ 9093379101 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 18186758203) ^ 6062252734 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 18186758203) ^ 1069809306 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 18186758203) ^ 249133674 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 18186758203) ^ 7446 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_27251402226539261 : Nat.Prime 27251402226539261 := by
  apply lucas_primality 27251402226539261 (3 : ZMod 27251402226539261)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 2), (11, 1), (139, 1), (18186758203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 2), (11, 1), (139, 1), (18186758203, 1)] : List FactorBlock).map factorBlockValue).prod = 27251402226539261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_139
      · exact prime_thirtyAB_18186758203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27251402226539261) ^ 13625701113269630 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 27251402226539261) ^ 5450280445307852 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 27251402226539261) ^ 3893057460934180 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 27251402226539261) ^ 2477400202412660 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 27251402226539261) ^ 196053253428340 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 27251402226539261) ^ 1498420 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2712337 : Nat.Prime 2712337 := by norm_num
private theorem prime_thirtyAB_2442113 : Nat.Prime 2442113 := by norm_num
private theorem prime_thirtyAB_21683 : Nat.Prime 21683 := by norm_num
private theorem prime_thirtyAB_106750482823 : Nat.Prime 106750482823 := by
  apply lucas_primality 106750482823 (3 : ZMod 106750482823)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (17, 1), (31, 1), (173, 1), (21683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (17, 1), (31, 1), (173, 1), (21683, 1)] : List FactorBlock).map factorBlockValue).prod = 106750482823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_31
      · exact prime_thirtyAB_173
      · exact prime_thirtyAB_21683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 106750482823) ^ 53375241411 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 35583494274 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 6279440166 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 3443563962 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 617054814 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 106750482823) ^ 4923234 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_137647879701195599473 : Nat.Prime 137647879701195599473 := by
  apply lucas_primality 137647879701195599473 (5 : ZMod 137647879701195599473)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (11, 1), (2442113, 1), (106750482823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (11, 1), (2442113, 1), (106750482823, 1)] : List FactorBlock).map factorBlockValue).prod = 137647879701195599473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_11
      · exact prime_thirtyAB_2442113
      · exact prime_thirtyAB_106750482823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 137647879701195599473) ^ 68823939850597799736 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 45882626567065199824 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 12513443609199599952 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 56364254930544 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 137647879701195599473) ^ 1289435664 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_2122619 : Nat.Prime 2122619 := by norm_num
private theorem prime_thirtyAB_433014277 : Nat.Prime 433014277 := by
  apply lucas_primality 433014277 (5 : ZMod 433014277)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod = 433014277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_2122619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 433014277) ^ 216507138 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 144338092 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 25471428 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 204 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_5075167 : Nat.Prime 5075167 := by norm_num
private theorem prime_thirtyAB_152255011 : Nat.Prime 152255011 := by
  apply lucas_primality 152255011 (3 : ZMod 152255011)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod = 152255011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_5
      · exact prime_thirtyAB_5075167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 152255011) ^ 76127505 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 50751670 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30451002 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1045618291773007 : Nat.Prime 1045618291773007 := by
  apply lucas_primality 1045618291773007 (5 : ZMod 1045618291773007)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod = 1045618291773007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_47
      · exact prime_thirtyAB_71
      · exact prime_thirtyAB_152255011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1045618291773007) ^ 522809145886503 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 348539430591002 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 149374041681858 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 22247197697298 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 14727018193986 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 6867546 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_853224526086773713 : Nat.Prime 853224526086773713 := by
  apply lucas_primality 853224526086773713 (5 : ZMod 853224526086773713)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod = 853224526086773713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_1045618291773007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 853224526086773713) ^ 426612263043386856 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 284408175362257904 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 50189678005104336 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 816 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_thirtyAB_32487773 : Nat.Prime 32487773 := by
  apply lucas_primality 32487773 (3 : ZMod 32487773)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (229, 1), (1223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (229, 1), (1223, 1)] : List FactorBlock).map factorBlockValue).prod = 32487773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_229
      · exact prime_thirtyAB_1223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32487773) ^ 16243886 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 32487773) ^ 1120268 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 32487773) ^ 141868 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 32487773) ^ 26564 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_thirtyAB_116504309 : Nat.Prime 116504309 := by
  apply lucas_primality 116504309 (2 : ZMod 116504309)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (101, 1), (283, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (101, 1), (283, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod = 116504309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_101
      · exact prime_thirtyAB_283
      · exact prime_thirtyAB_1019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 116504309) ^ 58252154 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 116504309) ^ 1153508 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 116504309) ^ 411676 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 116504309) ^ 114332 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_48353 : Nat.Prime 48353 := by norm_num
private theorem prime_thirtyAB_696089789 : Nat.Prime 696089789 := by
  apply lucas_primality 696089789 (2 : ZMod 696089789)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (59, 1), (61, 1), (48353, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (59, 1), (61, 1), (48353, 1)] : List FactorBlock).map factorBlockValue).prod = 696089789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_59
      · exact prime_thirtyAB_61
      · exact prime_thirtyAB_48353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 696089789) ^ 348044894 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 696089789) ^ 11798132 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 696089789) ^ 11411308 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 696089789) ^ 14396 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_8596330746156484907 : Nat.Prime 8596330746156484907 := by
  apply lucas_primality 8596330746156484907 (2 : ZMod 8596330746156484907)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (116504309, 1), (696089789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (116504309, 1), (696089789, 1)] : List FactorBlock).map factorBlockValue).prod = 8596330746156484907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_116504309
      · exact prime_thirtyAB_696089789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8596330746156484907) ^ 4298165373078242453 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 8596330746156484907) ^ 162194919738801602 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 8596330746156484907) ^ 73785517634 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 8596330746156484907) ^ 12349456754 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_25577 : Nat.Prime 25577 := by norm_num
private theorem prime_thirtyAB_323797 : Nat.Prime 323797 := by norm_num
private theorem prime_thirtyAB_120623 : Nat.Prime 120623 := by norm_num
private theorem prime_thirtyAB_171767153 : Nat.Prime 171767153 := by
  apply lucas_primality 171767153 (3 : ZMod 171767153)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (89, 1), (120623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (89, 1), (120623, 1)] : List FactorBlock).map factorBlockValue).prod = 171767153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_89
      · exact prime_thirtyAB_120623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 171767153) ^ 85883576 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 171767153) ^ 1929968 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 171767153) ^ 1424 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_1030602919 : Nat.Prime 1030602919 := by
  apply lucas_primality 1030602919 (3 : ZMod 1030602919)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (171767153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (171767153, 1)] : List FactorBlock).map factorBlockValue).prod = 1030602919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_171767153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1030602919) ^ 515301459 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1030602919) ^ 343534306 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 1030602919) ^ 6 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_735850484167 : Nat.Prime 735850484167 := by
  apply lucas_primality 735850484167 (3 : ZMod 735850484167)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (17, 1), (1030602919, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (17, 1), (1030602919, 1)] : List FactorBlock).map factorBlockValue).prod = 735850484167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_17
      · exact prime_thirtyAB_1030602919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 735850484167) ^ 367925242083 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 735850484167) ^ 245283494722 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 735850484167) ^ 105121497738 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 735850484167) ^ 43285322598 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 735850484167) ^ 714 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_140100513382431394213 : Nat.Prime 140100513382431394213 := by
  apply lucas_primality 140100513382431394213 (5 : ZMod 140100513382431394213)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (323797, 1), (735850484167, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (323797, 1), (735850484167, 1)] : List FactorBlock).map factorBlockValue).prod = 140100513382431394213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_3
      · exact prime_thirtyAB_7
      · exact prime_thirtyAB_323797
      · exact prime_thirtyAB_735850484167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 140100513382431394213) ^ 70050256691215697106 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 140100513382431394213) ^ 46700171127477131404 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 140100513382431394213) ^ 20014359054633056316 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 140100513382431394213) ^ 432680084690196 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (5 : ZMod 140100513382431394213) ^ 190392636 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_467 : Nat.Prime 467 := by norm_num
private theorem prime_thirtyAB_1479571 : Nat.Prime 1479571 := by norm_num
private theorem prime_thirtyAB_5477 : Nat.Prime 5477 := by norm_num
private theorem prime_thirtyAB_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_thirtyAB_6577 : Nat.Prime 6577 := by norm_num
private theorem prime_thirtyAB_426097523 : Nat.Prime 426097523 := by
  apply lucas_primality 426097523 (2 : ZMod 426097523)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (1117, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (1117, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod = 426097523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_29
      · exact prime_thirtyAB_1117
      · exact prime_thirtyAB_6577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 426097523) ^ 213048761 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 426097523) ^ 14693018 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 426097523) ^ 381466 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 426097523) ^ 64786 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_90332674877 : Nat.Prime 90332674877 := by
  apply lucas_primality 90332674877 (2 : ZMod 90332674877)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (53, 1), (426097523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (53, 1), (426097523, 1)] : List FactorBlock).map factorBlockValue).prod = 90332674877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_53
      · exact prime_thirtyAB_426097523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90332674877) ^ 45166337438 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 90332674877) ^ 1704390092 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (2 : ZMod 90332674877) ^ 212 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem prime_thirtyAB_518500159195792793 : Nat.Prime 518500159195792793 := by
  apply lucas_primality 518500159195792793 (3 : ZMod 518500159195792793)
  · rw [← thirtyABFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (131, 1), (5477, 1), (90332674877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (131, 1), (5477, 1), (90332674877, 1)] : List FactorBlock).map factorBlockValue).prod = 518500159195792793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyAB_2
      · exact prime_thirtyAB_131
      · exact prime_thirtyAB_5477
      · exact prime_thirtyAB_90332674877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 518500159195792793) ^ 259250079597896396 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 518500159195792793) ^ 3958016482410632 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 518500159195792793) ^ 94668643271096 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide
    · change (3 : ZMod 518500159195792793) ^ 5739896 ≠ 1
      rw [← thirtyABFastPow_eq_pow]
      decide

private theorem phi_thirtyAB_35468006523084668025340848000 : Nat.totient 35468006523084668025340848000 = 4667141053780819181568000000 := by
  rw [← show ((([(2, 7), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_5, prime_thirtyAB_7, prime_thirtyAB_11, prime_thirtyAB_13, prime_thirtyAB_17, prime_thirtyAB_19, prime_thirtyAB_23, prime_thirtyAB_29, prime_thirtyAB_31, prime_thirtyAB_37, prime_thirtyAB_41, prime_thirtyAB_43, prime_thirtyAB_47, prime_thirtyAB_53, prime_thirtyAB_59, prime_thirtyAB_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848001 : Nat.totient 35468006523084668025340848001 = 34936440976767665250629683200 := by
  rw [← show ((([(67, 1), (15937, 1), (1954163219, 1), (16997872587401, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_67, prime_thirtyAB_15937, prime_thirtyAB_1954163219, prime_thirtyAB_16997872587401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848002 : Nat.totient 35468006523084668025340848002 = 17713907915460003585022950720 := by
  rw [← show ((([(2, 1), (883, 1), (1535377, 1), (13080701940447819211, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_883, prime_thirtyAB_1535377, prime_thirtyAB_13080701940447819211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848003 : Nat.totient 35468006523084668025340848003 = 23605984450181700082453176096 := by
  rw [← show ((([(3, 1), (859, 1), (1997, 1), (6891984566505300835487, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_859, prime_thirtyAB_1997, prime_thirtyAB_6891984566505300835487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848004 : Nat.totient 35468006523084668025340848004 = 17726269287158756893606891104 := by
  rw [← show ((([(2, 2), (2293, 1), (3866987191788559531764157, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_2293, prime_thirtyAB_3866987191788559531764157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848005 : Nat.totient 35468006523084668025340848005 = 28374160405918078552743169920 := by
  rw [← show ((([(5, 1), (115903, 1), (32244294937, 1), (1898100541591, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_5, prime_thirtyAB_115903, prime_thirtyAB_32244294937, prime_thirtyAB_1898100541591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848006 : Nat.totient 35468006523084668025340848006 = 11822586549148761105448221024 := by
  rw [← show ((([(2, 1), (3, 1), (143669, 1), (13852339783, 1), (2970293224763, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_143669, prime_thirtyAB_13852339783, prime_thirtyAB_2970293224763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848007 : Nat.totient 35468006523084668025340848007 = 30399872536642655104536884472 := by
  rw [← show ((([(7, 1), (23827, 1), (212651952605295721092763, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_7, prime_thirtyAB_23827, prime_thirtyAB_212651952605295721092763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848008 : Nat.totient 35468006523084668025340848008 = 17660406267994430728807833600 := by
  rw [← show ((([(2, 3), (241, 1), (1701391, 1), (11484449, 1), (941489444879, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_241, prime_thirtyAB_1701391, prime_thirtyAB_11484449, prime_thirtyAB_941489444879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848009 : Nat.totient 35468006523084668025340848009 = 23645273705211858094619136000 := by
  rw [← show ((([(3, 2), (374681, 1), (27212041, 1), (386519565736481, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_374681, prime_thirtyAB_27212041, prime_thirtyAB_386519565736481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848010 : Nat.totient 35468006523084668025340848010 = 14187202608767627957354904400 := by
  rw [← show ((([(2, 1), (5, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_5, prime_thirtyAB_30429025931, prime_thirtyAB_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848011 : Nat.totient 35468006523084668025340848011 = 32243642293713334568491680000 := by
  rw [← show ((([(11, 1), (3224364229371333456849168001, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_11, prime_thirtyAB_3224364229371333456849168001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848012 : Nat.totient 35468006523084668025340848012 = 11767234303164905839260297216 := by
  rw [← show ((([(2, 2), (3, 1), (223, 1), (5113, 1), (101287, 1), (25592998416424177, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_223, prime_thirtyAB_5113, prime_thirtyAB_101287, prime_thirtyAB_25592998416424177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848013 : Nat.totient 35468006523084668025340848013 = 32739697846839128763779874048 := by
  rw [← show ((([(13, 1), (67901849, 1), (40180175271566404649, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_13, prime_thirtyAB_67901849, prime_thirtyAB_40180175271566404649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848014 : Nat.totient 35468006523084668025340848014 = 15084290360665353527528774400 := by
  rw [← show ((([(2, 1), (7, 1), (131, 1), (60607, 1), (275672333, 1), (1157501278441, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_7, prime_thirtyAB_131, prime_thirtyAB_60607, prime_thirtyAB_275672333, prime_thirtyAB_1157501278441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848015 : Nat.totient 35468006523084668025340848015 = 18916180150877748968060860416 := by
  rw [← show ((([(3, 1), (5, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_5, prime_thirtyAB_210193, prime_thirtyAB_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848016 : Nat.totient 35468006523084668025340848016 = 17649107852257261929427200000 := by
  rw [← show ((([(2, 4), (211, 1), (28751, 1), (75389, 1), (4847004293442769, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_211, prime_thirtyAB_28751, prime_thirtyAB_75389, prime_thirtyAB_4847004293442769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848017 : Nat.totient 35468006523084668025340848017 = 33360653617775260509863854080 := by
  rw [← show ((([(17, 1), (1637, 1), (109063, 1), (116411, 1), (2321369, 1), (43243769, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_17, prime_thirtyAB_1637, prime_thirtyAB_109063, prime_thirtyAB_116411, prime_thirtyAB_2321369, prime_thirtyAB_43243769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848018 : Nat.totient 35468006523084668025340848018 = 11660713454605173244211001600 := by
  rw [← show ((([(2, 1), (3, 2), (73, 1), (13737811, 1), (68784581, 1), (28564904807, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_73, prime_thirtyAB_13737811, prime_thirtyAB_68784581, prime_thirtyAB_28564904807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848019 : Nat.totient 35468006523084668025340848019 = 33601269199902109518093323616 := by
  rw [← show ((([(19, 1), (243916877, 1), (7653169425523223813, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_19, prime_thirtyAB_243916877, prime_thirtyAB_7653169425523223813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848020 : Nat.totient 35468006523084668025340848020 = 14185326469577935538308700160 := by
  rw [← show ((([(2, 2), (5, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_5, prime_thirtyAB_8233, prime_thirtyAB_93811, prime_thirtyAB_8274073, prime_thirtyAB_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848021 : Nat.totient 35468006523084668025340848021 = 20237317220736087977687938560 := by
  rw [← show ((([(3, 1), (7, 1), (673, 1), (889647091, 1), (2820880298726107, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_7, prime_thirtyAB_673, prime_thirtyAB_889647091, prime_thirtyAB_2820880298726107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848022 : Nat.totient 35468006523084668025340848022 = 16089469994230363967422824000 := by
  rw [← show ((([(2, 1), (11, 2), (499, 1), (375101, 1), (783019623353225509, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_11, prime_thirtyAB_499, prime_thirtyAB_375101, prime_thirtyAB_783019623353225509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848023 : Nat.totient 35468006523084668025340848023 = 33925919282945618550575846200 := by
  rw [← show ((([(23, 1), (7101574596971, 1), (217147228276931, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_23, prime_thirtyAB_7101574596971, prime_thirtyAB_217147228276931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848024 : Nat.totient 35468006523084668025340848024 = 11822668841028222675113616000 := by
  rw [← show ((([(2, 3), (3, 1), (1477833605128527834389202001, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_1477833605128527834389202001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848025 : Nat.totient 35468006523084668025340848025 = 28347152899525246696638504960 := by
  rw [← show ((([(5, 2), (1049, 1), (139537, 1), (175593973, 1), (55197867029, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_5, prime_thirtyAB_1049, prime_thirtyAB_139537, prime_thirtyAB_175593973, prime_thirtyAB_55197867029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848026 : Nat.totient 35468006523084668025340848026 = 16298346731226508570939428096 := by
  rw [← show ((([(2, 1), (13, 1), (229, 1), (887599, 1), (1779481213, 1), (3771531487, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_13, prime_thirtyAB_229, prime_thirtyAB_887599, prime_thirtyAB_1779481213, prime_thirtyAB_3771531487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848027 : Nat.totient 35468006523084668025340848027 = 23645337681957024539200817736 := by
  rw [← show ((([(3, 3), (237841108607, 1), (5523140549247743, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_237841108607, prime_thirtyAB_5523140549247743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848028 : Nat.totient 35468006523084668025340848028 = 15200158760185402606782934656 := by
  rw [← show ((([(2, 2), (7, 1), (36587, 1), (107042151929, 1), (323442523387, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_7, prime_thirtyAB_36587, prime_thirtyAB_107042151929, prime_thirtyAB_323442523387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848029 : Nat.totient 35468006523084668025340848029 = 33891930868841659314652041216 := by
  rw [← show ((([(29, 1), (97, 1), (12608605233944069685510433, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_29, prime_thirtyAB_97, prime_thirtyAB_12608605233944069685510433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848030 : Nat.totient 35468006523084668025340848030 = 9364438622826365116007809536 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_5, prime_thirtyAB_103, prime_thirtyAB_5009, prime_thirtyAB_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848031 : Nat.totient 35468006523084668025340848031 = 34096566657169337951180700000 := by
  rw [← show ((([(31, 1), (151, 1), (191909981, 1), (39482130177410771, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_31, prime_thirtyAB_151, prime_thirtyAB_191909981, prime_thirtyAB_39482130177410771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848032 : Nat.totient 35468006523084668025340848032 = 17733958119216199282728546048 := by
  rw [← show ((([(2, 5), (406247, 1), (11909399, 1), (229090346350717, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_406247, prime_thirtyAB_11909399, prime_thirtyAB_229090346350717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848033 : Nat.totient 35468006523084668025340848033 = 21495761529142223045661120000 := by
  rw [← show ((([(3, 1), (11, 1), (1074788076457111152283056001, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_11, prime_thirtyAB_1074788076457111152283056001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848034 : Nat.totient 35468006523084668025340848034 = 16668893843475415322740876800 := by
  rw [← show ((([(2, 1), (17, 2), (761, 1), (29811610063, 1), (2704823010871, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_17, prime_thirtyAB_761, prime_thirtyAB_29811610063, prime_thirtyAB_2704823010871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848035 : Nat.totient 35468006523084668025340848035 = 24244040422500088944487092480 := by
  rw [← show ((([(5, 1), (7, 1), (331, 1), (7129, 1), (429449525106920937499, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_5, prime_thirtyAB_7, prime_thirtyAB_331, prime_thirtyAB_7129, prime_thirtyAB_429449525106920937499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848036 : Nat.totient 35468006523084668025340848036 = 11761536323008053982600445952 := by
  rw [← show ((([(2, 2), (3, 2), (283, 1), (613, 1), (85303, 1), (66576822500643073, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_283, prime_thirtyAB_613, prime_thirtyAB_85303, prime_thirtyAB_66576822500643073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848037 : Nat.totient 35468006523084668025340848037 = 34509411752190487808439744000 := by
  rw [← show ((([(37, 1), (958594770894180216901104001, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_37, prime_thirtyAB_958594770894180216901104001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848038 : Nat.totient 35468006523084668025340848038 = 16787282114794309790110433280 := by
  rw [← show ((([(2, 1), (19, 1), (2113, 1), (4871, 1), (11119, 1), (48179, 1), (230969, 1), (732923, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_19, prime_thirtyAB_2113, prime_thirtyAB_4871, prime_thirtyAB_11119, prime_thirtyAB_48179, prime_thirtyAB_230969, prime_thirtyAB_732923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848039 : Nat.totient 35468006523084668025340848039 = 21826465552667488015594368000 := by
  rw [← show ((([(3, 1), (13, 1), (909436064694478667316432001, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_13, prime_thirtyAB_909436064694478667316432001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848040 : Nat.totient 35468006523084668025340848040 = 14160493283226141610141286400 := by
  rw [← show ((([(2, 3), (5, 1), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_5, prime_thirtyAB_769, prime_thirtyAB_2143, prime_thirtyAB_8597, prime_thirtyAB_9792301, prime_thirtyAB_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848041 : Nat.totient 35468006523084668025340848041 = 34557827328523828349380483200 := by
  rw [← show ((([(41, 1), (1063, 1), (3643, 1), (11279, 1), (19805686049008091, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_41, prime_thirtyAB_1063, prime_thirtyAB_3643, prime_thirtyAB_11279, prime_thirtyAB_19805686049008091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848042 : Nat.totient 35468006523084668025340848042 = 10043852580825757730349465600 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (113, 1), (54421, 1), (97654321, 1), (1406212853597, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_7, prime_thirtyAB_113, prime_thirtyAB_54421, prime_thirtyAB_97654321, prime_thirtyAB_1406212853597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848043 : Nat.totient 35468006523084668025340848043 = 34421301878210669641399794432 := by
  rw [← show ((([(43, 1), (157, 1), (49927, 1), (66107, 1), (1591789925487737, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_43, prime_thirtyAB_157, prime_thirtyAB_49927, prime_thirtyAB_66107, prime_thirtyAB_1591789925487737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848044 : Nat.totient 35468006523084668025340848044 = 16077414553359780765826473600 := by
  rw [← show ((([(2, 2), (11, 1), (367, 1), (33641, 1), (65290371830632690583, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_11, prime_thirtyAB_367, prime_thirtyAB_33641, prime_thirtyAB_65290371830632690583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848045 : Nat.totient 35468006523084668025340848045 = 18858596751130786945731072000 := by
  rw [← show ((([(3, 2), (5, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_5, prime_thirtyAB_421, prime_thirtyAB_1483, prime_thirtyAB_2072201, prime_thirtyAB_2567179, prime_thirtyAB_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848046 : Nat.totient 35468006523084668025340848046 = 16748238333046423068674265600 := by
  rw [← show ((([(2, 1), (23, 1), (79, 1), (82621199, 1), (325800521, 1), (362583961, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_23, prime_thirtyAB_79, prime_thirtyAB_82621199, prime_thirtyAB_325800521, prime_thirtyAB_362583961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848047 : Nat.totient 35468006523084668025340848047 = 34713368086423292109908064000 := by
  rw [← show ((([(47, 1), (754638436661375915432784001, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_47, prime_thirtyAB_754638436661375915432784001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848048 : Nat.totient 35468006523084668025340848048 = 11680218790863874308291942400 := by
  rw [← show ((([(2, 4), (3, 1), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_83, prime_thirtyAB_1433741, prime_thirtyAB_106163831, prime_thirtyAB_58488456857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848049 : Nat.totient 35468006523084668025340848049 = 30144739038203112694467037200 := by
  rw [← show ((([(7, 3), (191, 1), (311, 1), (1740800101532813178943, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_7, prime_thirtyAB_191, prime_thirtyAB_311, prime_thirtyAB_1740800101532813178943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848050 : Nat.totient 35468006523084668025340848050 = 14117584820985319161762892800 := by
  rw [← show ((([(2, 1), (5, 2), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_5, prime_thirtyAB_281, prime_thirtyAB_739, prime_thirtyAB_3540386347, prime_thirtyAB_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848051 : Nat.totient 35468006523084668025340848051 = 22254435464550222807481075200 := by
  rw [← show ((([(3, 1), (17, 1), (24330664621, 1), (28583317353999781, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_17, prime_thirtyAB_24330664621, prime_thirtyAB_28583317353999781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848052 : Nat.totient 35468006523084668025340848052 = 16249838054458671858537179136 := by
  rw [← show ((([(2, 2), (13, 1), (137, 1), (31063, 1), (912772537, 1), (175592882183, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_13, prime_thirtyAB_137, prime_thirtyAB_31063, prime_thirtyAB_912772537, prime_thirtyAB_175592882183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848053 : Nat.totient 35468006523084668025340848053 = 34585309289323445241980695824 := by
  rw [← show ((([(53, 1), (163, 1), (4105568529121966434233227, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_53, prime_thirtyAB_163, prime_thirtyAB_4105568529121966434233227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848054 : Nat.totient 35468006523084668025340848054 = 11801564591366053555799364864 := by
  rw [← show ((([(2, 1), (3, 3), (569, 1), (37039, 1), (1544987, 1), (20171893710853, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_569, prime_thirtyAB_37039, prime_thirtyAB_1544987, prime_thirtyAB_20171893710853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848055 : Nat.totient 35468006523084668025340848055 = 25794518671190466351030764160 := by
  rw [← show ((([(5, 1), (11, 1), (97327, 1), (208223, 1), (4129087, 1), (7706514863, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_5, prime_thirtyAB_11, prime_thirtyAB_97327, prime_thirtyAB_208223, prime_thirtyAB_4129087, prime_thirtyAB_7706514863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848056 : Nat.totient 35468006523084668025340848056 = 15200574224179143439431792000 := by
  rw [← show ((([(2, 3), (7, 1), (633357259340797643309658001, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_7, prime_thirtyAB_633357259340797643309658001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848057 : Nat.totient 35468006523084668025340848057 = 22400836868545842319131133440 := by
  rw [← show ((([(3, 1), (19, 1), (2428859, 1), (167470561, 1), (1529752406099, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_19, prime_thirtyAB_2428859, prime_thirtyAB_167470561, prime_thirtyAB_1529752406099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848058 : Nat.totient 35468006523084668025340848058 = 17077763509722148036096016640 := by
  rw [← show ((([(2, 1), (29, 1), (383, 1), (1056241, 1), (1511635180256161967, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_29, prime_thirtyAB_383, prime_thirtyAB_1056241, prime_thirtyAB_1511635180256161967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848059 : Nat.totient 35468006523084668025340848059 = 34864131573355804980492613920 := by
  rw [← show ((([(59, 1), (12893, 1), (1939867, 1), (24035813759802671, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_59, prime_thirtyAB_12893, prime_thirtyAB_1939867, prime_thirtyAB_24035813759802671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848060 : Nat.totient 35468006523084668025340848060 = 9458135065086595926115297600 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_5, prime_thirtyAB_1222615931, prime_thirtyAB_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848061 : Nat.totient 35468006523084668025340848061 = 34654434984564424011896686080 := by
  rw [← show ((([(61, 1), (167, 1), (1493, 1), (87584729, 1), (26625776075699, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_61, prime_thirtyAB_167, prime_thirtyAB_1493, prime_thirtyAB_87584729, prime_thirtyAB_26625776075699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848062 : Nat.totient 35468006523084668025340848062 = 17160796015907491722944332800 := by
  rw [← show ((([(2, 1), (31, 1), (15073, 1), (4979131, 1), (33351053, 1), (228550559, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_31, prime_thirtyAB_15073, prime_thirtyAB_4979131, prime_thirtyAB_33351053, prime_thirtyAB_228550559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848063 : Nat.totient 35468006523084668025340848063 = 20267432208937314285104498832 := by
  rw [← show ((([(3, 2), (7, 1), (225273263, 1), (2499116952574853327, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_7, prime_thirtyAB_225273263, prime_thirtyAB_2499116952574853327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848064 : Nat.totient 35468006523084668025340848064 = 17734003259182272770537103104 := by
  rw [← show ((([(2, 6), (7514213933, 1), (73751906302452347, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_7514213933, prime_thirtyAB_73751906302452347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848065 : Nat.totient 35468006523084668025340848065 = 26191758663200985618713241600 := by
  rw [← show ((([(5, 1), (13, 1), (545661638816687200389859201, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_5, prime_thirtyAB_13, prime_thirtyAB_545661638816687200389859201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848066 : Nat.totient 35468006523084668025340848066 = 10596502161856110116733916800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (71, 1), (26687336297, 1), (283615046165023, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_11, prime_thirtyAB_71, prime_thirtyAB_26687336297, prime_thirtyAB_283615046165023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848067 : Nat.totient 35468006523084668025340848067 = 35463042027337919098847357664 := by
  rw [← show ((([(7219, 1), (690629, 1), (7114017466219560317, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_7219, prime_thirtyAB_690629, prime_thirtyAB_7114017466219560317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848068 : Nat.totient 35468006523084668025340848068 = 16441709784130158323103221760 := by
  rw [← show ((([(2, 2), (17, 1), (67, 1), (293769120283, 1), (26500063922641, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_17, prime_thirtyAB_67, prime_thirtyAB_293769120283, prime_thirtyAB_26500063922641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848069 : Nat.totient 35468006523084668025340848069 = 22589996518050324023003175360 := by
  rw [← show ((([(3, 1), (23, 1), (829, 1), (56624411, 1), (10950386820164879, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_23, prime_thirtyAB_829, prime_thirtyAB_56624411, prime_thirtyAB_10950386820164879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848070 : Nat.totient 35468006523084668025340848070 = 12143732174124047542787144832 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_5, prime_thirtyAB_7, prime_thirtyAB_727, prime_thirtyAB_40346827, prime_thirtyAB_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848071 : Nat.totient 35468006523084668025340848071 = 35322719208728996321080473600 := by
  rw [← show ((([(487, 1), (631, 1), (2741, 1), (10177, 1), (4137610917680299, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_487, prime_thirtyAB_631, prime_thirtyAB_2741, prime_thirtyAB_10177, prime_thirtyAB_4137610917680299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848072 : Nat.totient 35468006523084668025340848072 = 11714188603258043153623613952 := by
  rw [← show ((([(2, 3), (3, 2), (109, 1), (762563, 1), (500452427, 1), (11842387189, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_109, prime_thirtyAB_762563, prime_thirtyAB_500452427, prime_thirtyAB_11842387189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848073 : Nat.totient 35468006523084668025340848073 = 35467998100438677440928877008 := by
  rw [← show ((([(4211029, 1), (8422645990584407760037, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_4211029, prime_thirtyAB_8422645990584407760037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848074 : Nat.totient 35468006523084668025340848074 = 17254691634756876898718230272 := by
  rw [← show ((([(2, 1), (37, 1), (1211593, 1), (395592732416818278457, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_37, prime_thirtyAB_1211593, prime_thirtyAB_395592732416818278457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848075 : Nat.totient 35468006523084668025340848075 = 18832753673753496183975381120 := by
  rw [← show ((([(3, 1), (5, 2), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_5, prime_thirtyAB_239, prime_thirtyAB_4327, prime_thirtyAB_1214459, prime_thirtyAB_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848076 : Nat.totient 35468006523084668025340848076 = 16792592172736510180854876672 := by
  rw [← show ((([(2, 2), (19, 1), (2089, 1), (251162293, 1), (889467958641013, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_19, prime_thirtyAB_2089, prime_thirtyAB_251162293, prime_thirtyAB_889467958641013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848077 : Nat.totient 35468006523084668025340848077 = 27637407680325715344421440000 := by
  rw [← show ((([(7, 1), (11, 1), (460623461338761922407024001, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_7, prime_thirtyAB_11, prime_thirtyAB_460623461338761922407024001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848078 : Nat.totient 35468006523084668025340848078 = 10888675595149121812154112000 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (599, 1), (1811, 1), (33809, 1), (12398369604474701, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_13, prime_thirtyAB_599, prime_thirtyAB_1811, prime_thirtyAB_33809, prime_thirtyAB_12398369604474701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848079 : Nat.totient 35468006523084668025340848079 = 35310824238719078565291135360 := by
  rw [← show ((([(269, 1), (2003, 1), (4679, 1), (437819, 1), (591091, 1), (54362767, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_269, prime_thirtyAB_2003, prime_thirtyAB_4679, prime_thirtyAB_437819, prime_thirtyAB_591091, prime_thirtyAB_54362767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848080 : Nat.totient 35468006523084668025340848080 = 14148802857292038353182556160 := by
  rw [← show ((([(2, 4), (5, 1), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_5, prime_thirtyAB_373, prime_thirtyAB_55249, prime_thirtyAB_157429, prime_thirtyAB_773027, prime_thirtyAB_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848081 : Nat.totient 35468006523084668025340848081 = 23645337682056445350227232000 := by
  rw [← show ((([(3, 4), (437876623741786025004208001, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_437876623741786025004208001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848082 : Nat.totient 35468006523084668025340848082 = 17300808953649091232864409600 := by
  rw [← show ((([(2, 1), (41, 1), (42743, 1), (68483, 1), (77945521, 1), (1895762749, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_41, prime_thirtyAB_42743, prime_thirtyAB_68483, prime_thirtyAB_77945521, prime_thirtyAB_1895762749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848083 : Nat.totient 35468006523084668025340848083 = 35468006251870210737853278144 := by
  rw [← show ((([(132963293, 1), (12907356487, 1), (20666537113, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_132963293, prime_thirtyAB_12907356487, prime_thirtyAB_20666537113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848084 : Nat.totient 35468006523084668025340848084 = 10133716143389275870640042496 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (1671268889, 1), (252645265925168009, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_7, prime_thirtyAB_1671268889, prime_thirtyAB_252645265925168009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848085 : Nat.totient 35468006523084668025340848085 = 26388411916778949474603251712 := by
  rw [← show ((([(5, 1), (17, 1), (89, 1), (1567, 1), (2991981134619696139127, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_5, prime_thirtyAB_17, prime_thirtyAB_89, prime_thirtyAB_1567, prime_thirtyAB_2991981134619696139127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848086 : Nat.totient 35468006523084668025340848086 = 17295058417823828291710311216 := by
  rw [← show ((([(2, 1), (43, 2), (653, 1), (14687798016346184405519, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_43, prime_thirtyAB_653, prime_thirtyAB_14687798016346184405519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848087 : Nat.totient 35468006523084668025340848087 = 22829981210261395510564224000 := by
  rw [← show ((([(3, 1), (29, 1), (407678235897524919831504001, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_29, prime_thirtyAB_407678235897524919831504001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848088 : Nat.totient 35468006523084668025340848088 = 16080376823915928404010009600 := by
  rw [← show ((([(2, 3), (11, 1), (389, 1), (305476361, 1), (3391773930127669, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_11, prime_thirtyAB_389, prime_thirtyAB_305476361, prime_thirtyAB_3391773930127669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848089 : Nat.totient 35468006523084668025340848089 = 35465949083620578609127437552 := by
  rw [← show ((([(17239, 1), (3177784469, 1), (647441109840979, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_17239, prime_thirtyAB_3177784469, prime_thirtyAB_647441109840979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848090 : Nat.totient 35468006523084668025340848090 = 9458135072822578140090892800 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_5, prime_thirtyAB_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848091 : Nat.totient 35468006523084668025340848091 = 27331895882745912384540057600 := by
  rw [← show ((([(7, 1), (13, 1), (73, 1), (107, 1), (313, 1), (4078951, 1), (39083722743557, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_7, prime_thirtyAB_13, prime_thirtyAB_73, prime_thirtyAB_107, prime_thirtyAB_313, prime_thirtyAB_4078951, prime_thirtyAB_39083722743557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848092 : Nat.totient 35468006523084668025340848092 = 16962959631660521422761810608 := by
  rw [← show ((([(2, 2), (23, 1), (1728312167, 1), (223062602575272503, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_23, prime_thirtyAB_1728312167, prime_thirtyAB_223062602575272503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848093 : Nat.totient 35468006523084668025340848093 = 22756123348131671550520416000 := by
  rw [← show ((([(3, 1), (31, 1), (181, 1), (609781, 1), (21346979, 1), (161869470179, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_31, prime_thirtyAB_181, prime_thirtyAB_609781, prime_thirtyAB_21346979, prime_thirtyAB_161869470179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848094 : Nat.totient 35468006523084668025340848094 = 17356684041958080915623466400 := by
  rw [← show ((([(2, 1), (47, 1), (13845864341, 1), (27251402226539261, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_47, prime_thirtyAB_13845864341, prime_thirtyAB_27251402226539261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848095 : Nat.totient 35468006523084668025340848095 = 26881005559479988859243034624 := by
  rw [← show ((([(5, 1), (19, 1), (2712337, 1), (137647879701195599473, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_5, prime_thirtyAB_19, prime_thirtyAB_2712337, prime_thirtyAB_137647879701195599473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848096 : Nat.totient 35468006523084668025340848096 = 11822668813725037826480400384 := by
  rw [← show ((([(2, 5), (3, 1), (433014277, 1), (853224526086773713, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_3, prime_thirtyAB_433014277, prime_thirtyAB_853224526086773713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848097 : Nat.totient 35468006523084668025340848097 = 35188729798032941501393748432 := by
  rw [← show ((([(127, 1), (32487773, 1), (8596330746156484907, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_127, prime_thirtyAB_32487773, prime_thirtyAB_8596330746156484907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848098 : Nat.totient 35468006523084668025340848098 = 15049485067130074421137670400 := by
  rw [← show ((([(2, 1), (7, 2), (101, 1), (25577, 1), (140100513382431394213, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848098 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_2, prime_thirtyAB_7, prime_thirtyAB_101, prime_thirtyAB_25577, prime_thirtyAB_140100513382431394213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyAB_35468006523084668025340848099 : Nat.totient 35468006523084668025340848099 = 21449717563935283189613942400 := by
  rw [← show ((([(3, 2), (11, 1), (467, 1), (1479571, 1), (518500159195792793, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668025340848099 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyAB_3, prime_thirtyAB_11, prime_thirtyAB_467, prime_thirtyAB_1479571, prime_thirtyAB_518500159195792793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64ThirtyAB : certifiedKill 1 35468006523084668025340847999 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_thirtyAB_35468006523084668025340848000, phi_thirtyAB_35468006523084668025340848001, phi_thirtyAB_35468006523084668025340848002,
    phi_thirtyAB_35468006523084668025340848003, phi_thirtyAB_35468006523084668025340848004, phi_thirtyAB_35468006523084668025340848005,
    phi_thirtyAB_35468006523084668025340848006, phi_thirtyAB_35468006523084668025340848007, phi_thirtyAB_35468006523084668025340848008,
    phi_thirtyAB_35468006523084668025340848009, phi_thirtyAB_35468006523084668025340848010, phi_thirtyAB_35468006523084668025340848011,
    phi_thirtyAB_35468006523084668025340848012, phi_thirtyAB_35468006523084668025340848013, phi_thirtyAB_35468006523084668025340848014,
    phi_thirtyAB_35468006523084668025340848015, phi_thirtyAB_35468006523084668025340848016, phi_thirtyAB_35468006523084668025340848017,
    phi_thirtyAB_35468006523084668025340848018, phi_thirtyAB_35468006523084668025340848019, phi_thirtyAB_35468006523084668025340848020,
    phi_thirtyAB_35468006523084668025340848021, phi_thirtyAB_35468006523084668025340848022, phi_thirtyAB_35468006523084668025340848023,
    phi_thirtyAB_35468006523084668025340848024, phi_thirtyAB_35468006523084668025340848025, phi_thirtyAB_35468006523084668025340848026,
    phi_thirtyAB_35468006523084668025340848027, phi_thirtyAB_35468006523084668025340848028, phi_thirtyAB_35468006523084668025340848029,
    phi_thirtyAB_35468006523084668025340848030, phi_thirtyAB_35468006523084668025340848031, phi_thirtyAB_35468006523084668025340848032,
    phi_thirtyAB_35468006523084668025340848033, phi_thirtyAB_35468006523084668025340848034, phi_thirtyAB_35468006523084668025340848035,
    phi_thirtyAB_35468006523084668025340848036, phi_thirtyAB_35468006523084668025340848037, phi_thirtyAB_35468006523084668025340848038,
    phi_thirtyAB_35468006523084668025340848039, phi_thirtyAB_35468006523084668025340848040, phi_thirtyAB_35468006523084668025340848041,
    phi_thirtyAB_35468006523084668025340848042, phi_thirtyAB_35468006523084668025340848043, phi_thirtyAB_35468006523084668025340848044,
    phi_thirtyAB_35468006523084668025340848045, phi_thirtyAB_35468006523084668025340848046, phi_thirtyAB_35468006523084668025340848047,
    phi_thirtyAB_35468006523084668025340848048, phi_thirtyAB_35468006523084668025340848049, phi_thirtyAB_35468006523084668025340848050,
    phi_thirtyAB_35468006523084668025340848051, phi_thirtyAB_35468006523084668025340848052, phi_thirtyAB_35468006523084668025340848053,
    phi_thirtyAB_35468006523084668025340848054, phi_thirtyAB_35468006523084668025340848055, phi_thirtyAB_35468006523084668025340848056,
    phi_thirtyAB_35468006523084668025340848057, phi_thirtyAB_35468006523084668025340848058, phi_thirtyAB_35468006523084668025340848059,
    phi_thirtyAB_35468006523084668025340848060, phi_thirtyAB_35468006523084668025340848061, phi_thirtyAB_35468006523084668025340848062,
    phi_thirtyAB_35468006523084668025340848063, phi_thirtyAB_35468006523084668025340848064, phi_thirtyAB_35468006523084668025340848065,
    phi_thirtyAB_35468006523084668025340848066, phi_thirtyAB_35468006523084668025340848067, phi_thirtyAB_35468006523084668025340848068,
    phi_thirtyAB_35468006523084668025340848069, phi_thirtyAB_35468006523084668025340848070, phi_thirtyAB_35468006523084668025340848071,
    phi_thirtyAB_35468006523084668025340848072, phi_thirtyAB_35468006523084668025340848073, phi_thirtyAB_35468006523084668025340848074,
    phi_thirtyAB_35468006523084668025340848075, phi_thirtyAB_35468006523084668025340848076, phi_thirtyAB_35468006523084668025340848077,
    phi_thirtyAB_35468006523084668025340848078, phi_thirtyAB_35468006523084668025340848079, phi_thirtyAB_35468006523084668025340848080,
    phi_thirtyAB_35468006523084668025340848081, phi_thirtyAB_35468006523084668025340848082, phi_thirtyAB_35468006523084668025340848083,
    phi_thirtyAB_35468006523084668025340848084, phi_thirtyAB_35468006523084668025340848085, phi_thirtyAB_35468006523084668025340848086,
    phi_thirtyAB_35468006523084668025340848087, phi_thirtyAB_35468006523084668025340848088, phi_thirtyAB_35468006523084668025340848089,
    phi_thirtyAB_35468006523084668025340848090, phi_thirtyAB_35468006523084668025340848091, phi_thirtyAB_35468006523084668025340848092,
    phi_thirtyAB_35468006523084668025340848093, phi_thirtyAB_35468006523084668025340848094, phi_thirtyAB_35468006523084668025340848095,
    phi_thirtyAB_35468006523084668025340848096, phi_thirtyAB_35468006523084668025340848097, phi_thirtyAB_35468006523084668025340848098,
    phi_thirtyAB_35468006523084668025340848099]

end TotientTailPeriodKiller
end Erdos249257
