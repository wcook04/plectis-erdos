import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def twentyOneSFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem twentyOneSFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    twentyOneSFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [twentyOneSFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [twentyOneSFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then twentyOneSFastPow a n * twentyOneSFastPow a n * a
        else twentyOneSFastPow a n * twentyOneSFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_twentyOneS_2 : Nat.Prime 2 := by norm_num
private theorem prime_twentyOneS_3 : Nat.Prime 3 := by norm_num
private theorem prime_twentyOneS_5 : Nat.Prime 5 := by norm_num
private theorem prime_twentyOneS_7 : Nat.Prime 7 := by norm_num
private theorem prime_twentyOneS_11 : Nat.Prime 11 := by norm_num
private theorem prime_twentyOneS_13 : Nat.Prime 13 := by norm_num
private theorem prime_twentyOneS_17 : Nat.Prime 17 := by norm_num
private theorem prime_twentyOneS_19 : Nat.Prime 19 := by norm_num
private theorem prime_twentyOneS_23 : Nat.Prime 23 := by norm_num
private theorem prime_twentyOneS_29 : Nat.Prime 29 := by norm_num
private theorem prime_twentyOneS_31 : Nat.Prime 31 := by norm_num
private theorem prime_twentyOneS_37 : Nat.Prime 37 := by norm_num
private theorem prime_twentyOneS_41 : Nat.Prime 41 := by norm_num
private theorem prime_twentyOneS_43 : Nat.Prime 43 := by norm_num
private theorem prime_twentyOneS_47 : Nat.Prime 47 := by norm_num
private theorem prime_twentyOneS_53 : Nat.Prime 53 := by norm_num
private theorem prime_twentyOneS_59 : Nat.Prime 59 := by norm_num
private theorem prime_twentyOneS_61 : Nat.Prime 61 := by norm_num
private theorem prime_twentyOneS_487 : Nat.Prime 487 := by norm_num
private theorem prime_twentyOneS_10972711 : Nat.Prime 10972711 := by norm_num
private theorem prime_twentyOneS_499 : Nat.Prime 499 := by norm_num
private theorem prime_twentyOneS_2915719 : Nat.Prime 2915719 := by norm_num
private theorem prime_twentyOneS_8729662687 : Nat.Prime 8729662687 := by
  apply lucas_primality 8729662687 (3 : ZMod 8729662687)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (499, 1), (2915719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (499, 1), (2915719, 1)] : List FactorBlock).map factorBlockValue).prod = 8729662687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_499
      · exact prime_twentyOneS_2915719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8729662687) ^ 4364831343 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8729662687) ^ 2909887562 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8729662687) ^ 17494314 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8729662687) ^ 2994 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_61107638809001 : Nat.Prime 61107638809001 := by
  apply lucas_primality 61107638809001 (6 : ZMod 61107638809001)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 3), (7, 1), (8729662687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 3), (7, 1), (8729662687, 1)] : List FactorBlock).map factorBlockValue).prod = 61107638809001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_8729662687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 61107638809001) ^ 30553819404500 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 61107638809001) ^ 12221527761800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 61107638809001) ^ 8729662687000 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 61107638809001) ^ 7000 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_122215277618003 : Nat.Prime 122215277618003 := by
  apply lucas_primality 122215277618003 (2 : ZMod 122215277618003)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (61107638809001, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (61107638809001, 1)] : List FactorBlock).map factorBlockValue).prod = 122215277618003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_61107638809001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 122215277618003) ^ 61107638809001 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 122215277618003) ^ 2 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_32264833291152793 : Nat.Prime 32264833291152793 := by
  apply lucas_primality 32264833291152793 (5 : ZMod 32264833291152793)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (122215277618003, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (122215277618003, 1)] : List FactorBlock).map factorBlockValue).prod = 32264833291152793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_122215277618003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 32264833291152793) ^ 16132416645576396 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 32264833291152793) ^ 10754944430384264 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 32264833291152793) ^ 2933166662832072 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 32264833291152793) ^ 264 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_4646135993926002193 : Nat.Prime 4646135993926002193 := by
  apply lucas_primality 4646135993926002193 (10 : ZMod 4646135993926002193)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (32264833291152793, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (32264833291152793, 1)] : List FactorBlock).map factorBlockValue).prod = 4646135993926002193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_32264833291152793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 4646135993926002193) ^ 2323067996963001096 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 4646135993926002193) ^ 1548711997975334064 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 4646135993926002193) ^ 144 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_12413802283079633808869296801 : Nat.Prime 12413802283079633808869296801 := by
  apply lucas_primality 12413802283079633808869296801 (71 : ZMod 12413802283079633808869296801)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 12413802283079633808869296801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 12413802283079633808869296801) ^ 6206901141539816904434648400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 4137934094359877936289765600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 2482760456615926761773859360 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 1773400326154233401267042400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 1128527480279966709897208800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 954907867929202600682253600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 730223663710566694639370400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 653358014898928095203647200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 539730534046940600385621600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 428062147692401165823079200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 400445234938052703511912800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 335508169812963075915386400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 302775665440966678265104800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 288693076350689158345797600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 264123452831481570401474400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 234222684586408185073005600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 210403428526773454387615200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 203504955460321865719168800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_127487 : Nat.Prime 127487 := by norm_num
private theorem prime_twentyOneS_6475879 : Nat.Prime 6475879 := by norm_num
private theorem prime_twentyOneS_293 : Nat.Prime 293 := by norm_num
private theorem prime_twentyOneS_317 : Nat.Prime 317 := by norm_num
private theorem prime_twentyOneS_293147 : Nat.Prime 293147 := by norm_num
private theorem prime_twentyOneS_38554545693913 : Nat.Prime 38554545693913 := by
  apply lucas_primality 38554545693913 (10 : ZMod 38554545693913)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod = 38554545693913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_293
      · exact prime_twentyOneS_317
      · exact prime_twentyOneS_293147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 38554545693913) ^ 19277272846956 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 12851515231304 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 653466876168 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131585480184 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 121623172536 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131519496 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_32457694465787711188511 : Nat.Prime 32457694465787711188511 := by
  apply lucas_primality 32457694465787711188511 (7 : ZMod 32457694465787711188511)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod = 32457694465787711188511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_6475879
      · exact prime_twentyOneS_38554545693913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32457694465787711188511) ^ 16228847232893855594255 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 6491538893157542237702 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 2496745728137516245270 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 5012090940208690 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 841864270 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_64915388931575422377023 : Nat.Prime 64915388931575422377023 := by
  apply lucas_primality 64915388931575422377023 (5 : ZMod 64915388931575422377023)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod = 64915388931575422377023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_32457694465787711188511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 64915388931575422377023) ^ 32457694465787711188511 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 64915388931575422377023) ^ 2 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_555253 : Nat.Prime 555253 := by norm_num
private theorem prime_twentyOneS_117497 : Nat.Prime 117497 := by norm_num
private theorem prime_twentyOneS_5231 : Nat.Prime 5231 := by norm_num
private theorem prime_twentyOneS_784367 : Nat.Prime 784367 := by norm_num
private theorem prime_twentyOneS_13392269608129 : Nat.Prime 13392269608129 := by
  apply lucas_primality 13392269608129 (14 : ZMod 13392269608129)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (17, 1), (5231, 1), (784367, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (17, 1), (5231, 1), (784367, 1)] : List FactorBlock).map factorBlockValue).prod = 13392269608129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_5231
      · exact prime_twentyOneS_784367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 13392269608129) ^ 6696134804064 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 13392269608129) ^ 4464089869376 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 13392269608129) ^ 787780565184 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 13392269608129) ^ 2560173888 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 13392269608129) ^ 17073984 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_7928223608012369 : Nat.Prime 7928223608012369 := by
  apply lucas_primality 7928223608012369 (3 : ZMod 7928223608012369)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (37, 1), (13392269608129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (37, 1), (13392269608129, 1)] : List FactorBlock).map factorBlockValue).prod = 7928223608012369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_13392269608129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7928223608012369) ^ 3964111804006184 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 7928223608012369) ^ 214276313730064 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 7928223608012369) ^ 592 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_11178509871247551844717 : Nat.Prime 11178509871247551844717 := by
  apply lucas_primality 11178509871247551844717 (2 : ZMod 11178509871247551844717)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (117497, 1), (7928223608012369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (117497, 1), (7928223608012369, 1)] : List FactorBlock).map factorBlockValue).prod = 11178509871247551844717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_117497
      · exact prime_twentyOneS_7928223608012369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11178509871247551844717) ^ 5589254935623775922358 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11178509871247551844717) ^ 3726169957082517281572 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11178509871247551844717) ^ 95138683296148428 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11178509871247551844717) ^ 1409964 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_15756119 : Nat.Prime 15756119 := by norm_num
private theorem prime_twentyOneS_14962183 : Nat.Prime 14962183 := by norm_num
private theorem prime_twentyOneS_8977309801 : Nat.Prime 8977309801 := by
  apply lucas_primality 8977309801 (19 : ZMod 8977309801)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (14962183, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (14962183, 1)] : List FactorBlock).map factorBlockValue).prod = 8977309801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_14962183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 8977309801) ^ 4488654900 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (19 : ZMod 8977309801) ^ 2992436600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (19 : ZMod 8977309801) ^ 1795461960 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (19 : ZMod 8977309801) ^ 600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_67 : Nat.Prime 67 := by norm_num
private theorem prime_twentyOneS_107 : Nat.Prime 107 := by norm_num
private theorem prime_twentyOneS_13093 : Nat.Prime 13093 := by norm_num
private theorem prime_twentyOneS_35105030159 : Nat.Prime 35105030159 := by
  apply lucas_primality 35105030159 (11 : ZMod 35105030159)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (67, 1), (107, 1), (13093, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (67, 1), (107, 1), (13093, 1)] : List FactorBlock).map factorBlockValue).prod = 35105030159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_67
      · exact prime_twentyOneS_107
      · exact prime_twentyOneS_13093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 35105030159) ^ 17552515079 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 35105030159) ^ 3191366378 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 35105030159) ^ 2065001774 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 35105030159) ^ 523955674 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 35105030159) ^ 328084394 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 35105030159) ^ 2681206 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_363611 : Nat.Prime 363611 := by norm_num
private theorem prime_twentyOneS_19379 : Nat.Prime 19379 := by norm_num
private theorem prime_twentyOneS_311677 : Nat.Prime 311677 := by norm_num
private theorem prime_twentyOneS_2846287 : Nat.Prime 2846287 := by norm_num
private theorem prime_twentyOneS_216317813 : Nat.Prime 216317813 := by
  apply lucas_primality 216317813 (2 : ZMod 216317813)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod = 216317813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_2846287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 216317813) ^ 108158906 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 11385148 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 76 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_11380112522338097407091 : Nat.Prime 11380112522338097407091 := by
  apply lucas_primality 11380112522338097407091 (2 : ZMod 11380112522338097407091)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod = 11380112522338097407091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_67
      · exact prime_twentyOneS_19379
      · exact prime_twentyOneS_311677
      · exact prime_twentyOneS_216317813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11380112522338097407091) ^ 5690056261169048703545 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 2276022504467619481418 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 875393270949084415930 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 169852425706538767270 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 587239409790912710 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 36512519442686170 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 52608300557930 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_71 : Nat.Prime 71 := by norm_num
private theorem prime_twentyOneS_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_twentyOneS_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_71
      · exact prime_twentyOneS_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_twentyOneS_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_twentyOneS_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_81047
      · exact prime_twentyOneS_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_101 : Nat.Prime 101 := by norm_num
private theorem prime_twentyOneS_16499213 : Nat.Prime 16499213 := by norm_num
private theorem prime_twentyOneS_157 : Nat.Prime 157 := by norm_num
private theorem prime_twentyOneS_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_twentyOneS_10339193 : Nat.Prime 10339193 := by norm_num
private theorem prime_twentyOneS_29073707324071 : Nat.Prime 29073707324071 := by
  apply lucas_primality 29073707324071 (3 : ZMod 29073707324071)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (67, 1), (1399, 1), (10339193, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (67, 1), (1399, 1), (10339193, 1)] : List FactorBlock).map factorBlockValue).prod = 29073707324071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_67
      · exact prime_twentyOneS_1399
      · exact prime_twentyOneS_10339193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29073707324071) ^ 14536853662035 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 29073707324071) ^ 9691235774690 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 29073707324071) ^ 5814741464814 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 29073707324071) ^ 433935930210 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 29073707324071) ^ 20781777930 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 29073707324071) ^ 2811990 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1862345396350691977 : Nat.Prime 1862345396350691977 := by
  apply lucas_primality 1862345396350691977 (10 : ZMod 1862345396350691977)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (17, 1), (157, 1), (29073707324071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (17, 1), (157, 1), (29073707324071, 1)] : List FactorBlock).map factorBlockValue).prod = 1862345396350691977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_157
      · exact prime_twentyOneS_29073707324071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1862345396350691977) ^ 931172698175345988 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1862345396350691977) ^ 620781798783563992 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1862345396350691977) ^ 109549729197099528 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1862345396350691977) ^ 11862072588220968 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1862345396350691977) ^ 64056 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_137 : Nat.Prime 137 := by norm_num
private theorem prime_twentyOneS_991 : Nat.Prime 991 := by norm_num
private theorem prime_twentyOneS_3779417 : Nat.Prime 3779417 := by norm_num
private theorem prime_twentyOneS_5779 : Nat.Prime 5779 := by norm_num
private theorem prime_twentyOneS_1693169 : Nat.Prime 1693169 := by norm_num
private theorem prime_twentyOneS_39530687550041 : Nat.Prime 39530687550041 := by
  apply lucas_primality 39530687550041 (3 : ZMod 39530687550041)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod = 39530687550041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_101
      · exact prime_twentyOneS_5779
      · exact prime_twentyOneS_1693169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39530687550041) ^ 19765343775020 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 7906137510008 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 391392946040 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 6840402760 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 23347160 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_20135932332651474142529273 : Nat.Prime 20135932332651474142529273 := by
  apply lucas_primality 20135932332651474142529273 (3 : ZMod 20135932332651474142529273)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod = 20135932332651474142529273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_991
      · exact prime_twentyOneS_3779417
      · exact prime_twentyOneS_39530687550041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20135932332651474142529273) ^ 10067966166325737071264636 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 1184466607803027890737016 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 20318801546570609629192 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 5327787945244325816 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 509374705592 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2482760456615926761773859361 : Nat.Prime 2482760456615926761773859361 := by
  apply lucas_primality 2482760456615926761773859361 (103 : ZMod 2482760456615926761773859361)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 1), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 1), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 2482760456615926761773859361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 2482760456615926761773859361) ^ 1241380228307963380886929680 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 827586818871975587257953120 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 496552091323185352354771872 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 354680065230846680253408480 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 225705496055993341979441760 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 190981573585840520136450720 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 146044732742113338927874080 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 130671602979785619040729440 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 107946106809388120077124320 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 85612429538480233164615840 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 80089046987610540702382560 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 67101633962592615183077280 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 60555133088193335653020960 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 57738615270137831669159520 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 52824690566296314080294880 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 46844536917281637014601120 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 42080685705354690877523040 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 40700991092064373143833760 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2257054960559933419794417601 : Nat.Prime 2257054960559933419794417601 := by
  apply lucas_primality 2257054960559933419794417601 (142 : ZMod 2257054960559933419794417601)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 2257054960559933419794417601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (142 : ZMod 2257054960559933419794417601) ^ 1128527480279966709897208800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 752351653519977806598139200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 451410992111986683958883520 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 322436422937133345684916800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 173619612350764109214955200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 132767938856466671752612800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 118792366345259653673390400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 98132824372171018251931200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 77829481398618393786014400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 72808224534191400638529600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 61001485420538741075524800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 55050120989266668775473600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 52489650245579846971963200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 48022445969360285527540800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 42585942652074215467819200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 38255168823049718979566400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 37000900992785793767121600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_twentyOneS_7309 : Nat.Prime 7309 := by norm_num
private theorem prime_twentyOneS_139 : Nat.Prime 139 := by norm_num
private theorem prime_twentyOneS_413869 : Nat.Prime 413869 := by norm_num
private theorem prime_twentyOneS_73 : Nat.Prime 73 := by norm_num
private theorem prime_twentyOneS_367219 : Nat.Prime 367219 := by norm_num
private theorem prime_twentyOneS_73987284121 : Nat.Prime 73987284121 := by
  apply lucas_primality 73987284121 (29 : ZMod 73987284121)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod = 73987284121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_73
      · exact prime_twentyOneS_367219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 73987284121) ^ 36993642060 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 24662428040 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 14797456824 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 3216838440 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 1013524440 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 201480 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_93639150386551147643 : Nat.Prime 93639150386551147643 := by
  apply lucas_primality 93639150386551147643 (2 : ZMod 93639150386551147643)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod = 93639150386551147643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_139
      · exact prime_twentyOneS_413869
      · exact prime_twentyOneS_73987284121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93639150386551147643) ^ 46819575193275573821 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 8512650035141013422 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 673662952421231278 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 226253114842018 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 1265611402 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_547 : Nat.Prime 547 := by norm_num
private theorem prime_twentyOneS_47717 : Nat.Prime 47717 := by norm_num
private theorem prime_twentyOneS_436081 : Nat.Prime 436081 := by norm_num
private theorem prime_twentyOneS_1634609 : Nat.Prime 1634609 := by norm_num
private theorem prime_twentyOneS_2443997 : Nat.Prime 2443997 := by norm_num
private theorem prime_twentyOneS_3491436445810612799569483 : Nat.Prime 3491436445810612799569483 := by
  apply lucas_primality 3491436445810612799569483 (5 : ZMod 3491436445810612799569483)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (47717, 1), (436081, 1), (1634609, 1), (2443997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (47717, 1), (436081, 1), (1634609, 1), (2443997, 1)] : List FactorBlock).map factorBlockValue).prod = 3491436445810612799569483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_47717
      · exact prime_twentyOneS_436081
      · exact prime_twentyOneS_1634609
      · exact prime_twentyOneS_2443997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3491436445810612799569483) ^ 1745718222905306399784741 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 1163812148603537599856494 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 498776635115801828509926 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 73169655380904348546 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 8006394329976799722 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 2135945933131784298 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 1428576404067031506 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_twentyOneS_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_twentyOneS_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_twentyOneS_149 : Nat.Prime 149 := by norm_num
private theorem prime_twentyOneS_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_twentyOneS_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_twentyOneS_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_149
      · exact prime_twentyOneS_1429
      · exact prime_twentyOneS_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_89 : Nat.Prime 89 := by norm_num
private theorem prime_twentyOneS_1173959 : Nat.Prime 1173959 := by norm_num
private theorem prime_twentyOneS_79 : Nat.Prime 79 := by norm_num
private theorem prime_twentyOneS_97 : Nat.Prime 97 := by norm_num
private theorem prime_twentyOneS_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_twentyOneS_8807 : Nat.Prime 8807 := by norm_num
private theorem prime_twentyOneS_22951043 : Nat.Prime 22951043 := by
  apply lucas_primality 22951043 (2 : ZMod 22951043)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1303, 1), (8807, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1303, 1), (8807, 1)] : List FactorBlock).map factorBlockValue).prod = 22951043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_1303
      · exact prime_twentyOneS_8807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22951043) ^ 11475521 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951043) ^ 17614 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951043) ^ 2606 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_21910764024983 : Nat.Prime 21910764024983 := by
  apply lucas_primality 21910764024983 (5 : ZMod 21910764024983)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod = 21910764024983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_97
      · exact prime_twentyOneS_22951043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21910764024983) ^ 10955382012491 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 3130109146426 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 1153198106578 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 592182811486 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 225884165206 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 954674 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_180018837229260329 : Nat.Prime 180018837229260329 := by
  apply lucas_primality 180018837229260329 (3 : ZMod 180018837229260329)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod = 180018837229260329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_79
      · exact prime_twentyOneS_21910764024983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 180018837229260329) ^ 90009418614630164 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 13847602863789256 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 2278719458598232 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 8216 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_18597456603864619938380969 : Nat.Prime 18597456603864619938380969 := by
  apply lucas_primality 18597456603864619938380969 (3 : ZMod 18597456603864619938380969)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod = 18597456603864619938380969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_1173959
      · exact prime_twentyOneS_180018837229260329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18597456603864619938380969) ^ 9298728301932309969190484 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 1690677873078601812580088 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 15841657676174908952 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 103308392 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_twentyOneS_4229 : Nat.Prime 4229 := by norm_num
private theorem prime_twentyOneS_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_twentyOneS_125789 : Nat.Prime 125789 := by norm_num
private theorem prime_twentyOneS_1351547 : Nat.Prime 1351547 := by norm_num
private theorem prime_twentyOneS_3273367641455083 : Nat.Prime 3273367641455083 := by
  apply lucas_primality 3273367641455083 (2 : ZMod 3273367641455083)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3209, 1), (125789, 1), (1351547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3209, 1), (125789, 1), (1351547, 1)] : List FactorBlock).map factorBlockValue).prod = 3273367641455083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_3209
      · exact prime_twentyOneS_125789
      · exact prime_twentyOneS_1351547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3273367641455083) ^ 1636683820727541 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273367641455083) ^ 1091122547151694 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273367641455083) ^ 1020058473498 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273367641455083) ^ 26022685938 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273367641455083) ^ 2421941406 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_567565941984255386287001 : Nat.Prime 567565941984255386287001 := by
  apply lucas_primality 567565941984255386287001 (3 : ZMod 567565941984255386287001)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 3), (41, 1), (4229, 1), (3273367641455083, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 3), (41, 1), (4229, 1), (3273367641455083, 1)] : List FactorBlock).map factorBlockValue).prod = 567565941984255386287001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_4229
      · exact prime_twentyOneS_3273367641455083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 567565941984255386287001) ^ 283782970992127693143500 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 567565941984255386287001) ^ 113513188396851077257400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 567565941984255386287001) ^ 13843071755713546007000 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 567565941984255386287001) ^ 134208073299658403000 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 567565941984255386287001) ^ 173389000 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1135131883968510772574003 : Nat.Prime 1135131883968510772574003 := by
  apply lucas_primality 1135131883968510772574003 (2 : ZMod 1135131883968510772574003)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (567565941984255386287001, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (567565941984255386287001, 1)] : List FactorBlock).map factorBlockValue).prod = 1135131883968510772574003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_567565941984255386287001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1135131883968510772574003) ^ 567565941984255386287001 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1135131883968510772574003) ^ 2 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_83 : Nat.Prime 83 := by norm_num
private theorem prime_twentyOneS_1543 : Nat.Prime 1543 := by norm_num
private theorem prime_twentyOneS_461 : Nat.Prime 461 := by norm_num
private theorem prime_twentyOneS_28537 : Nat.Prime 28537 := by norm_num
private theorem prime_twentyOneS_151883 : Nat.Prime 151883 := by norm_num
private theorem prime_twentyOneS_163063 : Nat.Prime 163063 := by norm_num
private theorem prime_twentyOneS_216706854253751 : Nat.Prime 216706854253751 := by
  apply lucas_primality 216706854253751 (7 : ZMod 216706854253751)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 4), (7, 1), (151883, 1), (163063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 4), (7, 1), (151883, 1), (163063, 1)] : List FactorBlock).map factorBlockValue).prod = 216706854253751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_151883
      · exact prime_twentyOneS_163063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 216706854253751) ^ 108353427126875 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 216706854253751) ^ 43341370850750 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 216706854253751) ^ 30958122036250 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 216706854253751) ^ 1426801250 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 216706854253751) ^ 1328976250 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_11403597493703654977229 : Nat.Prime 11403597493703654977229 := by
  apply lucas_primality 11403597493703654977229 (2 : ZMod 11403597493703654977229)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (461, 1), (28537, 1), (216706854253751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (461, 1), (28537, 1), (216706854253751, 1)] : List FactorBlock).map factorBlockValue).prod = 11403597493703654977229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_461
      · exact prime_twentyOneS_28537
      · exact prime_twentyOneS_216706854253751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11403597493703654977229) ^ 5701798746851827488614 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11403597493703654977229) ^ 24736653999357169148 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11403597493703654977229) ^ 399607439243916844 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11403597493703654977229) ^ 52622228 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_263 : Nat.Prime 263 := by norm_num
private theorem prime_twentyOneS_33811 : Nat.Prime 33811 := by norm_num
private theorem prime_twentyOneS_189853 : Nat.Prime 189853 := by norm_num
private theorem prime_twentyOneS_223 : Nat.Prime 223 := by norm_num
private theorem prime_twentyOneS_283 : Nat.Prime 283 := by norm_num
private theorem prime_twentyOneS_5843 : Nat.Prime 5843 := by norm_num
private theorem prime_twentyOneS_12589 : Nat.Prime 12589 := by norm_num
private theorem prime_twentyOneS_817016986973969 : Nat.Prime 817016986973969 := by
  apply lucas_primality 817016986973969 (3 : ZMod 817016986973969)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod = 817016986973969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_223
      · exact prime_twentyOneS_283
      · exact prime_twentyOneS_5843
      · exact prime_twentyOneS_12589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 817016986973969) ^ 408508493486984 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 74274271543088 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 3663753304816 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 2886985819696 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 139828339376 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 64899276112 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_503 : Nat.Prime 503 := by norm_num
private theorem prime_twentyOneS_28940609 : Nat.Prime 28940609 := by
  apply lucas_primality 28940609 (3 : ZMod 28940609)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (29, 1), (31, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (29, 1), (31, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod = 28940609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28940609) ^ 14470304 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 28940609) ^ 997952 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 28940609) ^ 933568 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 28940609) ^ 57536 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_109 : Nat.Prime 109 := by norm_num
private theorem prime_twentyOneS_232753 : Nat.Prime 232753 := by norm_num
private theorem prime_twentyOneS_680104267 : Nat.Prime 680104267 := by
  apply lucas_primality 680104267 (13 : ZMod 680104267)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (487, 1), (232753, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (487, 1), (232753, 1)] : List FactorBlock).map factorBlockValue).prod = 680104267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_487
      · exact prime_twentyOneS_232753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 680104267) ^ 340052133 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (13 : ZMod 680104267) ^ 226701422 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (13 : ZMod 680104267) ^ 1396518 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (13 : ZMod 680104267) ^ 2922 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_45151642448085877889 : Nat.Prime 45151642448085877889 := by
  apply lucas_primality 45151642448085877889 (3 : ZMod 45151642448085877889)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (29, 1), (31, 1), (67, 1), (79, 1), (109, 1), (680104267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (29, 1), (31, 1), (67, 1), (79, 1), (109, 1), (680104267, 1)] : List FactorBlock).map factorBlockValue).prod = 45151642448085877889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_67
      · exact prime_twentyOneS_79
      · exact prime_twentyOneS_109
      · exact prime_twentyOneS_680104267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45151642448085877889) ^ 22575821224042938944 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 1556953187865030272 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 1456504595099544448 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 673905111165460864 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 571539777823871872 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 414235251817301632 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 66389294464 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_52697 : Nat.Prime 52697 := by norm_num
private theorem prime_twentyOneS_38363417 : Nat.Prime 38363417 := by
  apply lucas_primality 38363417 (3 : ZMod 38363417)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (13, 1), (52697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (13, 1), (52697, 1)] : List FactorBlock).map factorBlockValue).prod = 38363417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_52697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38363417) ^ 19181708 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38363417) ^ 5480488 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38363417) ^ 2951032 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38363417) ^ 728 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_86317688251 : Nat.Prime 86317688251 := by
  apply lucas_primality 86317688251 (10 : ZMod 86317688251)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 3), (38363417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 3), (38363417, 1)] : List FactorBlock).map factorBlockValue).prod = 86317688251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_38363417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 86317688251) ^ 43158844125 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 86317688251) ^ 28772562750 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 86317688251) ^ 17263537650 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 86317688251) ^ 2250 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_557 : Nat.Prime 557 := by norm_num
private theorem prime_twentyOneS_9719 : Nat.Prime 9719 := by norm_num
private theorem prime_twentyOneS_167 : Nat.Prime 167 := by norm_num
private theorem prime_twentyOneS_331 : Nat.Prime 331 := by norm_num
private theorem prime_twentyOneS_29517919 : Nat.Prime 29517919 := by
  apply lucas_primality 29517919 (3 : ZMod 29517919)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (89, 1), (167, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (89, 1), (167, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod = 29517919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_89
      · exact prime_twentyOneS_167
      · exact prime_twentyOneS_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29517919) ^ 14758959 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 29517919) ^ 9839306 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 29517919) ^ 331662 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 29517919) ^ 176754 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 29517919) ^ 89178 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_14381527743168931 : Nat.Prime 14381527743168931 := by
  apply lucas_primality 14381527743168931 (7 : ZMod 14381527743168931)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (557, 1), (9719, 1), (29517919, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (557, 1), (9719, 1), (29517919, 1)] : List FactorBlock).map factorBlockValue).prod = 14381527743168931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_557
      · exact prime_twentyOneS_9719
      · exact prime_twentyOneS_29517919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14381527743168931) ^ 7190763871584465 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381527743168931) ^ 4793842581056310 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381527743168931) ^ 2876305548633786 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381527743168931) ^ 25819618928490 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381527743168931) ^ 1479733279470 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381527743168931) ^ 487213470 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_103 : Nat.Prime 103 := by norm_num
private theorem prime_twentyOneS_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_twentyOneS_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_twentyOneS_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_twentyOneS_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_twentyOneS_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_35279
      · exact prime_twentyOneS_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_61717
      · exact prime_twentyOneS_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_107
      · exact prime_twentyOneS_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_359 : Nat.Prime 359 := by norm_num
private theorem prime_twentyOneS_173 : Nat.Prime 173 := by norm_num
private theorem prime_twentyOneS_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_twentyOneS_4259 : Nat.Prime 4259 := by norm_num
private theorem prime_twentyOneS_38651421607 : Nat.Prime 38651421607 := by
  apply lucas_primality 38651421607 (3 : ZMod 38651421607)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (173, 1), (1249, 1), (4259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (173, 1), (1249, 1), (4259, 1)] : List FactorBlock).map factorBlockValue).prod = 38651421607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_173
      · exact prime_twentyOneS_1249
      · exact prime_twentyOneS_4259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38651421607) ^ 19325710803 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38651421607) ^ 12883807202 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38651421607) ^ 5521631658 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38651421607) ^ 223418622 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38651421607) ^ 30945894 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38651421607) ^ 9075234 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_131 : Nat.Prime 131 := by norm_num
private theorem prime_twentyOneS_2087 : Nat.Prime 2087 := by norm_num
private theorem prime_twentyOneS_5083141924411 : Nat.Prime 5083141924411 := by
  apply lucas_primality 5083141924411 (2 : ZMod 5083141924411)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (103, 1), (131, 1), (547, 1), (2087, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (103, 1), (131, 1), (547, 1), (2087, 1)] : List FactorBlock).map factorBlockValue).prod = 5083141924411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_103
      · exact prime_twentyOneS_131
      · exact prime_twentyOneS_547
      · exact prime_twentyOneS_2087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5083141924411) ^ 2541570962205 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 1694380641470 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 1016628384882 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 462103811310 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 49350892470 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 38802610110 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 9292764030 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 2435621430 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_81330270790577 : Nat.Prime 81330270790577 := by
  apply lucas_primality 81330270790577 (3 : ZMod 81330270790577)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5083141924411, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5083141924411, 1)] : List FactorBlock).map factorBlockValue).prod = 81330270790577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5083141924411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 81330270790577) ^ 40665135395288 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 81330270790577) ^ 16 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_257 : Nat.Prime 257 := by norm_num
private theorem prime_twentyOneS_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_twentyOneS_213426679 : Nat.Prime 213426679 := by
  apply lucas_primality 213426679 (3 : ZMod 213426679)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61, 1), (257, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61, 1), (257, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod = 213426679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_61
      · exact prime_twentyOneS_257
      · exact prime_twentyOneS_2269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 213426679) ^ 106713339 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 213426679) ^ 71142226 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 213426679) ^ 3498798 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 213426679) ^ 830454 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 213426679) ^ 94062 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_4095737 : Nat.Prime 4095737 := by norm_num
private theorem prime_twentyOneS_712658239 : Nat.Prime 712658239 := by
  apply lucas_primality 712658239 (19 : ZMod 712658239)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29, 1), (4095737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29, 1), (4095737, 1)] : List FactorBlock).map factorBlockValue).prod = 712658239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_4095737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 712658239) ^ 356329119 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (19 : ZMod 712658239) ^ 237552746 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (19 : ZMod 712658239) ^ 24574422 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (19 : ZMod 712658239) ^ 174 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_197 : Nat.Prime 197 := by norm_num
private theorem prime_twentyOneS_11119 : Nat.Prime 11119 := by norm_num
private theorem prime_twentyOneS_7097035321 : Nat.Prime 7097035321 := by
  apply lucas_primality 7097035321 (7 : ZMod 7097035321)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 4), (5, 1), (197, 1), (11119, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 4), (5, 1), (197, 1), (11119, 1)] : List FactorBlock).map factorBlockValue).prod = 7097035321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_197
      · exact prime_twentyOneS_11119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7097035321) ^ 3548517660 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 7097035321) ^ 2365678440 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 7097035321) ^ 1419407064 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 7097035321) ^ 36025560 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 7097035321) ^ 638280 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_193 : Nat.Prime 193 := by norm_num
private theorem prime_twentyOneS_239 : Nat.Prime 239 := by norm_num
private theorem prime_twentyOneS_4519 : Nat.Prime 4519 := by norm_num
private theorem prime_twentyOneS_15661 : Nat.Prime 15661 := by norm_num
private theorem prime_twentyOneS_971 : Nat.Prime 971 := by norm_num
private theorem prime_twentyOneS_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_twentyOneS_22279 : Nat.Prime 22279 := by norm_num
private theorem prime_twentyOneS_13203689273969 : Nat.Prime 13203689273969 := by
  apply lucas_primality 13203689273969 (3 : ZMod 13203689273969)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod = 13203689273969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_971
      · exact prime_twentyOneS_1031
      · exact prime_twentyOneS_22279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13203689273969) ^ 6601844636984 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 356856466864 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 13598032208 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 12806682128 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 592651792 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_5360018256942847067732857 : Nat.Prime 5360018256942847067732857 := by
  apply lucas_primality 5360018256942847067732857 (5 : ZMod 5360018256942847067732857)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod = 5360018256942847067732857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_239
      · exact prime_twentyOneS_4519
      · exact prime_twentyOneS_15661
      · exact prime_twentyOneS_13203689273969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5360018256942847067732857) ^ 2680009128471423533866428 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1786672752314282355910952 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 22426854631560029572104 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1186107160199789127624 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 342252618411522065496 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 405948530424 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_349 : Nat.Prime 349 := by norm_num
private theorem prime_twentyOneS_16850357 : Nat.Prime 16850357 := by norm_num
private theorem prime_twentyOneS_233 : Nat.Prime 233 := by norm_num
private theorem prime_twentyOneS_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_twentyOneS_4561 : Nat.Prime 4561 := by norm_num
private theorem prime_twentyOneS_176317 : Nat.Prime 176317 := by norm_num
private theorem prime_twentyOneS_33774604584521293 : Nat.Prime 33774604584521293 := by
  apply lucas_primality 33774604584521293 (2 : ZMod 33774604584521293)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (233, 1), (1669, 1), (4561, 1), (176317, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (233, 1), (1669, 1), (4561, 1), (176317, 1)] : List FactorBlock).map factorBlockValue).prod = 33774604584521293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_233
      · exact prime_twentyOneS_1669
      · exact prime_twentyOneS_4561
      · exact prime_twentyOneS_176317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33774604584521293) ^ 16887302292260646 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33774604584521293) ^ 11258201528173764 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33774604584521293) ^ 144955384482924 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33774604584521293) ^ 20236431746268 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33774604584521293) ^ 7405087608972 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33774604584521293) ^ 191556143676 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2731 : Nat.Prime 2731 := by norm_num
private theorem prime_twentyOneS_5945839 : Nat.Prime 5945839 := by norm_num
private theorem prime_twentyOneS_142700137 : Nat.Prime 142700137 := by
  apply lucas_primality 142700137 (7 : ZMod 142700137)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5945839, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5945839, 1)] : List FactorBlock).map factorBlockValue).prod = 142700137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5945839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 142700137) ^ 71350068 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 142700137) ^ 47566712 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 142700137) ^ 24 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_563 : Nat.Prime 563 := by norm_num
private theorem prime_twentyOneS_18353 : Nat.Prime 18353 := by norm_num
private theorem prime_twentyOneS_84811121713 : Nat.Prime 84811121713 := by
  apply lucas_primality 84811121713 (5 : ZMod 84811121713)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (19, 1), (563, 1), (18353, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (19, 1), (563, 1), (18353, 1)] : List FactorBlock).map factorBlockValue).prod = 84811121713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_563
      · exact prime_twentyOneS_18353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 84811121713) ^ 42405560856 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 84811121713) ^ 28270373904 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 84811121713) ^ 4463743248 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 84811121713) ^ 150641424 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 84811121713) ^ 4621104 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_919540909857750652508836801 : Nat.Prime 919540909857750652508836801 := by
  apply lucas_primality 919540909857750652508836801 (113 : ZMod 919540909857750652508836801)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 919540909857750652508836801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 919540909857750652508836801) ^ 459770454928875326254418400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 306513636619250217502945600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 183908181971550130501767360 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 131362987122535807501262400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 83594628168886422955348800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 70733916142903896346833600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 54090641756338273676990400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 48396889992513192237307200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 39980039559032637065601600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 31708307236474160431339200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 29662609995411311371252800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 24852457023182450067806400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 22427827069701235427044800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 21384672322273270988577600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 19564700209739375585294400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 17349828487882087783185600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15585439150131366991675200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15074441145209027090308800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_769 : Nat.Prime 769 := by norm_num
private theorem prime_twentyOneS_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_twentyOneS_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_twentyOneS_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_twentyOneS_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_twentyOneS_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_89
      · exact prime_twentyOneS_223
      · exact prime_twentyOneS_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_17788357 : Nat.Prime 17788357 := by norm_num
private theorem prime_twentyOneS_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_twentyOneS_32503 : Nat.Prime 32503 := by norm_num
private theorem prime_twentyOneS_400780711729 : Nat.Prime 400780711729 := by
  apply lucas_primality 400780711729 (7 : ZMod 400780711729)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (17, 1), (23, 1), (73, 1), (32503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (17, 1), (23, 1), (73, 1), (32503, 1)] : List FactorBlock).map factorBlockValue).prod = 400780711729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_73
      · exact prime_twentyOneS_32503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 400780711729) ^ 200390355864 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 400780711729) ^ 133593570576 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 400780711729) ^ 23575335984 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 400780711729) ^ 17425248336 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 400780711729) ^ 5490146736 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 400780711729) ^ 12330576 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_445632882740015849 : Nat.Prime 445632882740015849 := by
  apply lucas_primality 445632882740015849 (3 : ZMod 445632882740015849)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (23, 1), (6043, 1), (400780711729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (23, 1), (6043, 1), (400780711729, 1)] : List FactorBlock).map factorBlockValue).prod = 445632882740015849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_6043
      · exact prime_twentyOneS_400780711729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 445632882740015849) ^ 222816441370007924 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 445632882740015849) ^ 19375342727826776 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 445632882740015849) ^ 73743650958136 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 445632882740015849) ^ 1111912 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_48128351335921711693 : Nat.Prime 48128351335921711693 := by
  apply lucas_primality 48128351335921711693 (2 : ZMod 48128351335921711693)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (445632882740015849, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (445632882740015849, 1)] : List FactorBlock).map factorBlockValue).prod = 48128351335921711693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_445632882740015849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 48128351335921711693) ^ 24064175667960855846 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 48128351335921711693) ^ 16042783778640570564 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 48128351335921711693) ^ 108 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_72973 : Nat.Prime 72973 := by norm_num
private theorem prime_twentyOneS_195271 : Nat.Prime 195271 := by norm_num
private theorem prime_twentyOneS_409 : Nat.Prime 409 := by norm_num
private theorem prime_twentyOneS_1957301 : Nat.Prime 1957301 := by norm_num
private theorem prime_twentyOneS_598744972004371 : Nat.Prime 598744972004371 := by
  apply lucas_primality 598744972004371 (2 : ZMod 598744972004371)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod = 598744972004371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_107
      · exact prime_twentyOneS_233
      · exact prime_twentyOneS_409
      · exact prime_twentyOneS_1957301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 598744972004371) ^ 299372486002185 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 199581657334790 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 119748994400874 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 5595747401910 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 2569720909890 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 1463924136930 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 305903370 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_16217 : Nat.Prime 16217 := by norm_num
private theorem prime_twentyOneS_281 : Nat.Prime 281 := by norm_num
private theorem prime_twentyOneS_9431 : Nat.Prime 9431 := by norm_num
private theorem prime_twentyOneS_80149 : Nat.Prime 80149 := by norm_num
private theorem prime_twentyOneS_3096739 : Nat.Prime 3096739 := by norm_num
private theorem prime_twentyOneS_1593092214812622769463 : Nat.Prime 1593092214812622769463 := by
  apply lucas_primality 1593092214812622769463 (5 : ZMod 1593092214812622769463)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (173, 1), (281, 1), (9431, 1), (80149, 1), (3096739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (173, 1), (281, 1), (9431, 1), (80149, 1), (3096739, 1)] : List FactorBlock).map factorBlockValue).prod = 1593092214812622769463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_173
      · exact prime_twentyOneS_281
      · exact prime_twentyOneS_9431
      · exact prime_twentyOneS_80149
      · exact prime_twentyOneS_3096739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1593092214812622769463) ^ 796546107406311384731 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 227584602116088967066 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 9208625519148108494 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 5669367312500436902 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 168920815906332602 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 19876632457206238 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 514441874117458 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2029 : Nat.Prime 2029 := by norm_num
private theorem prime_twentyOneS_2245339 : Nat.Prime 2245339 := by norm_num
private theorem prime_twentyOneS_439 : Nat.Prime 439 := by norm_num
private theorem prime_twentyOneS_251609 : Nat.Prime 251609 := by norm_num
private theorem prime_twentyOneS_883650809 : Nat.Prime 883650809 := by
  apply lucas_primality 883650809 (3 : ZMod 883650809)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (439, 1), (251609, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (439, 1), (251609, 1)] : List FactorBlock).map factorBlockValue).prod = 883650809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_439
      · exact prime_twentyOneS_251609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 883650809) ^ 441825404 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 883650809) ^ 2012872 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 883650809) ^ 3512 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2398625938490051 : Nat.Prime 2398625938490051 := by
  apply lucas_primality 2398625938490051 (2 : ZMod 2398625938490051)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (233, 2), (883650809, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (233, 2), (883650809, 1)] : List FactorBlock).map factorBlockValue).prod = 2398625938490051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_233
      · exact prime_twentyOneS_883650809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2398625938490051) ^ 1199312969245025 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2398625938490051) ^ 479725187698010 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2398625938490051) ^ 10294531924850 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2398625938490051) ^ 2714450 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_752351653519977806598139201 : Nat.Prime 752351653519977806598139201 := by
  apply lucas_primality 752351653519977806598139201 (22 : ZMod 752351653519977806598139201)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 752351653519977806598139201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 752351653519977806598139201) ^ 376175826759988903299069600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 250783884506659268866046400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 150470330703995561319627840 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 107478807645711115228305600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 57873204116921369738318400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 44255979618822223917537600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 39597455448419884557796800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 32710941457390339417310400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 25943160466206131262004800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 24269408178063800212843200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 20333828473512913691841600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 18350040329755556258491200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 17496550081859948990654400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 16007481989786761842513600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 14195314217358071822606400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12751722941016572993188800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12333633664261931255707200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1879 : Nat.Prime 1879 := by norm_num
private theorem prime_twentyOneS_2243 : Nat.Prime 2243 := by norm_num
private theorem prime_twentyOneS_127 : Nat.Prime 127 := by norm_num
private theorem prime_twentyOneS_190769 : Nat.Prime 190769 := by norm_num
private theorem prime_twentyOneS_58756853 : Nat.Prime 58756853 := by
  apply lucas_primality 58756853 (2 : ZMod 58756853)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (11, 1), (190769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (11, 1), (190769, 1)] : List FactorBlock).map factorBlockValue).prod = 58756853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_190769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58756853) ^ 29378426 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 58756853) ^ 8393836 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 58756853) ^ 5341532 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 58756853) ^ 308 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_3260946584647001 : Nat.Prime 3260946584647001 := by
  apply lucas_primality 3260946584647001 (6 : ZMod 3260946584647001)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 3), (19, 1), (23, 1), (127, 1), (58756853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 3), (19, 1), (23, 1), (127, 1), (58756853, 1)] : List FactorBlock).map factorBlockValue).prod = 3260946584647001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_127
      · exact prime_twentyOneS_58756853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3260946584647001) ^ 1630473292323500 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 3260946584647001) ^ 652189316929400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 3260946584647001) ^ 171628767613000 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 3260946584647001) ^ 141780286289000 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 3260946584647001) ^ 25676744761000 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 3260946584647001) ^ 55499000 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_173260613935464457133 : Nat.Prime 173260613935464457133 := by
  apply lucas_primality 173260613935464457133 (2 : ZMod 173260613935464457133)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (359, 1), (3260946584647001, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (359, 1), (3260946584647001, 1)] : List FactorBlock).map factorBlockValue).prod = 173260613935464457133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_359
      · exact prime_twentyOneS_3260946584647001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 173260613935464457133) ^ 86630306967732228566 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 173260613935464457133) ^ 4682719295553093436 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 173260613935464457133) ^ 482620094527756148 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 173260613935464457133) ^ 53132 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_739 : Nat.Prime 739 := by norm_num
private theorem prime_twentyOneS_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_twentyOneS_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_twentyOneS_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_43591 : Nat.Prime 43591 := by norm_num
private theorem prime_twentyOneS_550990241 : Nat.Prime 550990241 := by
  apply lucas_primality 550990241 (3 : ZMod 550990241)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod = 550990241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_79
      · exact prime_twentyOneS_43591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 550990241) ^ 275495120 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 110198048 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 6974560 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 12640 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_601 : Nat.Prime 601 := by norm_num
private theorem prime_twentyOneS_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_twentyOneS_7978459 : Nat.Prime 7978459 := by norm_num
private theorem prime_twentyOneS_31913837 : Nat.Prime 31913837 := by
  apply lucas_primality 31913837 (2 : ZMod 31913837)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod = 31913837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7978459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31913837) ^ 15956918 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 31913837) ^ 4 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_41007301887107 : Nat.Prime 41007301887107 := by
  apply lucas_primality 41007301887107 (2 : ZMod 41007301887107)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod = 41007301887107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_601
      · exact prime_twentyOneS_1069
      · exact prime_twentyOneS_31913837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41007301887107) ^ 20503650943553 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 68231783506 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 38360432074 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 1284938 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_773 : Nat.Prime 773 := by norm_num
private theorem prime_twentyOneS_8219 : Nat.Prime 8219 := by norm_num
private theorem prime_twentyOneS_33352703 : Nat.Prime 33352703 := by
  apply lucas_primality 33352703 (5 : ZMod 33352703)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2029, 1), (8219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2029, 1), (8219, 1)] : List FactorBlock).map factorBlockValue).prod = 33352703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_2029
      · exact prime_twentyOneS_8219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33352703) ^ 16676351 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 33352703) ^ 16438 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 33352703) ^ 4058 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_81463 : Nat.Prime 81463 := by norm_num
private theorem prime_twentyOneS_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_twentyOneS_31471001 : Nat.Prime 31471001 := by
  apply lucas_primality 31471001 (3 : ZMod 31471001)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 3), (11, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 3), (11, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod = 31471001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_2861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31471001) ^ 15735500 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 31471001) ^ 6294200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 31471001) ^ 2861000 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 31471001) ^ 11000 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_5916548189 : Nat.Prime 5916548189 := by
  apply lucas_primality 5916548189 (2 : ZMod 5916548189)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (47, 1), (31471001, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (47, 1), (31471001, 1)] : List FactorBlock).map factorBlockValue).prod = 5916548189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_31471001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5916548189) ^ 2958274094 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5916548189) ^ 125884004 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5916548189) ^ 188 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_26026907316507379 : Nat.Prime 26026907316507379 := by
  apply lucas_primality 26026907316507379 (2 : ZMod 26026907316507379)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (81463, 1), (5916548189, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (81463, 1), (5916548189, 1)] : List FactorBlock).map factorBlockValue).prod = 26026907316507379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_81463
      · exact prime_twentyOneS_5916548189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26026907316507379) ^ 13013453658253689 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26026907316507379) ^ 8675635772169126 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26026907316507379) ^ 319493602206 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26026907316507379) ^ 4399002 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_331489 : Nat.Prime 331489 := by norm_num
private theorem prime_twentyOneS_419 : Nat.Prime 419 := by norm_num
private theorem prime_twentyOneS_22013 : Nat.Prime 22013 := by norm_num
private theorem prime_twentyOneS_117701 : Nat.Prime 117701 := by norm_num
private theorem prime_twentyOneS_5796774251 : Nat.Prime 5796774251 := by
  apply lucas_primality 5796774251 (2 : ZMod 5796774251)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 3), (197, 1), (117701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 3), (197, 1), (117701, 1)] : List FactorBlock).map factorBlockValue).prod = 5796774251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_197
      · exact prime_twentyOneS_117701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5796774251) ^ 2898387125 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5796774251) ^ 1159354850 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5796774251) ^ 29425250 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5796774251) ^ 49250 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1970979474127129694209 : Nat.Prime 1970979474127129694209 := by
  apply lucas_primality 1970979474127129694209 (17 : ZMod 1970979474127129694209)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 12), (3, 2), (419, 1), (22013, 1), (5796774251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 12), (3, 2), (419, 1), (22013, 1), (5796774251, 1)] : List FactorBlock).map factorBlockValue).prod = 1970979474127129694209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_419
      · exact prime_twentyOneS_22013
      · exact prime_twentyOneS_5796774251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1970979474127129694209) ^ 985489737063564847104 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 1970979474127129694209) ^ 656993158042376564736 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 1970979474127129694209) ^ 4704008291472863232 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 1970979474127129694209) ^ 89537067829334016 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 1970979474127129694209) ^ 340013150208 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_10391 : Nat.Prime 10391 := by norm_num
private theorem prime_twentyOneS_431 : Nat.Prime 431 := by norm_num
private theorem prime_twentyOneS_3532679 : Nat.Prime 3532679 := by norm_num
private theorem prime_twentyOneS_677 : Nat.Prime 677 := by norm_num
private theorem prime_twentyOneS_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_twentyOneS_3139143389 : Nat.Prime 3139143389 := by
  apply lucas_primality 3139143389 (2 : ZMod 3139143389)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod = 3139143389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_359
      · exact prime_twentyOneS_677
      · exact prime_twentyOneS_3229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3139143389) ^ 1569571694 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 8744132 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 4636844 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 972172 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_4712696973609818164547 : Nat.Prime 4712696973609818164547 := by
  apply lucas_primality 4712696973609818164547 (2 : ZMod 4712696973609818164547)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod = 4712696973609818164547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_431
      · exact prime_twentyOneS_3532679
      · exact prime_twentyOneS_3139143389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4712696973609818164547) ^ 2356348486804909082273 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 277217469035871656738 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 162506792193442005674 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 10934331725312803166 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1334029209449774 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1501268463914 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_439171 : Nat.Prime 439171 := by norm_num
private theorem prime_twentyOneS_16411 : Nat.Prime 16411 := by norm_num
private theorem prime_twentyOneS_163 : Nat.Prime 163 := by norm_num
private theorem prime_twentyOneS_28517 : Nat.Prime 28517 := by norm_num
private theorem prime_twentyOneS_54068233 : Nat.Prime 54068233 := by
  apply lucas_primality 54068233 (10 : ZMod 54068233)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (79, 1), (28517, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (79, 1), (28517, 1)] : List FactorBlock).map factorBlockValue).prod = 54068233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_79
      · exact prime_twentyOneS_28517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 54068233) ^ 27034116 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 54068233) ^ 18022744 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 54068233) ^ 684408 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 54068233) ^ 1896 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_18401798692153 : Nat.Prime 18401798692153 := by
  apply lucas_primality 18401798692153 (10 : ZMod 18401798692153)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (29, 1), (163, 1), (54068233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (29, 1), (163, 1), (54068233, 1)] : List FactorBlock).map factorBlockValue).prod = 18401798692153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_163
      · exact prime_twentyOneS_54068233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 18401798692153) ^ 9200899346076 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 18401798692153) ^ 6133932897384 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 18401798692153) ^ 634544782488 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 18401798692153) ^ 112894470504 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 18401798692153) ^ 340344 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2870680595975869 : Nat.Prime 2870680595975869 := by
  apply lucas_primality 2870680595975869 (2 : ZMod 2870680595975869)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (18401798692153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (18401798692153, 1)] : List FactorBlock).map factorBlockValue).prod = 2870680595975869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_18401798692153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2870680595975869) ^ 1435340297987934 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2870680595975869) ^ 956893531991956 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2870680595975869) ^ 220821584305836 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2870680595975869) ^ 156 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1413322177816799584771 : Nat.Prime 1413322177816799584771 := by
  apply lucas_primality 1413322177816799584771 (2 : ZMod 1413322177816799584771)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (16411, 1), (2870680595975869, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (16411, 1), (2870680595975869, 1)] : List FactorBlock).map factorBlockValue).prod = 1413322177816799584771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_16411
      · exact prime_twentyOneS_2870680595975869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1413322177816799584771) ^ 706661088908399792385 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1413322177816799584771) ^ 471107392605599861590 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1413322177816799584771) ^ 282664435563359916954 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1413322177816799584771) ^ 86120417879276070 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1413322177816799584771) ^ 492330 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_683 : Nat.Prime 683 := by norm_num
private theorem prime_twentyOneS_823 : Nat.Prime 823 := by norm_num
private theorem prime_twentyOneS_179 : Nat.Prime 179 := by norm_num
private theorem prime_twentyOneS_191 : Nat.Prime 191 := by norm_num
private theorem prime_twentyOneS_156859133 : Nat.Prime 156859133 := by
  apply lucas_primality 156859133 (2 : ZMod 156859133)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (37, 1), (179, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (37, 1), (179, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod = 156859133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_179
      · exact prime_twentyOneS_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 156859133) ^ 78429566 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 156859133) ^ 5059972 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 156859133) ^ 4239436 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 156859133) ^ 876308 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 156859133) ^ 821252 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_491 : Nat.Prime 491 := by norm_num
private theorem prime_twentyOneS_6287 : Nat.Prime 6287 := by norm_num
private theorem prime_twentyOneS_734686247 : Nat.Prime 734686247 := by
  apply lucas_primality 734686247 (5 : ZMod 734686247)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (17, 1), (491, 1), (6287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (17, 1), (491, 1), (6287, 1)] : List FactorBlock).map factorBlockValue).prod = 734686247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_491
      · exact prime_twentyOneS_6287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 734686247) ^ 367343123 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 734686247) ^ 104955178 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 734686247) ^ 43216838 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 734686247) ^ 1496306 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 734686247) ^ 116858 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_26275232482769198029 : Nat.Prime 26275232482769198029 := by
  apply lucas_primality 26275232482769198029 (2 : ZMod 26275232482769198029)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (156859133, 1), (734686247, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (156859133, 1), (734686247, 1)] : List FactorBlock).map factorBlockValue).prod = 26275232482769198029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_156859133
      · exact prime_twentyOneS_734686247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26275232482769198029) ^ 13137616241384599014 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26275232482769198029) ^ 8758410827589732676 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26275232482769198029) ^ 1382906972777326212 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26275232482769198029) ^ 167508464316 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26275232482769198029) ^ 35763882324 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_113 : Nat.Prime 113 := by norm_num
private theorem prime_twentyOneS_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_twentyOneS_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_113
      · exact prime_twentyOneS_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_397 : Nat.Prime 397 := by norm_num
private theorem prime_twentyOneS_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_twentyOneS_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_twentyOneS_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_397
      · exact prime_twentyOneS_2531
      · exact prime_twentyOneS_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_14014339 : Nat.Prime 14014339 := by norm_num
private theorem prime_twentyOneS_1849892749 : Nat.Prime 1849892749 := by
  apply lucas_primality 1849892749 (2 : ZMod 1849892749)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (14014339, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (14014339, 1)] : List FactorBlock).map factorBlockValue).prod = 1849892749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_14014339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1849892749) ^ 924946374 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1849892749) ^ 616630916 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1849892749) ^ 168172068 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1849892749) ^ 132 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_12588833 : Nat.Prime 12588833 := by norm_num
private theorem prime_twentyOneS_139753 : Nat.Prime 139753 := by norm_num
private theorem prime_twentyOneS_187828033 : Nat.Prime 187828033 := by
  apply lucas_primality 187828033 (11 : ZMod 187828033)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (7, 1), (139753, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (7, 1), (139753, 1)] : List FactorBlock).map factorBlockValue).prod = 187828033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_139753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 187828033) ^ 93914016 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 187828033) ^ 62609344 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 187828033) ^ 26832576 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 187828033) ^ 1344 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_312118717700524549 : Nat.Prime 312118717700524549 := by
  apply lucas_primality 312118717700524549 (6 : ZMod 312118717700524549)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (12588833, 1), (187828033, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (12588833, 1), (187828033, 1)] : List FactorBlock).map factorBlockValue).prod = 312118717700524549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_12588833
      · exact prime_twentyOneS_187828033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 312118717700524549) ^ 156059358850262274 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 312118717700524549) ^ 104039572566841516 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 312118717700524549) ^ 28374428881865868 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 312118717700524549) ^ 24793300356 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 312118717700524549) ^ 1661725956 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_3463 : Nat.Prime 3463 := by norm_num
private theorem prime_twentyOneS_4261 : Nat.Prime 4261 := by norm_num
private theorem prime_twentyOneS_25717 : Nat.Prime 25717 := by norm_num
private theorem prime_twentyOneS_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_twentyOneS_191467 : Nat.Prime 191467 := by norm_num
private theorem prime_twentyOneS_27571249 : Nat.Prime 27571249 := by
  apply lucas_primality 27571249 (7 : ZMod 27571249)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (191467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (191467, 1)] : List FactorBlock).map factorBlockValue).prod = 27571249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_191467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 27571249) ^ 13785624 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 27571249) ^ 9190416 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 27571249) ^ 144 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1770184470797 : Nat.Prime 1770184470797 := by
  apply lucas_primality 1770184470797 (2 : ZMod 1770184470797)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (2293, 1), (27571249, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (2293, 1), (27571249, 1)] : List FactorBlock).map factorBlockValue).prod = 1770184470797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_2293
      · exact prime_twentyOneS_27571249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1770184470797) ^ 885092235398 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1770184470797) ^ 252883495828 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1770184470797) ^ 771994972 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1770184470797) ^ 64204 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_6373336764968102861 : Nat.Prime 6373336764968102861 := by
  apply lucas_primality 6373336764968102861 (2 : ZMod 6373336764968102861)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (25717, 1), (1770184470797, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (25717, 1), (1770184470797, 1)] : List FactorBlock).map factorBlockValue).prod = 6373336764968102861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_25717
      · exact prime_twentyOneS_1770184470797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6373336764968102861) ^ 3186668382484051430 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6373336764968102861) ^ 1274667352993620572 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6373336764968102861) ^ 910476680709728980 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6373336764968102861) ^ 247825825911580 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6373336764968102861) ^ 3600380 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_162940727733174517744327 : Nat.Prime 162940727733174517744327 := by
  apply lucas_primality 162940727733174517744327 (5 : ZMod 162940727733174517744327)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (4261, 1), (6373336764968102861, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (4261, 1), (6373336764968102861, 1)] : List FactorBlock).map factorBlockValue).prod = 162940727733174517744327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_4261
      · exact prime_twentyOneS_6373336764968102861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 162940727733174517744327) ^ 81470363866587258872163 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 162940727733174517744327) ^ 54313575911058172581442 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 162940727733174517744327) ^ 38240020589808617166 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 162940727733174517744327) ^ 25566 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_twentyOneS_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_twentyOneS_24913302187 : Nat.Prime 24913302187 := by
  apply lucas_primality 24913302187 (2 : ZMod 24913302187)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod = 24913302187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_487
      · exact prime_twentyOneS_2621
      · exact prime_twentyOneS_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24913302187) ^ 12456651093 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 8304434062 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 51156678 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 9505266 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 7658562 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_613 : Nat.Prime 613 := by norm_num
private theorem prime_twentyOneS_1590164911 : Nat.Prime 1590164911 := by
  apply lucas_primality 1590164911 (3 : ZMod 1590164911)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod = 1590164911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1590164911) ^ 795082455 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 530054970 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 318032982 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 83692890 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 42977430 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 38784510 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 2594070 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_254426385761 : Nat.Prime 254426385761 := by
  apply lucas_primality 254426385761 (3 : ZMod 254426385761)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod = 254426385761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_1590164911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 254426385761) ^ 127213192880 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 50885277152 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 160 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_22145781469408963 : Nat.Prime 22145781469408963 := by
  apply lucas_primality 22145781469408963 (2 : ZMod 22145781469408963)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod = 22145781469408963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_89
      · exact prime_twentyOneS_163
      · exact prime_twentyOneS_254426385761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22145781469408963) ^ 11072890734704481 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 7381927156469654 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 248829005274258 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 135863689996374 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 87042 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_539730534046940600385621601 : Nat.Prime 539730534046940600385621601 := by
  apply lucas_primality 539730534046940600385621601 (46 : ZMod 539730534046940600385621601)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 539730534046940600385621601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (46 : ZMod 539730534046940600385621601) ^ 269865267023470300192810800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 179910178015646866795207200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 107946106809388120077124320 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 77104362006705800055088800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 49066412186085509125965600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 41517733388226200029663200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 31748854943937682375624800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 28406870212996873704506400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 18611397725756572427090400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 17410662388610987109213600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 14587311730998394605016800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 13164159366998551228917600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 12551872884812572101991200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 11483628383977459582672800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 10183594982017747177087200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 9147975153337976277722400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 8848041541753124596485600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_181 : Nat.Prime 181 := by norm_num
private theorem prime_twentyOneS_7601051 : Nat.Prime 7601051 := by norm_num
private theorem prime_twentyOneS_18431951 : Nat.Prime 18431951 := by norm_num
private theorem prime_twentyOneS_2584511 : Nat.Prime 2584511 := by norm_num
private theorem prime_twentyOneS_67197287 : Nat.Prime 67197287 := by
  apply lucas_primality 67197287 (5 : ZMod 67197287)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (2584511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (2584511, 1)] : List FactorBlock).map factorBlockValue).prod = 67197287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_2584511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 67197287) ^ 33598643 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 67197287) ^ 5169022 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 67197287) ^ 26 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_383958901408250471 : Nat.Prime 383958901408250471 := by
  apply lucas_primality 383958901408250471 (7 : ZMod 383958901408250471)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (31, 1), (18431951, 1), (67197287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (31, 1), (18431951, 1), (67197287, 1)] : List FactorBlock).map factorBlockValue).prod = 383958901408250471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_18431951
      · exact prime_twentyOneS_67197287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 383958901408250471) ^ 191979450704125235 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 383958901408250471) ^ 76791780281650094 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 383958901408250471) ^ 12385771013169370 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 383958901408250471) ^ 20831158970 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 383958901408250471) ^ 5713904810 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_6229 : Nat.Prime 6229 := by norm_num
private theorem prime_twentyOneS_6470753 : Nat.Prime 6470753 := by norm_num
private theorem prime_twentyOneS_8696692033 : Nat.Prime 8696692033 := by
  apply lucas_primality 8696692033 (17 : ZMod 8696692033)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod = 8696692033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_6470753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 8696692033) ^ 4348346016 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 2898897344 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1242384576 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1344 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_6389 : Nat.Prime 6389 := by norm_num
private theorem prime_twentyOneS_45885799 : Nat.Prime 45885799 := by
  apply lucas_primality 45885799 (7 : ZMod 45885799)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod = 45885799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_6389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 45885799) ^ 22942899 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 15295266 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 6555114 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 2415042 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 7182 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_120863194567 : Nat.Prime 120863194567 := by
  apply lucas_primality 120863194567 (3 : ZMod 120863194567)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod = 120863194567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_439
      · exact prime_twentyOneS_45885799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 120863194567) ^ 60431597283 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 40287731522 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 275314794 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 2634 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_727 : Nat.Prime 727 := by norm_num
private theorem prime_twentyOneS_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_twentyOneS_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_twentyOneS_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_twentyOneS_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_173
      · exact prime_twentyOneS_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_4159
      · exact prime_twentyOneS_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_12853 : Nat.Prime 12853 := by norm_num
private theorem prime_twentyOneS_37663 : Nat.Prime 37663 := by norm_num
private theorem prime_twentyOneS_318281 : Nat.Prime 318281 := by norm_num
private theorem prime_twentyOneS_389 : Nat.Prime 389 := by norm_num
private theorem prime_twentyOneS_449 : Nat.Prime 449 := by norm_num
private theorem prime_twentyOneS_160338799 : Nat.Prime 160338799 := by
  apply lucas_primality 160338799 (3 : ZMod 160338799)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (17, 1), (389, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (17, 1), (389, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod = 160338799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_389
      · exact prime_twentyOneS_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 160338799) ^ 80169399 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 160338799) ^ 53446266 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 160338799) ^ 9431694 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 160338799) ^ 412182 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 160338799) ^ 357102 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_170959857503138651 : Nat.Prime 170959857503138651 := by
  apply lucas_primality 170959857503138651 (10 : ZMod 170959857503138651)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (67, 1), (318281, 1), (160338799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (67, 1), (318281, 1), (160338799, 1)] : List FactorBlock).map factorBlockValue).prod = 170959857503138651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_67
      · exact prime_twentyOneS_318281
      · exact prime_twentyOneS_160338799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 170959857503138651) ^ 85479928751569325 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 170959857503138651) ^ 34191971500627730 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 170959857503138651) ^ 2551639664225950 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 170959857503138651) ^ 537134976650 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (10 : ZMod 170959857503138651) ^ 1066241350 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1025759145018831907 : Nat.Prime 1025759145018831907 := by
  apply lucas_primality 1025759145018831907 (2 : ZMod 1025759145018831907)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (170959857503138651, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (170959857503138651, 1)] : List FactorBlock).map factorBlockValue).prod = 1025759145018831907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_170959857503138651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1025759145018831907) ^ 512879572509415953 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1025759145018831907) ^ 341919715006277302 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1025759145018831907) ^ 6 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1346333 : Nat.Prime 1346333 := by norm_num
private theorem prime_twentyOneS_316097 : Nat.Prime 316097 := by norm_num
private theorem prime_twentyOneS_1489003 : Nat.Prime 1489003 := by norm_num
private theorem prime_twentyOneS_97937826197793863 : Nat.Prime 97937826197793863 := by
  apply lucas_primality 97937826197793863 (5 : ZMod 97937826197793863)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (89, 1), (167, 1), (316097, 1), (1489003, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (89, 1), (167, 1), (316097, 1), (1489003, 1)] : List FactorBlock).map factorBlockValue).prod = 97937826197793863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_89
      · exact prime_twentyOneS_167
      · exact prime_twentyOneS_316097
      · exact prime_twentyOneS_1489003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97937826197793863) ^ 48968913098896931 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 13991118028256266 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 1100425013458358 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 586454049088586 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 309834722246 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 65774095954 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_361586454322254942197 : Nat.Prime 361586454322254942197 := by
  apply lucas_primality 361586454322254942197 (2 : ZMod 361586454322254942197)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (71, 1), (97937826197793863, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (71, 1), (97937826197793863, 1)] : List FactorBlock).map factorBlockValue).prod = 361586454322254942197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_71
      · exact prime_twentyOneS_97937826197793863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 361586454322254942197) ^ 180793227161127471098 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 27814342640173457092 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 5092766962285280876 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 3692 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_227 : Nat.Prime 227 := by norm_num
private theorem prime_twentyOneS_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_twentyOneS_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_twentyOneS_106217 : Nat.Prime 106217 := by norm_num
private theorem prime_twentyOneS_2473421 : Nat.Prime 2473421 := by norm_num
private theorem prime_twentyOneS_18613462787595076228651 : Nat.Prime 18613462787595076228651 := by
  apply lucas_primality 18613462787595076228651 (2 : ZMod 18613462787595076228651)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 2), (19, 1), (1453, 1), (1901, 1), (106217, 1), (2473421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 2), (19, 1), (1453, 1), (1901, 1), (106217, 1), (2473421, 1)] : List FactorBlock).map factorBlockValue).prod = 18613462787595076228651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_1453
      · exact prime_twentyOneS_1901
      · exact prime_twentyOneS_106217
      · exact prime_twentyOneS_2473421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18613462787595076228651) ^ 9306731393797538114325 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18613462787595076228651) ^ 6204487595865025409550 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18613462787595076228651) ^ 3722692557519015245730 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18613462787595076228651) ^ 979655936189214538350 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18613462787595076228651) ^ 12810366681070252050 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18613462787595076228651) ^ 9791405990318293650 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18613462787595076228651) ^ 175239959588343450 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18613462787595076228651) ^ 7525392073405650 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_20807 : Nat.Prime 20807 := by norm_num
private theorem prime_twentyOneS_1273541 : Nat.Prime 1273541 := by norm_num
private theorem prime_twentyOneS_739003 : Nat.Prime 739003 := by norm_num
private theorem prime_twentyOneS_1603636511 : Nat.Prime 1603636511 := by
  apply lucas_primality 1603636511 (7 : ZMod 1603636511)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (31, 1), (739003, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (31, 1), (739003, 1)] : List FactorBlock).map factorBlockValue).prod = 1603636511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_739003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1603636511) ^ 801818255 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603636511) ^ 320727302 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603636511) ^ 229090930 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603636511) ^ 51730210 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603636511) ^ 2170 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_943541142785218363 : Nat.Prime 943541142785218363 := by
  apply lucas_primality 943541142785218363 (2 : ZMod 943541142785218363)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 1), (1273541, 1), (1603636511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 1), (1273541, 1), (1603636511, 1)] : List FactorBlock).map factorBlockValue).prod = 943541142785218363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_1273541
      · exact prime_twentyOneS_1603636511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 943541142785218363) ^ 471770571392609181 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 943541142785218363) ^ 314513714261739454 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 943541142785218363) ^ 134791591826459766 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 943541142785218363) ^ 85776467525928942 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 943541142785218363) ^ 740880068082 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 943541142785218363) ^ 588375942 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_521 : Nat.Prime 521 := by norm_num
private theorem prime_twentyOneS_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_twentyOneS_2633923 : Nat.Prime 2633923 := by norm_num
private theorem prime_twentyOneS_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_twentyOneS_431891 : Nat.Prime 431891 := by norm_num
private theorem prime_twentyOneS_20319607769 : Nat.Prime 20319607769 := by
  apply lucas_primality 20319607769 (3 : ZMod 20319607769)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5881, 1), (431891, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5881, 1), (431891, 1)] : List FactorBlock).map factorBlockValue).prod = 20319607769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5881
      · exact prime_twentyOneS_431891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20319607769) ^ 10159803884 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 20319607769) ^ 3455128 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 20319607769) ^ 47048 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_607348163015529886877 : Nat.Prime 607348163015529886877 := by
  apply lucas_primality 607348163015529886877 (2 : ZMod 607348163015529886877)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (2837, 1), (2633923, 1), (20319607769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (2837, 1), (2633923, 1), (20319607769, 1)] : List FactorBlock).map factorBlockValue).prod = 607348163015529886877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_2837
      · exact prime_twentyOneS_2633923
      · exact prime_twentyOneS_20319607769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 607348163015529886877) ^ 303674081507764943438 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 214081129014991148 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 230586908962612 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 29889758204 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_3571 : Nat.Prime 3571 := by norm_num
private theorem prime_twentyOneS_41399 : Nat.Prime 41399 := by norm_num
private theorem prime_twentyOneS_4420502423 : Nat.Prime 4420502423 := by
  apply lucas_primality 4420502423 (5 : ZMod 4420502423)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (29, 1), (263, 1), (41399, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (29, 1), (263, 1), (41399, 1)] : List FactorBlock).map factorBlockValue).prod = 4420502423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_263
      · exact prime_twentyOneS_41399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4420502423) ^ 2210251211 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 4420502423) ^ 631500346 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 4420502423) ^ 152431118 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 4420502423) ^ 16807994 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 4420502423) ^ 106778 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1288981 : Nat.Prime 1288981 := by norm_num
private theorem prime_twentyOneS_145899759391 : Nat.Prime 145899759391 := by
  apply lucas_primality 145899759391 (3 : ZMod 145899759391)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 3), (11, 1), (1288981, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 3), (11, 1), (1288981, 1)] : List FactorBlock).map factorBlockValue).prod = 145899759391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_1288981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 145899759391) ^ 72949879695 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 145899759391) ^ 48633253130 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 145899759391) ^ 29179951878 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 145899759391) ^ 20842822770 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 145899759391) ^ 13263614490 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 145899759391) ^ 113190 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_28596352840637 : Nat.Prime 28596352840637 := by
  apply lucas_primality 28596352840637 (5 : ZMod 28596352840637)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 2), (145899759391, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 2), (145899759391, 1)] : List FactorBlock).map factorBlockValue).prod = 28596352840637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_145899759391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28596352840637) ^ 14298176420318 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 28596352840637) ^ 4085193262948 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 28596352840637) ^ 196 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_373 : Nat.Prime 373 := by norm_num
private theorem prime_twentyOneS_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_twentyOneS_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_twentyOneS_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_twentyOneS_17678041 : Nat.Prime 17678041 := by norm_num
private theorem prime_twentyOneS_176780411 : Nat.Prime 176780411 := by
  apply lucas_primality 176780411 (2 : ZMod 176780411)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod = 176780411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176780411) ^ 88390205 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 35356082 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 176780411) ^ 10 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_343559 : Nat.Prime 343559 := by norm_num
private theorem prime_twentyOneS_381350491 : Nat.Prime 381350491 := by
  apply lucas_primality 381350491 (2 : ZMod 381350491)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (37, 1), (343559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (37, 1), (343559, 1)] : List FactorBlock).map factorBlockValue).prod = 381350491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_343559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 381350491) ^ 190675245 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 127116830 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 76270098 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 10306770 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 1110 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_3813504911 : Nat.Prime 3813504911 := by
  apply lucas_primality 3813504911 (17 : ZMod 3813504911)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (381350491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (381350491, 1)] : List FactorBlock).map factorBlockValue).prod = 3813504911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_381350491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 3813504911) ^ 1906752455 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 3813504911) ^ 762700982 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 3813504911) ^ 10 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2677 : Nat.Prime 2677 := by norm_num
private theorem prime_twentyOneS_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_twentyOneS_576509 : Nat.Prime 576509 := by norm_num
private theorem prime_twentyOneS_114218290024018991 : Nat.Prime 114218290024018991 := by
  apply lucas_primality 114218290024018991 (17 : ZMod 114218290024018991)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (491, 1), (2677, 1), (15073, 1), (576509, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (491, 1), (2677, 1), (15073, 1), (576509, 1)] : List FactorBlock).map factorBlockValue).prod = 114218290024018991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_491
      · exact prime_twentyOneS_2677
      · exact prime_twentyOneS_15073
      · exact prime_twentyOneS_576509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 114218290024018991) ^ 57109145012009495 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 22843658004803798 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 232623808602890 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 42666525970870 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 7577674651630 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 198120567110 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1811 : Nat.Prime 1811 := by norm_num
private theorem prime_twentyOneS_18539 : Nat.Prime 18539 := by norm_num
private theorem prime_twentyOneS_604334323 : Nat.Prime 604334323 := by
  apply lucas_primality 604334323 (2 : ZMod 604334323)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (1811, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (1811, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod = 604334323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_1811
      · exact prime_twentyOneS_18539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 604334323) ^ 302167161 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 604334323) ^ 201444774 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 604334323) ^ 333702 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 604334323) ^ 32598 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2037209 : Nat.Prime 2037209 := by norm_num
private theorem prime_twentyOneS_4013 : Nat.Prime 4013 := by norm_num
private theorem prime_twentyOneS_19316190253 : Nat.Prime 19316190253 := by
  apply lucas_primality 19316190253 (2 : ZMod 19316190253)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (37, 2), (293, 1), (4013, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (37, 2), (293, 1), (4013, 1)] : List FactorBlock).map factorBlockValue).prod = 19316190253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_293
      · exact prime_twentyOneS_4013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19316190253) ^ 9658095126 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 19316190253) ^ 6438730084 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 19316190253) ^ 522059196 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 19316190253) ^ 65925564 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 19316190253) ^ 4813404 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_708320099324229787 : Nat.Prime 708320099324229787 := by
  apply lucas_primality 708320099324229787 (2 : ZMod 708320099324229787)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (2037209, 1), (19316190253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (2037209, 1), (19316190253, 1)] : List FactorBlock).map factorBlockValue).prod = 708320099324229787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_2037209
      · exact prime_twentyOneS_19316190253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 708320099324229787) ^ 354160049662114893 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 708320099324229787) ^ 236106699774743262 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 708320099324229787) ^ 347691424554 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 708320099324229787) ^ 36669762 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_28493 : Nat.Prime 28493 := by norm_num
private theorem prime_twentyOneS_1182917 : Nat.Prime 1182917 := by norm_num
private theorem prime_twentyOneS_224729 : Nat.Prime 224729 := by norm_num
private theorem prime_twentyOneS_20675069 : Nat.Prime 20675069 := by
  apply lucas_primality 20675069 (2 : ZMod 20675069)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (23, 1), (224729, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (23, 1), (224729, 1)] : List FactorBlock).map factorBlockValue).prod = 20675069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_224729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20675069) ^ 10337534 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 20675069) ^ 898916 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 20675069) ^ 92 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1410911 : Nat.Prime 1410911 := by norm_num
private theorem prime_twentyOneS_603869909 : Nat.Prime 603869909 := by
  apply lucas_primality 603869909 (2 : ZMod 603869909)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (107, 1), (1410911, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (107, 1), (1410911, 1)] : List FactorBlock).map factorBlockValue).prod = 603869909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_107
      · exact prime_twentyOneS_1410911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 603869909) ^ 301934954 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 603869909) ^ 5643644 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 603869909) ^ 428 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_619 : Nat.Prime 619 := by norm_num
private theorem prime_twentyOneS_4919 : Nat.Prime 4919 := by norm_num
private theorem prime_twentyOneS_19801 : Nat.Prime 19801 := by norm_num
private theorem prime_twentyOneS_70908014633 : Nat.Prime 70908014633 := by
  apply lucas_primality 70908014633 (3 : ZMod 70908014633)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (13, 1), (4919, 1), (19801, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (13, 1), (4919, 1), (19801, 1)] : List FactorBlock).map factorBlockValue).prod = 70908014633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_4919
      · exact prime_twentyOneS_19801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 70908014633) ^ 35454007316 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 10129716376 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 5454462664 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 14415128 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 3581032 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_3600853 : Nat.Prime 3600853 := by norm_num
private theorem prime_twentyOneS_277280084413 : Nat.Prime 277280084413 := by
  apply lucas_primality 277280084413 (5 : ZMod 277280084413)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (23, 1), (31, 1), (3600853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (23, 1), (31, 1), (3600853, 1)] : List FactorBlock).map factorBlockValue).prod = 277280084413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_3600853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 277280084413) ^ 138640042206 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 92426694804 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 12055655844 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 8944518852 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 77004 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_9427522870043 : Nat.Prime 9427522870043 := by
  apply lucas_primality 9427522870043 (2 : ZMod 9427522870043)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (277280084413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (277280084413, 1)] : List FactorBlock).map factorBlockValue).prod = 9427522870043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_277280084413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9427522870043) ^ 4713761435021 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9427522870043) ^ 554560168826 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9427522870043) ^ 34 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_59123 : Nat.Prime 59123 := by norm_num
private theorem prime_twentyOneS_718657 : Nat.Prime 718657 := by norm_num
private theorem prime_twentyOneS_26321 : Nat.Prime 26321 := by norm_num
private theorem prime_twentyOneS_142972351132073 : Nat.Prime 142972351132073 := by
  apply lucas_primality 142972351132073 (5 : ZMod 142972351132073)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 2), (11, 1), (61, 1), (107, 1), (193, 1), (26321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 2), (11, 1), (61, 1), (107, 1), (193, 1), (26321, 1)] : List FactorBlock).map factorBlockValue).prod = 142972351132073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_61
      · exact prime_twentyOneS_107
      · exact prime_twentyOneS_193
      · exact prime_twentyOneS_26321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 142972351132073) ^ 71486175566036 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 142972351132073) ^ 20424621590296 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 142972351132073) ^ 12997486466552 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 142972351132073) ^ 2343809034952 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 142972351132073) ^ 1336190197496 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 142972351132073) ^ 740789384104 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 142972351132073) ^ 5431873832 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_400445234938052703511912801 : Nat.Prime 400445234938052703511912801 := by
  apply lucas_primality 400445234938052703511912801 (73 : ZMod 400445234938052703511912801)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 400445234938052703511912801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 400445234938052703511912801) ^ 200222617469026351755956400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 133481744979350901170637600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 80089046987610540702382560 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 57206462134007529073130400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 36404112267095700319264800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 30803479610619438731685600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 23555602055179570794818400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 21076064996739615974311200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 17410662388610987109213600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 13808456377174231155583200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 10822844187514937932754400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 9766956949708602524680800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 9312679882280295430509600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 8520111381660695819402400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 7555570470529296292677600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 6787207371831401754439200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (73 : ZMod 400445234938052703511912801) ^ 6564675982591027926424800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_229 : Nat.Prime 229 := by norm_num
private theorem prime_twentyOneS_2851 : Nat.Prime 2851 := by norm_num
private theorem prime_twentyOneS_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_twentyOneS_27689743 : Nat.Prime 27689743 := by
  apply lucas_primality 27689743 (6 : ZMod 27689743)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (181, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (181, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod = 27689743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_181
      · exact prime_twentyOneS_2833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 27689743) ^ 13844871 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 27689743) ^ 9229914 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 27689743) ^ 152982 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 27689743) ^ 9774 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_4153 : Nat.Prime 4153 := by norm_num
private theorem prime_twentyOneS_6907799 : Nat.Prime 6907799 := by norm_num
private theorem prime_twentyOneS_10729345378379 : Nat.Prime 10729345378379 := by
  apply lucas_primality 10729345378379 (2 : ZMod 10729345378379)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (4153, 1), (6907799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (4153, 1), (6907799, 1)] : List FactorBlock).map factorBlockValue).prod = 10729345378379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_4153
      · exact prime_twentyOneS_6907799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10729345378379) ^ 5364672689189 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10729345378379) ^ 975395034398 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10729345378379) ^ 631137963434 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10729345378379) ^ 2583516826 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10729345378379) ^ 1553222 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_twentyOneS_64109047 : Nat.Prime 64109047 := by
  apply lucas_primality 64109047 (6 : ZMod 64109047)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (59, 1), (97, 1), (1867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (59, 1), (97, 1), (1867, 1)] : List FactorBlock).map factorBlockValue).prod = 64109047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_97
      · exact prime_twentyOneS_1867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 64109047) ^ 32054523 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 64109047) ^ 21369682 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 64109047) ^ 1086594 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 64109047) ^ 660918 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 64109047) ^ 34338 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1923271411 : Nat.Prime 1923271411 := by
  apply lucas_primality 1923271411 (2 : ZMod 1923271411)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (64109047, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (64109047, 1)] : List FactorBlock).map factorBlockValue).prod = 1923271411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_64109047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1923271411) ^ 961635705 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1923271411) ^ 641090470 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1923271411) ^ 384654282 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1923271411) ^ 30 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_twentyOneS_479 : Nat.Prime 479 := by norm_num
private theorem prime_twentyOneS_3191 : Nat.Prime 3191 := by norm_num
private theorem prime_twentyOneS_924842839231 : Nat.Prime 924842839231 := by
  apply lucas_primality 924842839231 (6 : ZMod 924842839231)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 6), (5, 1), (83, 1), (479, 1), (3191, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 6), (5, 1), (83, 1), (479, 1), (3191, 1)] : List FactorBlock).map factorBlockValue).prod = 924842839231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_83
      · exact prime_twentyOneS_479
      · exact prime_twentyOneS_3191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 924842839231) ^ 462421419615 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 924842839231) ^ 308280946410 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 924842839231) ^ 184968567846 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 924842839231) ^ 11142684810 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 924842839231) ^ 1930778370 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 924842839231) ^ 289828530 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_5549057035387 : Nat.Prime 5549057035387 := by
  apply lucas_primality 5549057035387 (3 : ZMod 5549057035387)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (924842839231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (924842839231, 1)] : List FactorBlock).map factorBlockValue).prod = 5549057035387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_924842839231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5549057035387) ^ 2774528517693 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 5549057035387) ^ 1849685678462 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 5549057035387) ^ 6 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_198600751296500731 : Nat.Prime 198600751296500731 := by
  apply lucas_primality 198600751296500731 (2 : ZMod 198600751296500731)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (1193, 1), (5549057035387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (1193, 1), (5549057035387, 1)] : List FactorBlock).map factorBlockValue).prod = 198600751296500731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_1193
      · exact prime_twentyOneS_5549057035387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 198600751296500731) ^ 99300375648250365 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 198600751296500731) ^ 66200250432166910 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 198600751296500731) ^ 39720150259300146 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 198600751296500731) ^ 166471711061610 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 198600751296500731) ^ 35790 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_376175826759988903299069601 : Nat.Prime 376175826759988903299069601 := by
  apply lucas_primality 376175826759988903299069601 (33 : ZMod 376175826759988903299069601)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 376175826759988903299069601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 376175826759988903299069601) ^ 188087913379994451649534800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 125391942253329634433023200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 75235165351997780659813920 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 53739403822855557614152800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 28936602058460684869159200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 22127989809411111958768800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 19798727724209942278898400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 16355470728695169708655200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 12971580233103065631002400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 12134704089031900106421600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 10166914236756456845920800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 9175020164877778129245600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 8748275040929974495327200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 8003740994893380921256800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 7097657108679035911303200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 6375861470508286496594400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 6166816832130965627853600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_151 : Nat.Prime 151 := by norm_num
private theorem prime_twentyOneS_4824031 : Nat.Prime 4824031 := by norm_num
private theorem prime_twentyOneS_33677401 : Nat.Prime 33677401 := by
  apply lucas_primality 33677401 (11 : ZMod 33677401)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (37, 2), (41, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (37, 2), (41, 1)] : List FactorBlock).map factorBlockValue).prod = 33677401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 33677401) ^ 16838700 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 33677401) ^ 11225800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 33677401) ^ 6735480 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 33677401) ^ 910200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 33677401) ^ 821400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_196577599972351511 : Nat.Prime 196577599972351511 := by
  apply lucas_primality 196577599972351511 (7 : ZMod 196577599972351511)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 2), (4824031, 1), (33677401, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 2), (4824031, 1), (33677401, 1)] : List FactorBlock).map factorBlockValue).prod = 196577599972351511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_4824031
      · exact prime_twentyOneS_33677401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 196577599972351511) ^ 98288799986175755 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 196577599972351511) ^ 39315519994470302 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 196577599972351511) ^ 17870690906577410 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 196577599972351511) ^ 40749655210 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 196577599972351511) ^ 5837077510 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1957395503481493820383049 : Nat.Prime 1957395503481493820383049 := by
  apply lucas_primality 1957395503481493820383049 (3 : ZMod 1957395503481493820383049)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (19, 1), (109, 1), (601, 1), (196577599972351511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (19, 1), (109, 1), (601, 1), (196577599972351511, 1)] : List FactorBlock).map factorBlockValue).prod = 1957395503481493820383049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_109
      · exact prime_twentyOneS_601
      · exact prime_twentyOneS_196577599972351511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1957395503481493820383049) ^ 978697751740746910191524 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957395503481493820383049) ^ 103020815972710201072792 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957395503481493820383049) ^ 17957756912674255232872 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957395503481493820383049) ^ 3256897676341919834248 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957395503481493820383049) ^ 9957368 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_164421222292445480912176117 : Nat.Prime 164421222292445480912176117 := by
  apply lucas_primality 164421222292445480912176117 (2 : ZMod 164421222292445480912176117)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (1957395503481493820383049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (1957395503481493820383049, 1)] : List FactorBlock).map factorBlockValue).prod = 164421222292445480912176117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_1957395503481493820383049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 164421222292445480912176117) ^ 82210611146222740456088058 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 164421222292445480912176117) ^ 54807074097481826970725372 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 164421222292445480912176117) ^ 23488746041777925844596588 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 164421222292445480912176117) ^ 84 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_587 : Nat.Prime 587 := by norm_num
private theorem prime_twentyOneS_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_twentyOneS_1182739 : Nat.Prime 1182739 := by norm_num
private theorem prime_twentyOneS_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_twentyOneS_4931 : Nat.Prime 4931 := by norm_num
private theorem prime_twentyOneS_23561 : Nat.Prime 23561 := by norm_num
private theorem prime_twentyOneS_697075747 : Nat.Prime 697075747 := by
  apply lucas_primality 697075747 (2 : ZMod 697075747)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (4931, 1), (23561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (4931, 1), (23561, 1)] : List FactorBlock).map factorBlockValue).prod = 697075747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_4931
      · exact prime_twentyOneS_23561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 697075747) ^ 348537873 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 697075747) ^ 232358582 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 697075747) ^ 141366 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 697075747) ^ 29586 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_84576200383511 : Nat.Prime 84576200383511 := by
  apply lucas_primality 84576200383511 (7 : ZMod 84576200383511)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (1103, 1), (697075747, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (1103, 1), (697075747, 1)] : List FactorBlock).map factorBlockValue).prod = 84576200383511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_1103
      · exact prime_twentyOneS_697075747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 84576200383511) ^ 42288100191755 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 84576200383511) ^ 16915240076702 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 84576200383511) ^ 7688745489410 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 84576200383511) ^ 76678332170 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 84576200383511) ^ 121330 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_621996306397416264599123 : Nat.Prime 621996306397416264599123 := by
  apply lucas_primality 621996306397416264599123 (2 : ZMod 621996306397416264599123)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3109, 1), (1182739, 1), (84576200383511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3109, 1), (1182739, 1), (84576200383511, 1)] : List FactorBlock).map factorBlockValue).prod = 621996306397416264599123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3109
      · exact prime_twentyOneS_1182739
      · exact prime_twentyOneS_84576200383511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 621996306397416264599123) ^ 310998153198708132299561 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 621996306397416264599123) ^ 200063141330786833258 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 621996306397416264599123) ^ 525894813984671398 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 621996306397416264599123) ^ 7354271102 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2939 : Nat.Prime 2939 := by norm_num
private theorem prime_twentyOneS_16631 : Nat.Prime 16631 := by norm_num
private theorem prime_twentyOneS_18223631 : Nat.Prime 18223631 := by norm_num
private theorem prime_twentyOneS_13063 : Nat.Prime 13063 := by norm_num
private theorem prime_twentyOneS_90735599 : Nat.Prime 90735599 := by
  apply lucas_primality 90735599 (11 : ZMod 90735599)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (151, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (151, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod = 90735599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_151
      · exact prime_twentyOneS_13063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 90735599) ^ 45367799 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 3945026 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 600898 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 6946 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_7361524796742341989 : Nat.Prime 7361524796742341989 := by
  apply lucas_primality 7361524796742341989 (2 : ZMod 7361524796742341989)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (53, 1), (18223631, 1), (90735599, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (53, 1), (18223631, 1), (90735599, 1)] : List FactorBlock).map factorBlockValue).prod = 7361524796742341989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_18223631
      · exact prime_twentyOneS_90735599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7361524796742341989) ^ 3680762398371170994 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 2453841598914113996 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 1051646399534620284 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 138896694278157396 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 403954886748 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 81131605212 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_180533 : Nat.Prime 180533 := by norm_num
private theorem prime_twentyOneS_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_twentyOneS_8537 : Nat.Prime 8537 := by norm_num
private theorem prime_twentyOneS_561521 : Nat.Prime 561521 := by norm_num
private theorem prime_twentyOneS_19518469961 : Nat.Prime 19518469961 := by
  apply lucas_primality 19518469961 (3 : ZMod 19518469961)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod = 19518469961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_79
      · exact prime_twentyOneS_561521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19518469961) ^ 9759234980 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 3903693992 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 1774406360 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 247069240 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 19518469961) ^ 34760 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_44650621068881221949 : Nat.Prime 44650621068881221949 := by
  apply lucas_primality 44650621068881221949 (2 : ZMod 44650621068881221949)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod = 44650621068881221949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_2161
      · exact prime_twentyOneS_8537
      · exact prime_twentyOneS_19518469961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44650621068881221949) ^ 22325310534440610974 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 1440342615125200708 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 20662018079075068 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 5230247284629404 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44650621068881221949) ^ 2287608668 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1964627327030773765757 : Nat.Prime 1964627327030773765757 := by
  apply lucas_primality 1964627327030773765757 (3 : ZMod 1964627327030773765757)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod = 1964627327030773765757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_44650621068881221949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1964627327030773765757) ^ 982313663515386882878 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 178602484275524887796 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1964627327030773765757) ^ 44 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1447 : Nat.Prime 1447 := by norm_num
private theorem prime_twentyOneS_857 : Nat.Prime 857 := by norm_num
private theorem prime_twentyOneS_863 : Nat.Prime 863 := by norm_num
private theorem prime_twentyOneS_1431848177 : Nat.Prime 1431848177 := by
  apply lucas_primality 1431848177 (3 : ZMod 1431848177)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (11, 2), (857, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (11, 2), (857, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod = 1431848177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_857
      · exact prime_twentyOneS_863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1431848177) ^ 715924088 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1431848177) ^ 130168016 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1431848177) ^ 1670768 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1431848177) ^ 1659152 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_421 : Nat.Prime 421 := by norm_num
private theorem prime_twentyOneS_108343 : Nat.Prime 108343 := by norm_num
private theorem prime_twentyOneS_1003472867 : Nat.Prime 1003472867 := by
  apply lucas_primality 1003472867 (2 : ZMod 1003472867)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (421, 1), (108343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (421, 1), (108343, 1)] : List FactorBlock).map factorBlockValue).prod = 1003472867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_421
      · exact prime_twentyOneS_108343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1003472867) ^ 501736433 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1003472867) ^ 91224806 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1003472867) ^ 2383546 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1003472867) ^ 9262 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_96333395233 : Nat.Prime 96333395233 := by
  apply lucas_primality 96333395233 (7 : ZMod 96333395233)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (1003472867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (1003472867, 1)] : List FactorBlock).map factorBlockValue).prod = 96333395233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_1003472867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 96333395233) ^ 48166697616 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 96333395233) ^ 32111131744 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 96333395233) ^ 96 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_164152105477033 : Nat.Prime 164152105477033 := by
  apply lucas_primality 164152105477033 (13 : ZMod 164152105477033)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (71, 1), (96333395233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (71, 1), (96333395233, 1)] : List FactorBlock).map factorBlockValue).prod = 164152105477033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_71
      · exact prime_twentyOneS_96333395233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 164152105477033) ^ 82076052738516 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (13 : ZMod 164152105477033) ^ 54717368492344 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (13 : ZMod 164152105477033) ^ 2312001485592 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (13 : ZMod 164152105477033) ^ 1704 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_344827841196656494690813801 : Nat.Prime 344827841196656494690813801 := by
  apply lucas_primality 344827841196656494690813801 (97 : ZMod 344827841196656494690813801)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 344827841196656494690813801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 344827841196656494690813801) ^ 172413920598328247345406900 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 114942613732218831563604600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 68965568239331298938162760 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 49261120170950927812973400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 31347985563332408608255800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 26525218553588961130062600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 20283990658626852628871400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 18148833747192447088990200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 14992514834637238899600600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 11890615213677810161752200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 11123478748279241764219800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 9319671383693418775427400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 8410435151137963285141800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 8019252120852476620716600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 7336762578652265844485400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 6506185682955782918694600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 5844539681299262621878200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 5652915429453385158865800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_twentyOneS_25396949 : Nat.Prime 25396949 := by
  apply lucas_primality 25396949 (2 : ZMod 25396949)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (157, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (157, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod = 25396949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_157
      · exact prime_twentyOneS_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25396949) ^ 12698474 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 25396949) ^ 686404 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 25396949) ^ 161764 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 25396949) ^ 23236 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_643 : Nat.Prime 643 := by norm_num
private theorem prime_twentyOneS_11280721 : Nat.Prime 11280721 := by norm_num
private theorem prime_twentyOneS_3793 : Nat.Prime 3793 := by norm_num
private theorem prime_twentyOneS_35730061 : Nat.Prime 35730061 := by
  apply lucas_primality 35730061 (2 : ZMod 35730061)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (157, 1), (3793, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (157, 1), (3793, 1)] : List FactorBlock).map factorBlockValue).prod = 35730061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_157
      · exact prime_twentyOneS_3793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35730061) ^ 17865030 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 35730061) ^ 11910020 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 35730061) ^ 7146012 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 35730061) ^ 227580 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 35730061) ^ 9420 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_977582172022287701477 : Nat.Prime 977582172022287701477 := by
  apply lucas_primality 977582172022287701477 (2 : ZMod 977582172022287701477)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (23, 1), (41, 1), (643, 1), (11280721, 1), (35730061, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (23, 1), (41, 1), (643, 1), (11280721, 1), (35730061, 1)] : List FactorBlock).map factorBlockValue).prod = 977582172022287701477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_643
      · exact prime_twentyOneS_11280721
      · exact prime_twentyOneS_35730061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 977582172022287701477) ^ 488791086011143850738 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 977582172022287701477) ^ 42503572696621204412 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 977582172022287701477) ^ 23843467610299700036 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 977582172022287701477) ^ 1520345524140416332 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 977582172022287701477) ^ 86659547029156 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 977582172022287701477) ^ 27360215590516 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_148517 : Nat.Prime 148517 := by norm_num
private theorem prime_twentyOneS_26185717 : Nat.Prime 26185717 := by
  apply lucas_primality 26185717 (2 : ZMod 26185717)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (41, 1), (113, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (41, 1), (113, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod = 26185717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_113
      · exact prime_twentyOneS_157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26185717) ^ 13092858 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26185717) ^ 8728572 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26185717) ^ 638676 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26185717) ^ 231732 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26185717) ^ 166788 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_8588915177 : Nat.Prime 8588915177 := by
  apply lucas_primality 8588915177 (3 : ZMod 8588915177)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (41, 1), (26185717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (41, 1), (26185717, 1)] : List FactorBlock).map factorBlockValue).prod = 8588915177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_26185717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8588915177) ^ 4294457588 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8588915177) ^ 209485736 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8588915177) ^ 328 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_5641 : Nat.Prime 5641 := by norm_num
private theorem prime_twentyOneS_555077 : Nat.Prime 555077 := by norm_num
private theorem prime_twentyOneS_263019905989 : Nat.Prime 263019905989 := by
  apply lucas_primality 263019905989 (2 : ZMod 263019905989)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (5641, 1), (555077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (5641, 1), (555077, 1)] : List FactorBlock).map factorBlockValue).prod = 263019905989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_5641
      · exact prime_twentyOneS_555077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 263019905989) ^ 131509952994 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 263019905989) ^ 87673301996 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 263019905989) ^ 37574272284 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 263019905989) ^ 46626468 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 263019905989) ^ 473844 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_331034727548790234903181249 : Nat.Prime 331034727548790234903181249 := by
  apply lucas_primality 331034727548790234903181249 (67 : ZMod 331034727548790234903181249)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 331034727548790234903181249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 331034727548790234903181249) ^ 165517363774395117451590624 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 110344909182930078301060416 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 47290675364112890700454464 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 30094066140799112263925568 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 25464209811445402684860096 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 19472631032281778523716544 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 17422880397304749205430592 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 14392814241251749343616576 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 11414990605130697755282112 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 10678539598348072093651008 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 8946884528345682024410304 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 8074017745092444753736128 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 7698482036018377555887936 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 7043292075506175210705984 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 6245938255637551601946816 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 5610758094047292117003072 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (67 : ZMod 331034727548790234903181249) ^ 5426798812275249752511168 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1913 : Nat.Prime 1913 := by norm_num
private theorem prime_twentyOneS_2186231 : Nat.Prime 2186231 := by norm_num
private theorem prime_twentyOneS_151072934563 : Nat.Prime 151072934563 := by
  apply lucas_primality 151072934563 (2 : ZMod 151072934563)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (349, 1), (2186231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (349, 1), (2186231, 1)] : List FactorBlock).map factorBlockValue).prod = 151072934563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_349
      · exact prime_twentyOneS_2186231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 151072934563) ^ 75536467281 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 151072934563) ^ 50357644854 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 151072934563) ^ 13733903142 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 151072934563) ^ 432873738 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 151072934563) ^ 69102 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_311 : Nat.Prime 311 := by norm_num
private theorem prime_twentyOneS_48091 : Nat.Prime 48091 := by norm_num
private theorem prime_twentyOneS_1130367316979 : Nat.Prime 1130367316979 := by
  apply lucas_primality 1130367316979 (2 : ZMod 1130367316979)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (31, 1), (53, 1), (311, 1), (48091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (31, 1), (53, 1), (311, 1), (48091, 1)] : List FactorBlock).map factorBlockValue).prod = 1130367316979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_311
      · exact prime_twentyOneS_48091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1130367316979) ^ 565183658489 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130367316979) ^ 49146405086 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130367316979) ^ 36463461838 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130367316979) ^ 21327685226 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130367316979) ^ 3634621598 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130367316979) ^ 23504758 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_4637 : Nat.Prime 4637 := by norm_num
private theorem prime_twentyOneS_13311821 : Nat.Prime 13311821 := by norm_num
private theorem prime_twentyOneS_2076644077 : Nat.Prime 2076644077 := by
  apply lucas_primality 2076644077 (2 : ZMod 2076644077)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod = 2076644077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_13311821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2076644077) ^ 1038322038 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 692214692 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 159741852 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2076644077) ^ 156 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_809 : Nat.Prime 809 := by norm_num
private theorem prime_twentyOneS_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_twentyOneS_14851 : Nat.Prime 14851 := by norm_num
private theorem prime_twentyOneS_166895539 : Nat.Prime 166895539 := by
  apply lucas_primality 166895539 (2 : ZMod 166895539)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod = 166895539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_1873
      · exact prime_twentyOneS_14851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 166895539) ^ 83447769 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 55631846 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 89106 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 166895539) ^ 11238 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_33484585780649 : Nat.Prime 33484585780649 := by
  apply lucas_primality 33484585780649 (3 : ZMod 33484585780649)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod = 33484585780649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_809
      · exact prime_twentyOneS_166895539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33484585780649) ^ 16742292890324 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 1080147928408 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 41390093672 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 33484585780649) ^ 200632 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_620159 : Nat.Prime 620159 := by norm_num
private theorem prime_twentyOneS_1099177 : Nat.Prime 1099177 := by norm_num
private theorem prime_twentyOneS_116512763 : Nat.Prime 116512763 := by
  apply lucas_primality 116512763 (2 : ZMod 116512763)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (1099177, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (1099177, 1)] : List FactorBlock).map factorBlockValue).prod = 116512763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_1099177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116512763) ^ 58256381 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 116512763) ^ 2198354 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 116512763) ^ 106 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_292483 : Nat.Prime 292483 := by norm_num
private theorem prime_twentyOneS_938870431 : Nat.Prime 938870431 := by
  apply lucas_primality 938870431 (7 : ZMod 938870431)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (107, 1), (292483, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (107, 1), (292483, 1)] : List FactorBlock).map factorBlockValue).prod = 938870431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_107
      · exact prime_twentyOneS_292483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 938870431) ^ 469435215 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 312956810 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 187774086 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 8774490 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 938870431) ^ 3210 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_4405180062253 : Nat.Prime 4405180062253 := by
  apply lucas_primality 4405180062253 (6 : ZMod 4405180062253)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (23, 1), (938870431, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (23, 1), (938870431, 1)] : List FactorBlock).map factorBlockValue).prod = 4405180062253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_938870431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4405180062253) ^ 2202590031126 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 1468393354084 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 259128238956 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 191529567924 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4405180062253) ^ 4692 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_24091 : Nat.Prime 24091 := by norm_num
private theorem prime_twentyOneS_4517 : Nat.Prime 4517 := by norm_num
private theorem prime_twentyOneS_457 : Nat.Prime 457 := by norm_num
private theorem prime_twentyOneS_265526141 : Nat.Prime 265526141 := by
  apply lucas_primality 265526141 (2 : ZMod 265526141)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (11, 1), (19, 1), (139, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (11, 1), (19, 1), (139, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod = 265526141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_139
      · exact prime_twentyOneS_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 265526141) ^ 132763070 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 265526141) ^ 53105228 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 265526141) ^ 24138740 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 265526141) ^ 13975060 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 265526141) ^ 1910260 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 265526141) ^ 581020 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_26242468946266361 : Nat.Prime 26242468946266361 := by
  apply lucas_primality 26242468946266361 (3 : ZMod 26242468946266361)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (547, 1), (4517, 1), (265526141, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (547, 1), (4517, 1), (265526141, 1)] : List FactorBlock).map factorBlockValue).prod = 26242468946266361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_547
      · exact prime_twentyOneS_4517
      · exact prime_twentyOneS_265526141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26242468946266361) ^ 13121234473133180 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 26242468946266361) ^ 5248493789253272 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 26242468946266361) ^ 47975263155880 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 26242468946266361) ^ 5809711965080 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 26242468946266361) ^ 98831960 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_79658122242447365759227 : Nat.Prime 79658122242447365759227 := by
  apply lucas_primality 79658122242447365759227 (2 : ZMod 79658122242447365759227)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (24091, 1), (26242468946266361, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (24091, 1), (26242468946266361, 1)] : List FactorBlock).map factorBlockValue).prod = 79658122242447365759227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_24091
      · exact prime_twentyOneS_26242468946266361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79658122242447365759227) ^ 39829061121223682879613 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 79658122242447365759227) ^ 26552707414149121919742 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 79658122242447365759227) ^ 11379731748921052251318 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 79658122242447365759227) ^ 3306551087229561486 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 79658122242447365759227) ^ 3035466 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_7433 : Nat.Prime 7433 := by norm_num
private theorem prime_twentyOneS_444344741 : Nat.Prime 444344741 := by
  apply lucas_primality 444344741 (2 : ZMod 444344741)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 2), (61, 1), (7433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 2), (61, 1), (7433, 1)] : List FactorBlock).map factorBlockValue).prod = 444344741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_61
      · exact prime_twentyOneS_7433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 444344741) ^ 222172370 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 444344741) ^ 88868948 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 444344741) ^ 63477820 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 444344741) ^ 7284340 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 444344741) ^ 59780 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_110051 : Nat.Prime 110051 := by norm_num
private theorem prime_twentyOneS_13270427 : Nat.Prime 13270427 := by norm_num
private theorem prime_twentyOneS_698433059832232481 : Nat.Prime 698433059832232481 := by
  apply lucas_primality 698433059832232481 (15 : ZMod 698433059832232481)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 1), (7, 2), (61, 1), (110051, 1), (13270427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 1), (7, 2), (61, 1), (110051, 1), (13270427, 1)] : List FactorBlock).map factorBlockValue).prod = 698433059832232481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_61
      · exact prime_twentyOneS_110051
      · exact prime_twentyOneS_13270427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 698433059832232481) ^ 349216529916116240 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (15 : ZMod 698433059832232481) ^ 139686611966446496 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (15 : ZMod 698433059832232481) ^ 99776151404604640 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (15 : ZMod 698433059832232481) ^ 11449722292331680 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (15 : ZMod 698433059832232481) ^ 6346449008480 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (15 : ZMod 698433059832232481) ^ 52630790240 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_128749 : Nat.Prime 128749 := by norm_num
private theorem prime_twentyOneS_443 : Nat.Prime 443 := by norm_num
private theorem prime_twentyOneS_3457 : Nat.Prime 3457 := by norm_num
private theorem prime_twentyOneS_15683 : Nat.Prime 15683 := by norm_num
private theorem prime_twentyOneS_394811 : Nat.Prime 394811 := by norm_num
private theorem prime_twentyOneS_7510116500595532297 : Nat.Prime 7510116500595532297 := by
  apply lucas_primality 7510116500595532297 (5 : ZMod 7510116500595532297)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (11, 1), (443, 1), (3457, 1), (15683, 1), (394811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (11, 1), (443, 1), (3457, 1), (15683, 1), (394811, 1)] : List FactorBlock).map factorBlockValue).prod = 7510116500595532297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_443
      · exact prime_twentyOneS_3457
      · exact prime_twentyOneS_15683
      · exact prime_twentyOneS_394811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7510116500595532297) ^ 3755058250297766148 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 2503372166865177432 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 682737863690502936 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 16952858917822872 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 2172437518251528 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 478869891002712 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 7510116500595532297) ^ 19022054858136 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_673 : Nat.Prime 673 := by norm_num
private theorem prime_twentyOneS_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_twentyOneS_1568141 : Nat.Prime 1568141 := by norm_num
private theorem prime_twentyOneS_2035447019 : Nat.Prime 2035447019 := by
  apply lucas_primality 2035447019 (2 : ZMod 2035447019)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (59, 1), (1568141, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (59, 1), (1568141, 1)] : List FactorBlock).map factorBlockValue).prod = 2035447019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_1568141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2035447019) ^ 1017723509 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2035447019) ^ 185040638 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2035447019) ^ 34499102 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2035447019) ^ 1298 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_385087 : Nat.Prime 385087 := by norm_num
private theorem prime_twentyOneS_156868270147 : Nat.Prime 156868270147 := by
  apply lucas_primality 156868270147 (2 : ZMod 156868270147)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (53, 1), (61, 1), (385087, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (53, 1), (61, 1), (385087, 1)] : List FactorBlock).map factorBlockValue).prod = 156868270147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_61
      · exact prime_twentyOneS_385087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 156868270147) ^ 78434135073 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 156868270147) ^ 52289423382 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 156868270147) ^ 22409752878 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 156868270147) ^ 2959778682 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 156868270147) ^ 2571610986 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 156868270147) ^ 407358 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_199 : Nat.Prime 199 := by norm_num
private theorem prime_twentyOneS_1325663 : Nat.Prime 1325663 := by norm_num
private theorem prime_twentyOneS_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_twentyOneS_6577 : Nat.Prime 6577 := by norm_num
private theorem prime_twentyOneS_2162504447 : Nat.Prime 2162504447 := by
  apply lucas_primality 2162504447 (5 : ZMod 2162504447)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (79, 1), (2081, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (79, 1), (2081, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod = 2162504447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_79
      · exact prime_twentyOneS_2081
      · exact prime_twentyOneS_6577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2162504447) ^ 1081252223 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2162504447) ^ 27373474 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2162504447) ^ 1039166 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2162504447) ^ 328798 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_414779 : Nat.Prime 414779 := by norm_num
private theorem prime_twentyOneS_43520271797 : Nat.Prime 43520271797 := by
  apply lucas_primality 43520271797 (2 : ZMod 43520271797)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (1543, 1), (414779, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (1543, 1), (414779, 1)] : List FactorBlock).map factorBlockValue).prod = 43520271797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_1543
      · exact prime_twentyOneS_414779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43520271797) ^ 21760135898 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43520271797) ^ 2560015988 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43520271797) ^ 28204972 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43520271797) ^ 104924 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_18959 : Nat.Prime 18959 := by norm_num
private theorem prime_twentyOneS_20930737 : Nat.Prime 20930737 := by
  apply lucas_primality 20930737 (5 : ZMod 20930737)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (23, 1), (18959, 1)] : List FactorBlock).map factorBlockValue).prod = 20930737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_18959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20930737) ^ 10465368 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 6976912 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 910032 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 20930737) ^ 1104 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_twentyOneS_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_twentyOneS_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_67
      · exact prime_twentyOneS_28807
      · exact prime_twentyOneS_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_292089465484226677855748161 : Nat.Prime 292089465484226677855748161 := by
  apply lucas_primality 292089465484226677855748161 (149 : ZMod 292089465484226677855748161)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 1), (7, 3), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 1), (7, 3), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 292089465484226677855748161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (149 : ZMod 292089465484226677855748161) ^ 146044732742113338927874080 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 97363155161408892618582720 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 58417893096845335571149632 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 41727066497746668265106880 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 26553587771293334350522560 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 22468420421863590604288320 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 15373129762327719887144640 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 12699541977575072950249920 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 10072050533938850960543040 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 9422240822071828317927360 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 7894309877952072374479680 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 7124133304493333606237760 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 6792778267075039019901120 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 6214669478387801656505280 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 5511121990268427884070720 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 4950668906512316573826240 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (149 : ZMod 292089465484226677855748161) ^ 4788351893184043899274560 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_57203 : Nat.Prime 57203 := by norm_num
private theorem prime_twentyOneS_729338251 : Nat.Prime 729338251 := by
  apply lucas_primality 729338251 (13 : ZMod 729338251)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 3), (17, 1), (57203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 3), (17, 1), (57203, 1)] : List FactorBlock).map factorBlockValue).prod = 729338251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_57203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 729338251) ^ 364669125 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (13 : ZMod 729338251) ^ 243112750 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (13 : ZMod 729338251) ^ 145867650 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (13 : ZMod 729338251) ^ 42902250 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (13 : ZMod 729338251) ^ 12750 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_251 : Nat.Prime 251 := by norm_num
private theorem prime_twentyOneS_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_twentyOneS_3607 : Nat.Prime 3607 := by norm_num
private theorem prime_twentyOneS_90874759 : Nat.Prime 90874759 := by
  apply lucas_primality 90874759 (3 : ZMod 90874759)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (17, 1), (19, 1), (3607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (17, 1), (19, 1), (3607, 1)] : List FactorBlock).map factorBlockValue).prod = 90874759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_3607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 90874759) ^ 45437379 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 90874759) ^ 30291586 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 90874759) ^ 6990366 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 90874759) ^ 5345574 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 90874759) ^ 4782882 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 90874759) ^ 25194 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2428397475886177 : Nat.Prime 2428397475886177 := by
  apply lucas_primality 2428397475886177 (7 : ZMod 2428397475886177)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (251, 1), (1109, 1), (90874759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (251, 1), (1109, 1), (90874759, 1)] : List FactorBlock).map factorBlockValue).prod = 2428397475886177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_251
      · exact prime_twentyOneS_1109
      · exact prime_twentyOneS_90874759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2428397475886177) ^ 1214198737943088 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2428397475886177) ^ 809465825295392 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2428397475886177) ^ 9674890342176 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2428397475886177) ^ 2189718192864 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2428397475886177) ^ 26722464 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_285374765128267443882052801 : Nat.Prime 285374765128267443882052801 := by
  apply lucas_primality 285374765128267443882052801 (29 : ZMod 285374765128267443882052801)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 285374765128267443882052801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 285374765128267443882052801) ^ 142687382564133721941026400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 95124921709422481294017600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 57074953025653488776410560 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 40767823589752491983150400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 25943160466206131262004800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 21951905009866726452465600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 16786750889898084934238400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 15019724480435128625371200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 12407598483837714951393600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 9205637584782820770388800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 7712831489953174158974400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 6960360125079693753220800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 6636622444843428927489600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 6071803513367392423022400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 5384429530722027243057600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 4836860425902838031899200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (29 : ZMod 285374765128267443882052801) ^ 4678274838168318752164800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_859 : Nat.Prime 859 := by norm_num
private theorem prime_twentyOneS_156823 : Nat.Prime 156823 := by norm_num
private theorem prime_twentyOneS_811703 : Nat.Prime 811703 := by norm_num
private theorem prime_twentyOneS_46788184327 : Nat.Prime 46788184327 := by
  apply lucas_primality 46788184327 (3 : ZMod 46788184327)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (739, 1), (811703, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (739, 1), (811703, 1)] : List FactorBlock).map factorBlockValue).prod = 46788184327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_739
      · exact prime_twentyOneS_811703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46788184327) ^ 23394092163 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 46788184327) ^ 15596061442 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 46788184327) ^ 3599091102 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 46788184327) ^ 63312834 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 46788184327) ^ 57642 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_190395439210967063 : Nat.Prime 190395439210967063 := by
  apply lucas_primality 190395439210967063 (5 : ZMod 190395439210967063)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (173, 1), (619, 1), (46788184327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (173, 1), (619, 1), (46788184327, 1)] : List FactorBlock).map factorBlockValue).prod = 190395439210967063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_173
      · exact prime_twentyOneS_619
      · exact prime_twentyOneS_46788184327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 190395439210967063) ^ 95197719605483531 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 190395439210967063) ^ 10020812590050898 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 190395439210967063) ^ 1100551671739694 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 190395439210967063) ^ 307585523765698 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (5 : ZMod 190395439210967063) ^ 4069306 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1337593 : Nat.Prime 1337593 := by norm_num
private theorem prime_twentyOneS_15475567 : Nat.Prime 15475567 := by norm_num
private theorem prime_twentyOneS_1547556701 : Nat.Prime 1547556701 := by
  apply lucas_primality 1547556701 (2 : ZMod 1547556701)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (15475567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (15475567, 1)] : List FactorBlock).map factorBlockValue).prod = 1547556701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_15475567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1547556701) ^ 773778350 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1547556701) ^ 309511340 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1547556701) ^ 100 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2017 : Nat.Prime 2017 := by norm_num
private theorem prime_twentyOneS_7649238529 : Nat.Prime 7649238529 := by
  apply lucas_primality 7649238529 (17 : ZMod 7649238529)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (3, 2), (823, 1), (2017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (3, 2), (823, 1), (2017, 1)] : List FactorBlock).map factorBlockValue).prod = 7649238529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_823
      · exact prime_twentyOneS_2017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 7649238529) ^ 3824619264 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 7649238529) ^ 2549746176 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 7649238529) ^ 9294336 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (17 : ZMod 7649238529) ^ 3792384 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_18561404377982889875873 : Nat.Prime 18561404377982889875873 := by
  apply lucas_primality 18561404377982889875873 (3 : ZMod 18561404377982889875873)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (7, 2), (1547556701, 1), (7649238529, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (7, 2), (1547556701, 1), (7649238529, 1)] : List FactorBlock).map factorBlockValue).prod = 18561404377982889875873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_1547556701
      · exact prime_twentyOneS_7649238529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18561404377982889875873) ^ 9280702188991444937936 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 18561404377982889875873) ^ 2651629196854698553696 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 18561404377982889875873) ^ 11994006013472 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 18561404377982889875873) ^ 2426568907168 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_twentyOneS_23669 : Nat.Prime 23669 := by norm_num
private theorem prime_twentyOneS_60397 : Nat.Prime 60397 := by norm_num
private theorem prime_twentyOneS_1462090577 : Nat.Prime 1462090577 := by
  apply lucas_primality 1462090577 (6 : ZMod 1462090577)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (17, 1), (89, 1), (60397, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (17, 1), (89, 1), (60397, 1)] : List FactorBlock).map factorBlockValue).prod = 1462090577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_89
      · exact prime_twentyOneS_60397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1462090577) ^ 731045288 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1462090577) ^ 86005328 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1462090577) ^ 16427984 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1462090577) ^ 24208 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_914737 : Nat.Prime 914737 := by norm_num
private theorem prime_twentyOneS_3911415413 : Nat.Prime 3911415413 := by
  apply lucas_primality 3911415413 (2 : ZMod 3911415413)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1069, 1), (914737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1069, 1), (914737, 1)] : List FactorBlock).map factorBlockValue).prod = 3911415413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_1069
      · exact prime_twentyOneS_914737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3911415413) ^ 1955707706 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3911415413) ^ 3658948 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3911415413) ^ 4276 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_270718619192664568942739 : Nat.Prime 270718619192664568942739 := by
  apply lucas_primality 270718619192664568942739 (2 : ZMod 270718619192664568942739)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23669, 1), (1462090577, 1), (3911415413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23669, 1), (1462090577, 1), (3911415413, 1)] : List FactorBlock).map factorBlockValue).prod = 270718619192664568942739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_23669
      · exact prime_twentyOneS_1462090577
      · exact prime_twentyOneS_3911415413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 270718619192664568942739) ^ 135359309596332284471369 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 270718619192664568942739) ^ 11437687236159726602 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 270718619192664568942739) ^ 185158582820594 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 270718619192664568942739) ^ 69212443734026 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_272830819408343600194929601 : Nat.Prime 272830819408343600194929601 := by
  apply lucas_primality 272830819408343600194929601 (39 : ZMod 272830819408343600194929601)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 272830819408343600194929601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_23
      · exact prime_twentyOneS_29
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_37
      · exact prime_twentyOneS_41
      · exact prime_twentyOneS_43
      · exact prime_twentyOneS_47
      · exact prime_twentyOneS_53
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (39 : ZMod 272830819408343600194929601) ^ 136415409704171800097464800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 90943606469447866731643200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 54566163881668720038985920 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 38975831344049085742132800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 24802801764394872744993600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 16048871729902564717348800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 14359516810965452641838400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 11862209539493200008475200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 9407959289942882765342400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 8800994174462696780481600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 7373805929955232437700800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 6654410229471795126705600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 6344902776938223260347200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 5804911051241353195636800 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 5147751309591388682923200 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 4624251176412603393134400 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (39 : ZMod 272830819408343600194929601) ^ 4472636383743337708113600 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2393 : Nat.Prime 2393 := by norm_num
private theorem prime_twentyOneS_8887 : Nat.Prime 8887 := by norm_num
private theorem prime_twentyOneS_69767 : Nat.Prime 69767 := by norm_num
private theorem prime_twentyOneS_489449 : Nat.Prime 489449 := by norm_num
private theorem prime_twentyOneS_68111 : Nat.Prime 68111 := by norm_num
private theorem prime_twentyOneS_371613617 : Nat.Prime 371613617 := by
  apply lucas_primality 371613617 (3 : ZMod 371613617)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (11, 1), (31, 1), (68111, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (11, 1), (31, 1), (68111, 1)] : List FactorBlock).map factorBlockValue).prod = 371613617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_11
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_68111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 371613617) ^ 185806808 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 371613617) ^ 33783056 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 371613617) ^ 11987536 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 371613617) ^ 5456 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2099 : Nat.Prime 2099 := by norm_num
private theorem prime_twentyOneS_319919 : Nat.Prime 319919 := by norm_num
private theorem prime_twentyOneS_719 : Nat.Prime 719 := by norm_num
private theorem prime_twentyOneS_20354891 : Nat.Prime 20354891 := by
  apply lucas_primality 20354891 (2 : ZMod 20354891)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (19, 1), (149, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (19, 1), (149, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod = 20354891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_149
      · exact prime_twentyOneS_719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20354891) ^ 10177445 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 4070978 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 1071310 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 136610 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 20354891) ^ 28310 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_853 : Nat.Prime 853 := by norm_num
private theorem prime_twentyOneS_75997183 : Nat.Prime 75997183 := by
  apply lucas_primality 75997183 (3 : ZMod 75997183)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (31, 1), (479, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (31, 1), (479, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod = 75997183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_31
      · exact prime_twentyOneS_479
      · exact prime_twentyOneS_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75997183) ^ 37998591 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 25332394 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 2451522 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 158658 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 75997183) ^ 89094 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_30859 : Nat.Prime 30859 := by norm_num
private theorem prime_twentyOneS_751 : Nat.Prime 751 := by norm_num
private theorem prime_twentyOneS_50363 : Nat.Prime 50363 := by norm_num
private theorem prime_twentyOneS_268529 : Nat.Prime 268529 := by norm_num
private theorem prime_twentyOneS_17300786413 : Nat.Prime 17300786413 := by
  apply lucas_primality 17300786413 (14 : ZMod 17300786413)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (13, 1), (59, 1), (268529, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (13, 1), (59, 1), (268529, 1)] : List FactorBlock).map factorBlockValue).prod = 17300786413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_7
      · exact prime_twentyOneS_13
      · exact prime_twentyOneS_59
      · exact prime_twentyOneS_268529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 17300786413) ^ 8650393206 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 17300786413) ^ 5766928804 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 17300786413) ^ 2471540916 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 17300786413) ^ 1330829724 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 17300786413) ^ 293233668 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (14 : ZMod 17300786413) ^ 64428 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_69203145653 : Nat.Prime 69203145653 := by
  apply lucas_primality 69203145653 (2 : ZMod 69203145653)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17300786413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17300786413, 1)] : List FactorBlock).map factorBlockValue).prod = 69203145653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_17300786413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 69203145653) ^ 34601572826 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 69203145653) ^ 4 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_78523313892481538671 : Nat.Prime 78523313892481538671 := by
  apply lucas_primality 78523313892481538671 (3 : ZMod 78523313892481538671)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (751, 1), (50363, 1), (69203145653, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (751, 1), (50363, 1), (69203145653, 1)] : List FactorBlock).map factorBlockValue).prod = 78523313892481538671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_751
      · exact prime_twentyOneS_50363
      · exact prime_twentyOneS_69203145653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78523313892481538671) ^ 39261656946240769335 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 78523313892481538671) ^ 26174437964160512890 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 78523313892481538671) ^ 15704662778496307734 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 78523313892481538671) ^ 104558340735661170 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 78523313892481538671) ^ 1559146871562090 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 78523313892481538671) ^ 1134678390 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_313 : Nat.Prime 313 := by norm_num
private theorem prime_twentyOneS_14723 : Nat.Prime 14723 := by norm_num
private theorem prime_twentyOneS_32609 : Nat.Prime 32609 := by norm_num
private theorem prime_twentyOneS_59359 : Nat.Prime 59359 := by norm_num
private theorem prime_twentyOneS_1889743 : Nat.Prime 1889743 := by norm_num
private theorem prime_twentyOneS_143620469 : Nat.Prime 143620469 := by
  apply lucas_primality 143620469 (2 : ZMod 143620469)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (1889743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (1889743, 1)] : List FactorBlock).map factorBlockValue).prod = 143620469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_1889743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 143620469) ^ 71810234 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 143620469) ^ 7558972 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 143620469) ^ 76 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_14649287839 : Nat.Prime 14649287839 := by
  apply lucas_primality 14649287839 (3 : ZMod 14649287839)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (143620469, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (143620469, 1)] : List FactorBlock).map factorBlockValue).prod = 14649287839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_143620469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14649287839) ^ 7324643919 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 14649287839) ^ 4883095946 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 14649287839) ^ 861722814 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 14649287839) ^ 102 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_56711425617038138819 : Nat.Prime 56711425617038138819 := by
  apply lucas_primality 56711425617038138819 (2 : ZMod 56711425617038138819)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (32609, 1), (59359, 1), (14649287839, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (32609, 1), (59359, 1), (14649287839, 1)] : List FactorBlock).map factorBlockValue).prod = 56711425617038138819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_32609
      · exact prime_twentyOneS_59359
      · exact prime_twentyOneS_14649287839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56711425617038138819) ^ 28355712808519069409 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 56711425617038138819) ^ 1739134153670402 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 56711425617038138819) ^ 955397254283902 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 56711425617038138819) ^ 3871275262 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_5821 : Nat.Prime 5821 := by norm_num
private theorem prime_twentyOneS_28979 : Nat.Prime 28979 := by norm_num
private theorem prime_twentyOneS_10211 : Nat.Prime 10211 := by norm_num
private theorem prime_twentyOneS_6271 : Nat.Prime 6271 := by norm_num
private theorem prime_twentyOneS_83609 : Nat.Prime 83609 := by norm_num
private theorem prime_twentyOneS_119543144893 : Nat.Prime 119543144893 := by
  apply lucas_primality 119543144893 (2 : ZMod 119543144893)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (6271, 1), (83609, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (6271, 1), (83609, 1)] : List FactorBlock).map factorBlockValue).prod = 119543144893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_19
      · exact prime_twentyOneS_6271
      · exact prime_twentyOneS_83609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 119543144893) ^ 59771572446 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 39847714964 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 6291744468 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 19062852 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 119543144893) ^ 1429788 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_1533142745943043289 : Nat.Prime 1533142745943043289 := by
  apply lucas_primality 1533142745943043289 (3 : ZMod 1533142745943043289)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (157, 1), (10211, 1), (119543144893, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (157, 1), (10211, 1), (119543144893, 1)] : List FactorBlock).map factorBlockValue).prod = 1533142745943043289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_157
      · exact prime_twentyOneS_10211
      · exact prime_twentyOneS_119543144893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1533142745943043289) ^ 766571372971521644 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1533142745943043289) ^ 9765240420019384 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1533142745943043289) ^ 150146189985608 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1533142745943043289) ^ 12825016 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_2447 : Nat.Prime 2447 := by norm_num
private theorem prime_twentyOneS_45293 : Nat.Prime 45293 := by norm_num
private theorem prime_twentyOneS_11933 : Nat.Prime 11933 := by norm_num
private theorem prime_twentyOneS_569 : Nat.Prime 569 := by norm_num
private theorem prime_twentyOneS_1667 : Nat.Prime 1667 := by norm_num
private theorem prime_twentyOneS_19403143 : Nat.Prime 19403143 := by norm_num
private theorem prime_twentyOneS_184043274077891 : Nat.Prime 184043274077891 := by
  apply lucas_primality 184043274077891 (2 : ZMod 184043274077891)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (569, 1), (1667, 1), (19403143, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (569, 1), (1667, 1), (19403143, 1)] : List FactorBlock).map factorBlockValue).prod = 184043274077891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_569
      · exact prime_twentyOneS_1667
      · exact prime_twentyOneS_19403143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 184043274077891) ^ 92021637038945 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 184043274077891) ^ 36808654815578 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 184043274077891) ^ 323450393810 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 184043274077891) ^ 110403883670 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 184043274077891) ^ 9485230 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_224011215736290276907 : Nat.Prime 224011215736290276907 := by
  apply lucas_primality 224011215736290276907 (3 : ZMod 224011215736290276907)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (11933, 1), (184043274077891, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (11933, 1), (184043274077891, 1)] : List FactorBlock).map factorBlockValue).prod = 224011215736290276907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_11933
      · exact prime_twentyOneS_184043274077891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 224011215736290276907) ^ 112005607868145138453 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 224011215736290276907) ^ 74670405245430092302 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 224011215736290276907) ^ 13177130337428839818 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 224011215736290276907) ^ 18772413955944882 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (3 : ZMod 224011215736290276907) ^ 1217166 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_339389 : Nat.Prime 339389 := by norm_num
private theorem prime_twentyOneS_545911 : Nat.Prime 545911 := by norm_num
private theorem prime_twentyOneS_2940799 : Nat.Prime 2940799 := by norm_num
private theorem prime_twentyOneS_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_twentyOneS_464968781 : Nat.Prime 464968781 := by
  apply lucas_primality 464968781 (2 : ZMod 464968781)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod = 464968781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_103
      · exact prime_twentyOneS_131
      · exact prime_twentyOneS_1723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 464968781) ^ 232484390 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 92993756 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 4514260 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 3549380 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 464968781) ^ 269860 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_15959533 : Nat.Prime 15959533 := by norm_num
private theorem prime_twentyOneS_2687 : Nat.Prime 2687 := by norm_num
private theorem prime_twentyOneS_370537 : Nat.Prime 370537 := by norm_num
private theorem prime_twentyOneS_1686291654781 : Nat.Prime 1686291654781 := by
  apply lucas_primality 1686291654781 (2 : ZMod 1686291654781)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (131, 1), (193, 1), (370537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (131, 1), (193, 1), (370537, 1)] : List FactorBlock).map factorBlockValue).prod = 1686291654781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_5
      · exact prime_twentyOneS_131
      · exact prime_twentyOneS_193
      · exact prime_twentyOneS_370537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1686291654781) ^ 843145827390 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 562097218260 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 337258330956 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 12872455380 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 8737262460 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1686291654781) ^ 4550940 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem prime_twentyOneS_15713735765743224997 : Nat.Prime 15713735765743224997 := by
  apply lucas_primality 15713735765743224997 (2 : ZMod 15713735765743224997)
  · rw [← twentyOneSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 2), (2687, 1), (1686291654781, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 2), (2687, 1), (1686291654781, 1)] : List FactorBlock).map factorBlockValue).prod = 15713735765743224997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyOneS_2
      · exact prime_twentyOneS_3
      · exact prime_twentyOneS_17
      · exact prime_twentyOneS_2687
      · exact prime_twentyOneS_1686291654781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15713735765743224997) ^ 7856867882871612498 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 5237911921914408332 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 924337397984895588 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 5848059458780508 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15713735765743224997) ^ 9318516 ≠ 1
      rw [← twentyOneSFastPow_eq_pow]
      decide

private theorem phi_twentyOneS_24827604566159267617738593600 : Nat.totient 24827604566159267617738593600 = 3266998737646573427097600000 := by
  rw [← show ((([(2, 6), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593600 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_5, prime_twentyOneS_7, prime_twentyOneS_11, prime_twentyOneS_13, prime_twentyOneS_17, prime_twentyOneS_19, prime_twentyOneS_23, prime_twentyOneS_29, prime_twentyOneS_31, prime_twentyOneS_37, prime_twentyOneS_41, prime_twentyOneS_43, prime_twentyOneS_47, prime_twentyOneS_53, prime_twentyOneS_59, prime_twentyOneS_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593601 : Nat.totient 24827604566159267617738593601 = 24776621600609126786919635520 := by
  rw [← show ((([(487, 1), (10972711, 1), (4646135993926002193, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_487, prime_twentyOneS_10972711, prime_twentyOneS_4646135993926002193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593602 : Nat.totient 24827604566159267617738593602 = 12413802283079633808869296800 := by
  rw [← show ((([(2, 1), (12413802283079633808869296801, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_12413802283079633808869296801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593603 : Nat.totient 24827604566159267617738593603 = 16551606546661648594314053384 := by
  rw [← show ((([(3, 1), (127487, 1), (64915388931575422377023, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_127487, prime_twentyOneS_64915388931575422377023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593604 : Nat.totient 24827604566159267617738593604 = 12413779926059891313764496864 := by
  rw [← show ((([(2, 2), (555253, 1), (11178509871247551844717, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_555253, prime_twentyOneS_11178509871247551844717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593605 : Nat.totient 24827604566159267617738593605 = 19862082389554222650585244800 := by
  rw [← show ((([(5, 1), (15756119, 1), (8977309801, 1), (35105030159, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_5, prime_twentyOneS_15756119, prime_twentyOneS_8977309801, prime_twentyOneS_35105030159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593606 : Nat.totient 24827604566159267617738593606 = 8275845428494711196383989800 := by
  rw [← show ((([(2, 1), (3, 1), (363611, 1), (11380112522338097407091, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_363611, prime_twentyOneS_11380112522338097407091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593607 : Nat.totient 24827604566159267617738593607 = 21280803913151441936032356600 := by
  rw [← show ((([(7, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_7, prime_twentyOneS_30429025931, prime_twentyOneS_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593608 : Nat.totient 24827604566159267617738593608 = 12290892604645637303489164800 := by
  rw [← show ((([(2, 3), (101, 1), (16499213, 1), (1862345396350691977, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_101, prime_twentyOneS_16499213, prime_twentyOneS_1862345396350691977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593609 : Nat.totient 24827604566159267617738593609 = 16430920783443602900303885952 := by
  rw [← show ((([(3, 2), (137, 1), (20135932332651474142529273, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_137, prime_twentyOneS_20135932332651474142529273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593610 : Nat.totient 24827604566159267617738593610 = 9931041826463707047095437440 := by
  rw [← show ((([(2, 1), (5, 1), (2482760456615926761773859361, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_5, prime_twentyOneS_2482760456615926761773859361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593611 : Nat.totient 24827604566159267617738593611 = 22570549605599334197944176000 := by
  rw [← show ((([(11, 1), (2257054960559933419794417601, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_11, prime_twentyOneS_2257054960559933419794417601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593612 : Nat.totient 24827604566159267617738593612 = 8271998644469182032865992768 := by
  rw [← show ((([(2, 2), (3, 1), (3023, 1), (7309, 1), (93639150386551147643, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_3023, prime_twentyOneS_7309, prime_twentyOneS_93639150386551147643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593613 : Nat.totient 24827604566159267617738593613 = 22875891592951135062779246064 := by
  rw [← show ((([(13, 1), (547, 1), (3491436445810612799569483, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_13, prime_twentyOneS_547, prime_twentyOneS_3491436445810612799569483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593614 : Nat.totient 24827604566159267617738593614 = 10638994852183451653731525120 := by
  rw [← show ((([(2, 1), (7, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_7, prime_twentyOneS_8233, prime_twentyOneS_93811, prime_twentyOneS_8274073, prime_twentyOneS_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593615 : Nat.totient 24827604566159267617738593615 = 13092609449120692436620201472 := by
  rw [← show ((([(3, 1), (5, 1), (89, 1), (18597456603864619938380969, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_5, prime_twentyOneS_89, prime_twentyOneS_18597456603864619938380969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593616 : Nat.totient 24827604566159267617738593616 = 12404721228007885722688693856 := by
  rw [← show ((([(2, 4), (1367, 1), (1135131883968510772574003, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_1367, prime_twentyOneS_1135131883968510772574003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593617 : Nat.totient 24827604566159267617738593617 = 23070663703901839199049875712 := by
  rw [← show ((([(17, 1), (83, 1), (1543, 1), (11403597493703654977229, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_17, prime_twentyOneS_83, prime_twentyOneS_1543, prime_twentyOneS_11403597493703654977229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593618 : Nat.totient 24827604566159267617738593618 = 8244113747563553753312939520 := by
  rw [← show ((([(2, 1), (3, 2), (263, 1), (33811, 1), (189853, 1), (817016986973969, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_263, prime_twentyOneS_33811, prime_twentyOneS_189853, prime_twentyOneS_817016986973969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593619 : Nat.totient 24827604566159267617738593619 = 23520887723631847361264566272 := by
  rw [← show ((([(19, 1), (28940609, 1), (45151642448085877889, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_19, prime_twentyOneS_28940609, prime_twentyOneS_45151642448085877889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593620 : Nat.totient 24827604566159267617738593620 = 9931041826348654134608580000 := by
  rw [← show ((([(2, 2), (5, 1), (86317688251, 1), (14381527743168931, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_5, prime_twentyOneS_86317688251, prime_twentyOneS_14381527743168931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593621 : Nat.totient 24827604566159267617738593621 = 14046657934239547674011714304 := by
  rw [← show ((([(3, 1), (7, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_7, prime_twentyOneS_103, prime_twentyOneS_5009, prime_twentyOneS_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593622 : Nat.totient 24827604566159267617738593622 = 11253839496650985669154500480 := by
  rw [← show ((([(2, 1), (11, 1), (359, 1), (38651421607, 1), (81330270790577, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_11, prime_twentyOneS_359, prime_twentyOneS_38651421607, prime_twentyOneS_81330270790577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593623 : Nat.totient 24827604566159267617738593623 = 23748143350125118194406762560 := by
  rw [← show ((([(23, 1), (213426679, 1), (712658239, 1), (7097035321, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_23, prime_twentyOneS_213426679, prime_twentyOneS_712658239, prime_twentyOneS_7097035321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593624 : Nat.totient 24827604566159267617738593624 = 8232988042664213096037666816 := by
  rw [← show ((([(2, 3), (3, 1), (193, 1), (5360018256942847067732857, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_193, prime_twentyOneS_5360018256942847067732857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593625 : Nat.totient 24827604566159267617738593625 = 19805171063092871920342329600 := by
  rw [← show ((([(5, 3), (349, 1), (16850357, 1), (33774604584521293, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_5, prime_twentyOneS_349, prime_twentyOneS_16850357, prime_twentyOneS_33774604584521293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593626 : Nat.totient 24827604566159267617738593626 = 11320291815548203485573488640 := by
  rw [← show ((([(2, 1), (13, 1), (167, 1), (173, 1), (2731, 1), (142700137, 1), (84811121713, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_13, prime_twentyOneS_167, prime_twentyOneS_173, prime_twentyOneS_2731, prime_twentyOneS_142700137, prime_twentyOneS_84811121713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593627 : Nat.totient 24827604566159267617738593627 = 16551736377439511745159062400 := by
  rw [← show ((([(3, 3), (919540909857750652508836801, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_919540909857750652508836801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593628 : Nat.totient 24827604566159267617738593628 = 10620369962419606207605964800 := by
  rw [← show ((([(2, 2), (7, 1), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_7, prime_twentyOneS_769, prime_twentyOneS_2143, prime_twentyOneS_8597, prime_twentyOneS_9792301, prime_twentyOneS_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593629 : Nat.totient 24827604566159267617738593629 = 23971478923180627879786433856 := by
  rw [← show ((([(29, 1), (17788357, 1), (48128351335921711693, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_29, prime_twentyOneS_17788357, prime_twentyOneS_48128351335921711693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593630 : Nat.totient 24827604566159267617738593630 = 6552316620150743707747430400 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (97, 1), (72973, 1), (195271, 1), (598744972004371, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_5, prime_twentyOneS_97, prime_twentyOneS_72973, prime_twentyOneS_195271, prime_twentyOneS_598744972004371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593631 : Nat.totient 24827604566159267617738593631 = 24025232520523386471524086560 := by
  rw [← show ((([(31, 2), (16217, 1), (1593092214812622769463, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_31, prime_twentyOneS_16217, prime_twentyOneS_1593092214812622769463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593632 : Nat.totient 24827604566159267617738593632 = 12232922533489403409029184000 := by
  rw [← show ((([(2, 5), (71, 1), (2029, 1), (2245339, 1), (2398625938490051, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_71, prime_twentyOneS_2029, prime_twentyOneS_2245339, prime_twentyOneS_2398625938490051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593633 : Nat.totient 24827604566159267617738593633 = 15047033070399556131962784000 := by
  rw [← show ((([(3, 1), (11, 1), (752351653519977806598139201, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_11, prime_twentyOneS_752351653519977806598139201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593634 : Nat.totient 24827604566159267617738593634 = 11672154507528618329717037312 := by
  rw [← show ((([(2, 1), (17, 1), (1879, 1), (2243, 1), (173260613935464457133, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_17, prime_twentyOneS_1879, prime_twentyOneS_2243, prime_twentyOneS_173260613935464457133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593635 : Nat.totient 24827604566159267617738593635 = 16941101785182382994115471360 := by
  rw [← show ((([(5, 1), (7, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_5, prime_twentyOneS_7, prime_twentyOneS_281, prime_twentyOneS_739, prime_twentyOneS_3540386347, prime_twentyOneS_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593636 : Nat.totient 24827604566159267617738593636 = 8177445995438811281021644800 := by
  rw [← show ((([(2, 2), (3, 2), (131, 1), (233, 1), (550990241, 1), (41007301887107, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_131, prime_twentyOneS_233, prime_twentyOneS_550990241, prime_twentyOneS_41007301887107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593637 : Nat.totient 24827604566159267617738593637 = 24125337065643036484669013952 := by
  rw [← show ((([(37, 1), (773, 1), (33352703, 1), (26026907316507379, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_37, prime_twentyOneS_773, prime_twentyOneS_33352703, prime_twentyOneS_26026907316507379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593638 : Nat.totient 24827604566159267617738593638 = 11760408790550171425325187072 := by
  rw [← show ((([(2, 1), (19, 1), (331489, 1), (1970979474127129694209, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_19, prime_twentyOneS_331489, prime_twentyOneS_1970979474127129694209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593639 : Nat.totient 24827604566159267617738593639 = 15277055525411475347645477280 := by
  rw [← show ((([(3, 1), (13, 2), (10391, 1), (4712696973609818164547, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_13, prime_twentyOneS_10391, prime_twentyOneS_4712696973609818164547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593640 : Nat.totient 24827604566159267617738593640 = 9931019213308861978295054400 := by
  rw [← show ((([(2, 3), (5, 1), (439171, 1), (1413322177816799584771, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_5, prime_twentyOneS_439171, prime_twentyOneS_1413322177816799584771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593641 : Nat.totient 24827604566159267617738593641 = 24157200706463363325713815680 := by
  rw [← show ((([(41, 2), (683, 1), (823, 1), (26275232482769198029, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_41, prime_twentyOneS_683, prime_twentyOneS_823, prime_twentyOneS_26275232482769198029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593642 : Nat.totient 24827604566159267617738593642 = 7093601298814946944586473200 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_7, prime_twentyOneS_1222615931, prime_twentyOneS_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593643 : Nat.totient 24827604566159267617738593643 = 24250218400348903079929471968 := by
  rw [← show ((([(43, 1), (1849892749, 1), (312118717700524549, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_43, prime_twentyOneS_1849892749, prime_twentyOneS_312118717700524549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593644 : Nat.totient 24827604566159267617738593644 = 11282015988245003608617132240 := by
  rw [← show ((([(2, 2), (11, 1), (3463, 1), (162940727733174517744327, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_11, prime_twentyOneS_3463, prime_twentyOneS_162940727733174517744327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593645 : Nat.totient 24827604566159267617738593645 = 13241389101420110042942182368 := by
  rw [← show ((([(3, 2), (5, 1), (24913302187, 1), (22145781469408963, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_5, prime_twentyOneS_24913302187, prime_twentyOneS_22145781469408963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593646 : Nat.totient 24827604566159267617738593646 = 11874071749032693208483675200 := by
  rw [← show ((([(2, 1), (23, 1), (539730534046940600385621601, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_23, prime_twentyOneS_539730534046940600385621601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593647 : Nat.totient 24827604566159267617738593647 = 24165103886507228905746180000 := by
  rw [← show ((([(47, 1), (181, 1), (7601051, 1), (383958901408250471, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_47, prime_twentyOneS_181, prime_twentyOneS_7601051, prime_twentyOneS_383958901408250471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593648 : Nat.totient 24827604566159267617738593648 = 8169798577282448507783036928 := by
  rw [← show ((([(2, 4), (3, 1), (79, 1), (6229, 1), (8696692033, 1), (120863194567, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_79, prime_twentyOneS_6229, prime_twentyOneS_8696692033, prime_twentyOneS_120863194567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593649 : Nat.totient 24827604566159267617738593649 = 21251531304717083199877503456 := by
  rw [← show ((([(7, 2), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_7, prime_twentyOneS_727, prime_twentyOneS_40346827, prime_twentyOneS_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593650 : Nat.totient 24827604566159267617738593650 = 9930005501999494511539154880 := by
  rw [← show ((([(2, 1), (5, 2), (12853, 1), (37663, 1), (1025759145018831907, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_5, prime_twentyOneS_12853, prime_twentyOneS_37663, prime_twentyOneS_1025759145018831907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593651 : Nat.totient 24827604566159267617738593651 = 15578093255058884506772002304 := by
  rw [← show ((([(3, 1), (17, 1), (1346333, 1), (361586454322254942197, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_17, prime_twentyOneS_1346333, prime_twentyOneS_361586454322254942197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593652 : Nat.totient 24827604566159267617738593652 = 11307455281910557667990131200 := by
  rw [← show ((([(2, 2), (13, 1), (113, 1), (227, 1), (18613462787595076228651, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_13, prime_twentyOneS_113, prime_twentyOneS_227, prime_twentyOneS_18613462787595076228651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593653 : Nat.totient 24827604566159267617738593653 = 24022135906032404776392364608 := by
  rw [← show ((([(53, 1), (107, 1), (223, 1), (20807, 1), (943541142785218363, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_53, prime_twentyOneS_107, prime_twentyOneS_223, prime_twentyOneS_20807, prime_twentyOneS_943541142785218363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593654 : Nat.totient 24827604566159267617738593654 = 8254298826058422344163390720 := by
  rw [← show ((([(2, 1), (3, 3), (521, 1), (1453, 1), (607348163015529886877, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_521, prime_twentyOneS_1453, prime_twentyOneS_607348163015529886877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593655 : Nat.totient 24827604566159267617738593655 = 18051383270514436973311977600 := by
  rw [← show ((([(5, 1), (11, 1), (3571, 1), (4420502423, 1), (28596352840637, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_5, prime_twentyOneS_11, prime_twentyOneS_3571, prime_twentyOneS_4420502423, prime_twentyOneS_28596352840637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593656 : Nat.totient 24827604566159267617738593656 = 10611602142969028764886917120 := by
  rw [← show ((([(2, 3), (7, 1), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_7, prime_twentyOneS_373, prime_twentyOneS_55249, prime_twentyOneS_157429, prime_twentyOneS_773027, prime_twentyOneS_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593657 : Nat.totient 24827604566159267617738593657 = 15680592353462415706736672400 := by
  rw [← show ((([(3, 1), (19, 1), (3813504911, 1), (114218290024018991, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_19, prime_twentyOneS_3813504911, prime_twentyOneS_114218290024018991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593658 : Nat.totient 24827604566159267617738593658 = 11985740115554269845046422576 := by
  rw [← show ((([(2, 1), (29, 1), (604334323, 1), (708320099324229787, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_29, prime_twentyOneS_604334323, prime_twentyOneS_708320099324229787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593659 : Nat.totient 24827604566159267617738593659 = 24405919266982877168298310144 := by
  rw [← show ((([(59, 1), (28493, 1), (1182917, 1), (20675069, 1), (603869909, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_59, prime_twentyOneS_28493, prime_twentyOneS_1182917, prime_twentyOneS_20675069, prime_twentyOneS_603869909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593660 : Nat.totient 24827604566159267617738593660 = 6609998760007932994254531072 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (619, 1), (70908014633, 1), (9427522870043, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_5, prime_twentyOneS_619, prime_twentyOneS_70908014633, prime_twentyOneS_9427522870043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593661 : Nat.totient 24827604566159267617738593661 = 24055667812313361415961763840 := by
  rw [← show ((([(61, 1), (67, 1), (59123, 1), (718657, 1), (142972351132073, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_61, prime_twentyOneS_67, prime_twentyOneS_59123, prime_twentyOneS_718657, prime_twentyOneS_142972351132073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593662 : Nat.totient 24827604566159267617738593662 = 12013357048141581105357384000 := by
  rw [← show ((([(2, 1), (31, 1), (400445234938052703511912801, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_31, prime_twentyOneS_400445234938052703511912801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593663 : Nat.totient 24827604566159267617738593663 = 14187202609233867210136339200 := by
  rw [← show ((([(3, 2), (7, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_7, prime_twentyOneS_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593664 : Nat.totient 24827604566159267617738593664 = 12355257914908495562861107200 := by
  rw [← show ((([(2, 7), (229, 1), (2851, 1), (27689743, 1), (10729345378379, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_229, prime_twentyOneS_2851, prime_twentyOneS_27689743, prime_twentyOneS_10729345378379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593665 : Nat.totient 24827604566159267617738593665 = 18334231054707853778550206400 := by
  rw [← show ((([(5, 1), (13, 1), (1923271411, 1), (198600751296500731, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_5, prime_twentyOneS_13, prime_twentyOneS_1923271411, prime_twentyOneS_198600751296500731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593666 : Nat.totient 24827604566159267617738593666 = 7523516535199778065981392000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (376175826759988903299069601, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_11, prime_twentyOneS_376175826759988903299069601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593667 : Nat.totient 24827604566159267617738593667 = 24663183343866822136826417400 := by
  rw [← show ((([(151, 1), (164421222292445480912176117, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_151, prime_twentyOneS_164421222292445480912176117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593668 : Nat.totient 24827604566159267617738593668 = 11663674737564349793762735744 := by
  rw [← show ((([(2, 2), (17, 1), (587, 1), (621996306397416264599123, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_17, prime_twentyOneS_587, prime_twentyOneS_621996306397416264599123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593669 : Nat.totient 24827604566159267617738593669 = 15825757127512036436651599680 := by
  rw [← show ((([(3, 1), (23, 1), (2939, 1), (16631, 1), (7361524796742341989, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_23, prime_twentyOneS_2939, prime_twentyOneS_16631, prime_twentyOneS_7361524796742341989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593670 : Nat.totient 24827604566159267617738593670 = 8512274414484471587507092608 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (180533, 1), (1964627327030773765757, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_5, prime_twentyOneS_7, prime_twentyOneS_180533, prime_twentyOneS_1964627327030773765757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593671 : Nat.totient 24827604566159267617738593671 = 24470577432635330388196214784 := by
  rw [← show ((([(73, 1), (1447, 1), (1431848177, 1), (164152105477033, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_73, prime_twentyOneS_1447, prime_twentyOneS_1431848177, prime_twentyOneS_164152105477033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593672 : Nat.totient 24827604566159267617738593672 = 8275868188719755872579531200 := by
  rw [← show ((([(2, 3), (3, 2), (344827841196656494690813801, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_344827841196656494690813801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593673 : Nat.totient 24827604566159267617738593673 = 24827603588577095595425495248 := by
  rw [← show ((([(25396949, 1), (977582172022287701477, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_25396949, prime_twentyOneS_977582172022287701477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593674 : Nat.totient 24827604566159267617738593674 = 12078212785810647055054207488 := by
  rw [← show ((([(2, 1), (37, 1), (148517, 1), (8588915177, 1), (263019905989, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_37, prime_twentyOneS_148517, prime_twentyOneS_8588915177, prime_twentyOneS_263019905989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593675 : Nat.totient 24827604566159267617738593675 = 13241389101951609396127249920 := by
  rw [← show ((([(3, 1), (5, 2), (331034727548790234903181249, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_5, prime_twentyOneS_331034727548790234903181249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593676 : Nat.totient 24827604566159267617738593676 = 11754296623414937213821153152 := by
  rw [← show ((([(2, 2), (19, 1), (1913, 1), (151072934563, 1), (1130367316979, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_19, prime_twentyOneS_1913, prime_twentyOneS_151072934563, prime_twentyOneS_1130367316979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593677 : Nat.totient 24827604566159267617738593677 = 19342013232909419731009543680 := by
  rw [← show ((([(7, 1), (11, 1), (4637, 1), (2076644077, 1), (33484585780649, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_7, prime_twentyOneS_11, prime_twentyOneS_4637, prime_twentyOneS_2076644077, prime_twentyOneS_33484585780649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593678 : Nat.totient 24827604566159267617738593678 = 7639250559633289310005531008 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (620159, 1), (116512763, 1), (4405180062253, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_13, prime_twentyOneS_620159, prime_twentyOneS_116512763, prime_twentyOneS_4405180062253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593679 : Nat.totient 24827604566159267617738593679 = 24827524908037025170372522776 := by
  rw [← show ((([(311677, 1), (79658122242447365759227, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_311677, prime_twentyOneS_79658122242447365759227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593680 : Nat.totient 24827604566159267617738593680 = 9931041804113849118244966400 := by
  rw [← show ((([(2, 4), (5, 1), (444344741, 1), (698433059832232481, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_5, prime_twentyOneS_444344741, prime_twentyOneS_698433059832232481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593681 : Nat.totient 24827604566159267617738593681 = 16499394545387446174662842112 := by
  rw [← show ((([(3, 4), (317, 1), (128749, 1), (7510116500595532297, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_317, prime_twentyOneS_128749, prime_twentyOneS_7510116500595532297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593682 : Nat.totient 24827604566159267617738593682 = 12084448324945697634560901120 := by
  rw [← show ((([(2, 1), (41, 1), (673, 1), (1409, 1), (2035447019, 1), (156868270147, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_41, prime_twentyOneS_673, prime_twentyOneS_1409, prime_twentyOneS_2035447019, prime_twentyOneS_156868270147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593683 : Nat.totient 24827604566159267617738593683 = 24702824087846956725363477216 := by
  rw [← show ((([(199, 1), (1325663, 1), (2162504447, 1), (43520271797, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_199, prime_twentyOneS_1325663, prime_twentyOneS_2162504447, prime_twentyOneS_43520271797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593684 : Nat.totient 24827604566159267617738593684 = 7093600965708594895951147008 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_7, prime_twentyOneS_20930737, prime_twentyOneS_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593685 : Nat.totient 24827604566159267617738593685 = 18693725790990507382767882240 := by
  rw [← show ((([(5, 1), (17, 1), (292089465484226677855748161, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_5, prime_twentyOneS_17, prime_twentyOneS_292089465484226677855748161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593686 : Nat.totient 24827604566159267617738593686 = 12050722017158706423829728000 := by
  rw [← show ((([(2, 1), (43, 1), (163, 1), (729338251, 1), (2428397475886177, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_43, prime_twentyOneS_163, prime_twentyOneS_729338251, prime_twentyOneS_2428397475886177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593687 : Nat.totient 24827604566159267617738593687 = 15980986847182976857394956800 := by
  rw [← show ((([(3, 1), (29, 1), (285374765128267443882052801, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_29, prime_twentyOneS_285374765128267443882052801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593688 : Nat.totient 24827604566159267617738593688 = 11272065235769568260885849280 := by
  rw [← show ((([(2, 3), (11, 2), (859, 1), (156823, 1), (190395439210967063, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_11, prime_twentyOneS_859, prime_twentyOneS_156823, prime_twentyOneS_190395439210967063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593689 : Nat.totient 24827604566159267617738593689 = 24827586004754889634847380224 := by
  rw [← show ((([(1337593, 1), (18561404377982889875873, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_1337593, prime_twentyOneS_18561404377982889875873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593690 : Nat.totient 24827604566159267617738593690 = 6614197304115180748408974816 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (1019, 1), (270718619192664568942739, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_5, prime_twentyOneS_1019, prime_twentyOneS_270718619192664568942739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593691 : Nat.totient 24827604566159267617738593691 = 19643818997400739214034931200 := by
  rw [← show ((([(7, 1), (13, 1), (272830819408343600194929601, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_7, prime_twentyOneS_13, prime_twentyOneS_272830819408343600194929601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593692 : Nat.totient 24827604566159267617738593692 = 11867579803336061374235787264 := by
  rw [← show ((([(2, 2), (23, 1), (2393, 1), (8887, 1), (69767, 1), (489449, 1), (371613617, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_23, prime_twentyOneS_2393, prime_twentyOneS_8887, prime_twentyOneS_69767, prime_twentyOneS_489449, prime_twentyOneS_371613617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593693 : Nat.totient 24827604566159267617738593693 = 15947830978898188172094259200 := by
  rw [← show ((([(3, 1), (31, 1), (257, 1), (2099, 1), (319919, 1), (20354891, 1), (75997183, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_31, prime_twentyOneS_257, prime_twentyOneS_2099, prime_twentyOneS_319919, prime_twentyOneS_20354891, prime_twentyOneS_75997183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593694 : Nat.totient 24827604566159267617738593694 = 12037823783027962351145376480 := by
  rw [← show ((([(2, 1), (47, 1), (109, 1), (30859, 1), (78523313892481538671, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_47, prime_twentyOneS_109, prime_twentyOneS_30859, prime_twentyOneS_78523313892481538671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593695 : Nat.totient 24827604566159267617738593695 = 18755319576630173015499980544 := by
  rw [← show ((([(5, 1), (19, 1), (313, 1), (14723, 1), (56711425617038138819, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593695 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_5, prime_twentyOneS_19, prime_twentyOneS_313, prime_twentyOneS_14723, prime_twentyOneS_56711425617038138819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593696 : Nat.totient 24827604566159267617738593696 = 8274160930018441564353423360 := by
  rw [← show ((([(2, 5), (3, 1), (5821, 1), (28979, 1), (1533142745943043289, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593696 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_3, prime_twentyOneS_5821, prime_twentyOneS_28979, prime_twentyOneS_1533142745943043289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593697 : Nat.totient 24827604566159267617738593697 = 24816910494731232856098546192 := by
  rw [← show ((([(2447, 1), (45293, 1), (224011215736290276907, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593697 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2447, prime_twentyOneS_45293, prime_twentyOneS_224011215736290276907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593698 : Nat.totient 24827604566159267617738593698 = 10640347473181682443077878400 := by
  rw [← show ((([(2, 1), (7, 2), (339389, 1), (545911, 1), (2940799, 1), (464968781, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593698 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_2, prime_twentyOneS_7, prime_twentyOneS_339389, prime_twentyOneS_545911, prime_twentyOneS_2940799, prime_twentyOneS_464968781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyOneS_24827604566159267617738593699 : Nat.totient 24827604566159267617738593699 = 15047032127575410186411712320 := by
  rw [← show ((([(3, 2), (11, 1), (15959533, 1), (15713735765743224997, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159267617738593699 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyOneS_3, prime_twentyOneS_11, prime_twentyOneS_15959533, prime_twentyOneS_15713735765743224997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64TwentyOneS : certifiedKill 1 24827604566159267617738593599 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_twentyOneS_24827604566159267617738593600, phi_twentyOneS_24827604566159267617738593601, phi_twentyOneS_24827604566159267617738593602,
    phi_twentyOneS_24827604566159267617738593603, phi_twentyOneS_24827604566159267617738593604, phi_twentyOneS_24827604566159267617738593605,
    phi_twentyOneS_24827604566159267617738593606, phi_twentyOneS_24827604566159267617738593607, phi_twentyOneS_24827604566159267617738593608,
    phi_twentyOneS_24827604566159267617738593609, phi_twentyOneS_24827604566159267617738593610, phi_twentyOneS_24827604566159267617738593611,
    phi_twentyOneS_24827604566159267617738593612, phi_twentyOneS_24827604566159267617738593613, phi_twentyOneS_24827604566159267617738593614,
    phi_twentyOneS_24827604566159267617738593615, phi_twentyOneS_24827604566159267617738593616, phi_twentyOneS_24827604566159267617738593617,
    phi_twentyOneS_24827604566159267617738593618, phi_twentyOneS_24827604566159267617738593619, phi_twentyOneS_24827604566159267617738593620,
    phi_twentyOneS_24827604566159267617738593621, phi_twentyOneS_24827604566159267617738593622, phi_twentyOneS_24827604566159267617738593623,
    phi_twentyOneS_24827604566159267617738593624, phi_twentyOneS_24827604566159267617738593625, phi_twentyOneS_24827604566159267617738593626,
    phi_twentyOneS_24827604566159267617738593627, phi_twentyOneS_24827604566159267617738593628, phi_twentyOneS_24827604566159267617738593629,
    phi_twentyOneS_24827604566159267617738593630, phi_twentyOneS_24827604566159267617738593631, phi_twentyOneS_24827604566159267617738593632,
    phi_twentyOneS_24827604566159267617738593633, phi_twentyOneS_24827604566159267617738593634, phi_twentyOneS_24827604566159267617738593635,
    phi_twentyOneS_24827604566159267617738593636, phi_twentyOneS_24827604566159267617738593637, phi_twentyOneS_24827604566159267617738593638,
    phi_twentyOneS_24827604566159267617738593639, phi_twentyOneS_24827604566159267617738593640, phi_twentyOneS_24827604566159267617738593641,
    phi_twentyOneS_24827604566159267617738593642, phi_twentyOneS_24827604566159267617738593643, phi_twentyOneS_24827604566159267617738593644,
    phi_twentyOneS_24827604566159267617738593645, phi_twentyOneS_24827604566159267617738593646, phi_twentyOneS_24827604566159267617738593647,
    phi_twentyOneS_24827604566159267617738593648, phi_twentyOneS_24827604566159267617738593649, phi_twentyOneS_24827604566159267617738593650,
    phi_twentyOneS_24827604566159267617738593651, phi_twentyOneS_24827604566159267617738593652, phi_twentyOneS_24827604566159267617738593653,
    phi_twentyOneS_24827604566159267617738593654, phi_twentyOneS_24827604566159267617738593655, phi_twentyOneS_24827604566159267617738593656,
    phi_twentyOneS_24827604566159267617738593657, phi_twentyOneS_24827604566159267617738593658, phi_twentyOneS_24827604566159267617738593659,
    phi_twentyOneS_24827604566159267617738593660, phi_twentyOneS_24827604566159267617738593661, phi_twentyOneS_24827604566159267617738593662,
    phi_twentyOneS_24827604566159267617738593663, phi_twentyOneS_24827604566159267617738593664, phi_twentyOneS_24827604566159267617738593665,
    phi_twentyOneS_24827604566159267617738593666, phi_twentyOneS_24827604566159267617738593667, phi_twentyOneS_24827604566159267617738593668,
    phi_twentyOneS_24827604566159267617738593669, phi_twentyOneS_24827604566159267617738593670, phi_twentyOneS_24827604566159267617738593671,
    phi_twentyOneS_24827604566159267617738593672, phi_twentyOneS_24827604566159267617738593673, phi_twentyOneS_24827604566159267617738593674,
    phi_twentyOneS_24827604566159267617738593675, phi_twentyOneS_24827604566159267617738593676, phi_twentyOneS_24827604566159267617738593677,
    phi_twentyOneS_24827604566159267617738593678, phi_twentyOneS_24827604566159267617738593679, phi_twentyOneS_24827604566159267617738593680,
    phi_twentyOneS_24827604566159267617738593681, phi_twentyOneS_24827604566159267617738593682, phi_twentyOneS_24827604566159267617738593683,
    phi_twentyOneS_24827604566159267617738593684, phi_twentyOneS_24827604566159267617738593685, phi_twentyOneS_24827604566159267617738593686,
    phi_twentyOneS_24827604566159267617738593687, phi_twentyOneS_24827604566159267617738593688, phi_twentyOneS_24827604566159267617738593689,
    phi_twentyOneS_24827604566159267617738593690, phi_twentyOneS_24827604566159267617738593691, phi_twentyOneS_24827604566159267617738593692,
    phi_twentyOneS_24827604566159267617738593693, phi_twentyOneS_24827604566159267617738593694, phi_twentyOneS_24827604566159267617738593695,
    phi_twentyOneS_24827604566159267617738593696, phi_twentyOneS_24827604566159267617738593697, phi_twentyOneS_24827604566159267617738593698,
    phi_twentyOneS_24827604566159267617738593699]

end TotientTailPeriodKiller
end Erdos249257
