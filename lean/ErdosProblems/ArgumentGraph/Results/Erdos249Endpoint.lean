-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.ArgumentGraph.Results.Erdos249

/-!
# Erdős #249: the good-base gap gives the irrationality with no further input

`Results/Erdos249Route.lean` reaches the irrationality of `∑ φ(n)/2^n` from a first-harmonic
gap on the good bases by way of `DTWPivotResidualDecorrelation`. That demand bounds the fibre
means, so the route needs the prime number theorem. The irrationality consumer
(`irrational_totient_series_of_certificate_supply`) needs less: for every `h ≥ 1`, one certified
kill beyond every threshold. `exists_certifiedKill_of_first_harmonic_gap_subset` finds one in any
nonempty set of bases below `2X` whose average first cosine is at most `9/10`, at a depth with
room, so that is the whole requirement (`irrational_totient_series_of_support_gap`).

The good bases at the minimal depth, with `s = 26` and `η = 1/1000`, are such a set as soon as
their first harmonic has real part at most `603X/1000`. The good, bad and non-supplier bases
partition `[X, 2X)` (`card_pivotGoodBases_add_card_pivotBadBases`,
`card_pivotSupplierBases_add_card_pivotNonSupplierBases`); for all large `X` there are fewer than
`X/100` bad bases (Chebyshev's bound) and fewer than `8X/25` non-supplier bases
(`prop_dickman`), so more than `67X/100` good ones (`eventually_card_pivotGoodBases_gt`), and
`603/1000 = 9/10 · 67/100`. Hence `irrational_totient_series_of_goodBase_gap`: a cofinal
good-base gap at `603X/1000` for every `h ≥ 1` gives the irrationality, with no hypothesis
besides the gap. The route of `Results/Erdos249Route.lean` asks for the prime number theorem
and the gap at `11X/20`, which is smaller than `603X/1000`.

Two finite forms of the same barrier are stated for later suppliers: with nonnegative weights,
a weighted average first cosine at most `9/10` gives a certified kill of positive weight
(`exists_certifiedKill_of_weighted_first_harmonic_gap`), and the saving below `9/10` counts
certified kills (`card_certifiedKill_ge`). The pointwise barrier they use is the singleton case
of the subset theorem (`nine_tenths_lt_windowFirstCos_of_not_certifiedKill`).
-/

open Filter Finset

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor

/-- **The certificate interface of the first-harmonic family.** For every `h ≥ 1` and every
threshold `A`, some nonempty set of bases in `[A, 2X)` whose average first cosine is at most
`9/10`, at a depth `L` with room, gives the irrationality of `∑ φ(n)/2^n`. -/
theorem irrational_totient_series_of_support_gap
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X L : ℕ, ∃ T : Finset ℕ,
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧ T.Nonempty ∧ (∀ N ∈ T, A ≤ N ∧ N < 2 * X) ∧
      (∑ N ∈ T, windowFirstCos h N L) ≤ (9 / 10 : ℝ) * T.card) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_certificate_supply
  intro h hh A
  obtain ⟨X, L, T, hroom, hne, hT, hcos⟩ := hgap h hh A
  obtain ⟨N, hN, hkill⟩ :=
    exists_certifiedKill_of_first_harmonic_gap_subset T (fun N hN => (hT N hN).2) hne hroom hcos
  exact ⟨N, (hT N hN).1, L, hkill⟩

/-- The good and bad bases partition the supplier bases. -/
theorem card_pivotGoodBases_add_card_pivotBadBases (X L s : ℕ) (η : ℝ) :
    (pivotGoodBases X L s η).card + (pivotBadBases X L s η).card
      = (pivotSupplierBases X L s).card := by
  unfold pivotGoodBases pivotBadBases
  exact Finset.card_filter_add_card_filter_not _

/-- The supplier and non-supplier bases partition `[X, 2X)`. -/
theorem card_pivotSupplierBases_add_card_pivotNonSupplierBases (X L s : ℕ) :
    (pivotSupplierBases X L s).card + (pivotNonSupplierBases X L s).card = X := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.Ico X (2 * X)) (pivotSupplier X L s)
  rw [Nat.card_Ico] at hsplit
  unfold pivotSupplierBases pivotNonSupplierBases
  omega

/-- At the minimal depth, with `s = 26` and `η = 1/1000`, more than `67X/100` of the bases in
`[X, 2X)` are good, for all large `X`: Chebyshev's bound leaves fewer than `X/100` bad bases and
`prop_dickman` fewer than `8X/25` non-supplier bases. -/
theorem eventually_card_pivotGoodBases_gt (h : ℕ) :
    ∀ᶠ X : ℕ in atTop, (67 / 100 : ℝ) * X
      < ((pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).card : ℝ) := by
  filter_upwards [excluded_budget_one_thousandth_of_chebyshev h 26,
    (prop_dickman h 26).2.2.2.2.2] with X hbad hnon
  have hb := card_pivotBadBases_le_of_count h X hbad.1
  have hn : ((pivotNonSupplierBases X (minimalDepth h 26 X) 26).card : ℝ) < 8 / 25 * X := by
    simpa [filter_not_mem_pivotSupplierBases] using hnon.2
  have hgb := card_pivotGoodBases_add_card_pivotBadBases X (minimalDepth h 26 X) 26
    (1 / 1000 : ℝ)
  have hsn := card_pivotSupplierBases_add_card_pivotNonSupplierBases X (minimalDepth h 26 X) 26
  have hnat : (pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).card
      + (pivotBadBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).card
      + (pivotNonSupplierBases X (minimalDepth h 26 X) 26).card = X := by
    omega
  have hsum : ((pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).card : ℝ)
      + ((pivotBadBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).card : ℝ)
      + ((pivotNonSupplierBases X (minimalDepth h 26 X) 26).card : ℝ) = X := by
    exact_mod_cast hnat
  linarith

/-- **The irrationality of `∑ φ(n) / 2 ^ n` from a first-harmonic gap on the good bases, with no
further input**: for every `h ≥ 1`, arbitrarily large `X` at which the real part of the first
harmonic summed over the good bases (minimal depth, `s = 26`, `η = 1/1000`) is at most
`603X/1000`. -/
theorem irrational_totient_series_of_goodBase_gap
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        windowFirstExp h N (minimalDepth h 26 X)).re ≤ (603 / 1000 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_support_gap fun h hh A => ?_
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp (eventually_card_pivotGoodBases_gt h)
  obtain ⟨X, hX, hg⟩ := hgap h hh (max A A₁)
  simp only [max_le_iff] at hX
  obtain ⟨⟨hAX, hA₁X⟩, hX1⟩ := hX
  have hcard := hA₁ X hA₁X
  have hX0 : 0 < X := hX1
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX0
  have hadm : h ≤ minimalDepth h 26 X - 26 ∧
      16 * (2 * X + h + minimalDepth h 26 X + 2) ≤ 2 ^ minimalDepth h 26 X :=
    ((prop_dickman h 26).1 X).1
  refine ⟨X, minimalDepth h 26 X, pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
    hadm.2, ?_, ?_, ?_⟩
  · rw [← Finset.card_pos]
    have hpos : (0 : ℝ) < ((pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).card : ℝ) := by
      linarith
    exact_mod_cast hpos
  · intro N hN
    simp only [pivotGoodBases, pivotSupplierBases, Finset.mem_filter, Finset.mem_Ico] at hN
    exact ⟨le_trans hAX hN.1.1.1, hN.1.1.2⟩
  · have hre : (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        windowFirstExp h N (minimalDepth h 26 X)).re
        = ∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
          windowFirstCos h N (minimalDepth h 26 X) := by
      simp
    linarith [hre]

/-- The pointwise barrier: at a depth with room, a base below `2X` without a certified kill has
first cosine above `9/10`. It is the singleton case of
`exists_certifiedKill_of_first_harmonic_gap_subset`. -/
theorem nine_tenths_lt_windowFirstCos_of_not_certifiedKill {h X L N : ℕ} (hN : N < 2 * X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L) (hnot : ¬ certifiedKill h N L) :
    (9 / 10 : ℝ) < windowFirstCos h N L := by
  by_contra hle
  have hle' : windowFirstCos h N L ≤ 9 / 10 := not_lt.mp hle
  obtain ⟨M, hM, hk⟩ := exists_certifiedKill_of_first_harmonic_gap_subset {N}
    (by simpa using hN) (Finset.singleton_nonempty N) hroom (by simpa using hle')
  rw [Finset.mem_singleton] at hM
  rw [hM] at hk
  exact hnot hk

/-- **The weighted barrier.** With nonnegative weights `a` of positive total on a set of bases
below `2X`, a weighted average first cosine at most `9/10`, at a depth with room, gives a
certified kill at a base of positive weight. -/
theorem exists_certifiedKill_of_weighted_first_harmonic_gap {h X L : ℕ} (T : Finset ℕ)
    (a : ℕ → ℝ) (ha : ∀ N ∈ T, 0 ≤ a N) (hTlt : ∀ N ∈ T, N < 2 * X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L) (hpos : 0 < ∑ N ∈ T, a N)
    (hgap : (∑ N ∈ T, a N * windowFirstCos h N L) ≤ (9 / 10 : ℝ) * ∑ N ∈ T, a N) :
    ∃ N ∈ T, 0 < a N ∧ certifiedKill h N L := by
  by_contra hnone
  have hnot : ∀ N ∈ T, 0 < a N → ¬ certifiedKill h N L :=
    fun N hN hp hk => hnone ⟨N, hN, hp, hk⟩
  obtain ⟨M, hM, hMpos⟩ : ∃ M ∈ T, 0 < a M := by
    by_contra hall
    have hle : ∑ N ∈ T, a N ≤ 0 := Finset.sum_nonpos fun N hN => by
      by_contra hlt
      exact hall ⟨N, hN, not_le.mp hlt⟩
    linarith
  have hlt : (∑ N ∈ T, a N * (9 / 10 : ℝ)) < ∑ N ∈ T, a N * windowFirstCos h N L := by
    apply Finset.sum_lt_sum
    · intro N hN
      rcases (ha N hN).lt_or_eq with hp | h0
      · exact le_of_lt (mul_lt_mul_of_pos_left
          (nine_tenths_lt_windowFirstCos_of_not_certifiedKill (hTlt N hN) hroom
            (hnot N hN hp)) hp)
      · rw [← h0]
        simp
    · exact ⟨M, hM, mul_lt_mul_of_pos_left
        (nine_tenths_lt_windowFirstCos_of_not_certifiedKill (hTlt M hM) hroom
          (hnot M hM hMpos)) hMpos⟩
  rw [← Finset.sum_mul] at hlt
  linarith

/-- **Counting certified kills.** On a set of bases below `2X`, at a depth with room, the saving
of the first cosines below `9/10` is at most `19/10` times the number of certified kills: a
base without a kill has first cosine above `9/10`, and every first cosine is at least `-1`. -/
theorem card_certifiedKill_ge {h X L : ℕ} (T : Finset ℕ) (hTlt : ∀ N ∈ T, N < 2 * X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L) :
    (9 / 10 : ℝ) * T.card - ∑ N ∈ T, windowFirstCos h N L
      ≤ (19 / 10 : ℝ) * ((T.filter fun N => certifiedKill h N L).card : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not T (fun N => certifiedKill h N L)
    (fun N => windowFirstCos h N L)
  have hcard := Finset.card_filter_add_card_filter_not (s := T) (fun N => certifiedKill h N L)
  have hcardR : ((T.filter fun N => certifiedKill h N L).card : ℝ)
      + ((T.filter fun N => ¬ certifiedKill h N L).card : ℝ) = T.card := by
    exact_mod_cast hcard
  have hyes := Finset.card_nsmul_le_sum (T.filter fun N => certifiedKill h N L)
    (fun N => windowFirstCos h N L) (-1) (fun N _ => by
      unfold windowFirstCos
      exact Real.neg_one_le_cos _)
  have hno := Finset.card_nsmul_le_sum (T.filter fun N => ¬ certifiedKill h N L)
    (fun N => windowFirstCos h N L) (9 / 10) (fun N hN => le_of_lt
      (nine_tenths_lt_windowFirstCos_of_not_certifiedKill (hTlt N (Finset.mem_filter.mp hN).1)
        hroom (Finset.mem_filter.mp hN).2))
  rw [nsmul_eq_mul] at hyes hno
  linarith

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_support_gap
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.card_pivotGoodBases_add_card_pivotBadBases
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.card_pivotSupplierBases_add_card_pivotNonSupplierBases
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.eventually_card_pivotGoodBases_gt
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.nine_tenths_lt_windowFirstCos_of_not_certifiedKill
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_weighted_first_harmonic_gap
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.card_certifiedKill_ge
