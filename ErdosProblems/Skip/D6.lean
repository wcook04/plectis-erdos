/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleB2
import Erdos249257.HalfCylinderLargestSkipInduction

/-!
# Skip D6: the exact skip dichotomy, and where it does and does not hold

`ErdosProblems/Lift/AngleB2.lean` proves a contradiction from the all-right
tail, the landing equation, and one further hypothesis:

  `hcof : ∀ s, D+1 ≤ s → s < D+4 → cofRanks s ⊆ seamWordSupport (seamGreedyWord s)`

and records the measured fact that `hcof` is *not* unconditionally true: the
cofactor ranks are selected by the integer seam greedy roughly half the time.

Direct evaluation also finds no `s ∈ [5,102]` with
`Recon257.seamExcess s = 2`.  Thus the AngleB2 connection is unreachable on
that audited range.  The unconditional skip lemmas and cofinal implications
below remain valid, but none resolves Erdős #257.

This file settles what happens on the other side of that coin.  The governing
observation is arithmetic and completely elementary:

* `(2s+1)/3` and `2(s+1)/3` — the cofactor-`3` ranks — satisfy `3 * d > 2 * s`,
  so a *failure* of selection at either of them is a **late** skipped rank;
* `(s+1)/2` — the cofactor-`4` rank — satisfies `3 * d ≤ 2 * s` for every
  `s ≥ 3`, so a failure of selection there says nothing about lateness.

`cofRanks_late_or_half` proves exactly this trichotomy collapse, and
`halfCofactor_not_late` is the sharp negative that isolates `(s+1)/2` as the
*only* obstruction to the dichotomy in its naive form.

The dichotomy therefore holds in the following exact form
(`cofRanks_subset_or_largestSkipLateAt`):

  `cofRanks s ⊆ seamWordSupport (seamGreedyWord s) ∨ LargestSkipLateAt s`

**granted only** the single membership `(s+1)/2 ∈ seamWordSupport (...)` when
that rank is present.  For the cofactor-`3` ranks alone
(`cofRanksLate_subset_or_largestSkipLateAt`) the dichotomy is unconditional.

## What the positive branch actually needs

`Erdos249257.half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket`
consumes `LargestSkipLateStepSocket`, a *step* hypothesis.  Inspecting its
proof, the socket is used only to produce `∀ s ≥ 14, LargestSkipLateAt s`.  We
therefore cut out the socket entirely and expose the genuinely minimal input:

* `half_mem_of_unboundedSkip` — an unbounded supply of skipped ranks, at any
  rows whatsoever, already gives `1/2 ∈ mersenneAchievementSet`;
* `half_mem_of_forall_lateSkip`, `half_mem_of_forall_largestSkipLateAt` — the
  late and largest-false-rank specialisations;
* `half_mem_of_cofRanksLate_cofinal_miss` — **if the cofactor-`3` ranks fail to
  be selected at infinitely many rows, then `1/2 ∈ mersenneAchievementSet`.**

That last theorem is the positive half of the dichotomy at programme level.
Pairing it with the negation gives the unconditional global statement
`half_mem_or_eventually_late_selected`:

  `1/2 ∈ mersenneAchievementSet`  ∨  every late rank at every large row is
  selected.

and hence `half_mem_or_eventually_allRight_landingExcess_two_impossible`: either
the positive branch fires, or AngleB2's `hcof` needs *only* the even cofactor
`(s+1)/2` for every sufficiently large class `D`.

## What is measured, and what remains

Direct computation of `integerGreedyBits (seamWeights s) (seamSubsetTarget s)`
for **every** `s` in `[5, 20000]` (19987 rows with `s ≥ 14`) gives the following
raw counts.

Selection of the cofactor ranks — the rate is `1/2` and does not drift:

* `(2s+1)/3`, over the `6662` rows with `s ≡ 1 (mod 3)`: selected `3306`
  times, `0.4962`;
* `2(s+1)/3`, over the `6663` rows with `s ≡ 2 (mod 3)`: selected `3348`
  times, `0.5025`;
* `(s+1)/2`, over the `9993` odd rows: selected `5001` times, `0.5005`;
* `cofRanks s ⊆ seamWordSupport (seamGreedyWord s)` at `10000` of `19987`
  rows, `0.5003`.  Window rates over `[14,200)`, `[200,1000)`, …,
  `[17000,20001)` stay inside `[0.44, 0.52]` with no trend.

Lateness — the decisive measurement:

* `LargestSkipLateAt s` holds at **19987 of 19987** rows `s ∈ [14, 20000]`.
  There is not one exception.
* The margin is never tight: `min (3 * d - 2 * s) = 4`, attained only at
  `s = 19`; the number of false ranks in the late zone is at least `160` for
  every `s ≥ 1000`.
* The largest false rank sits just under the top: `(s-1) - d` has a geometric
  distribution (`9968` rows with `d = s-1`, `5044` with `d = s-2`, …) and
  never exceeds `12` over the whole range (attained at `s = 1148, 16012`).

The question this angle was asked — *among non-selected cofactor instances,
what fraction are the largest false rank?* — has the answer **zero**.  Over all
`6671` non-selected cofactor-`3` instances, the rank is the largest false rank
`0` times; the smallest witness is `s = 14`, where `2(s+1)/3 = 10` is skipped
while the largest false rank is `13`.  That is not a counterexample to the
dichotomy: `LargestSkipLateAt` asks only that the largest false rank *be* late,
and a skipped `(2s+1)/3` or `2(s+1)/3` is itself late, which forces the largest
false rank to be at least as large.  `largestSkipLateAt_of_lateSkip` turns that
into a proof, so on the late cofactor ranks the implication holds `6671/6671`
— as a theorem, not as a statistic.

Consequence for `AngleB2`: over the classes `D ∈ [60, 19990)`, the full
hypothesis `hcof` is certified on all three rows `D+1, D+2, D+3` for only
`1895/19930 = 0.095` of classes, and its cofactor-`3` part for
`5032/19930 = 0.252`.  For the other `14898/19930 = 0.748` of classes,
`allRight_landingExcess_two_lateSkip` delivers a late largest false rank inside
`{D+1, D+2, D+3}` instead.

Stronger still, and worth stating plainly: `AngleB2`'s *other* hypothesis
`hright` is measurably false everywhere in range.  By
`seamGreedyWord_succ_eq_extend_true_iff_terminal_true`, `hright` at `D` says
exactly that `t - 1 ∈ seamWordSupport (seamGreedyWord t)` for every `t ≥ D+2`,
i.e. that the largest false rank of row `t` is never `t-1`.  **MEASURED:** `9970` of the
rows `t ≤ 20000` have largest false rank exactly `t-1`, and for **every**
`D ∈ [60, 19960)` such a `t` occurs with `t - D ≤ 14` (the worst delay is `14`,
at `D = 1135`).  So on the computed range `hright` has no models at all — the
seven phases `D = 101, 122, 164, 314, 545, 629, 1112` singled out in
`AngleB2`'s remark 2 are refuted at `t = 105, 124, 166, 316, 547, 631, 1114`
respectively.  Those seven refutations are measurements, not theorems in this
file.  In particular `not_rightTail_of_largestSkipLateAt` does not certify the
listed pairs: its scale premise fails for them (for example
`3 * 102 ≤ 2 * 105` is false).

So the disjunct that actually fires, at every measured row, is
`LargestSkipLateAt s`.  What is *not* proved here — and is exactly the whole
remaining content of the `1/2`-membership question — is that it fires at
infinitely many rows.  Nothing below assumes it.
-/

namespace Erdos249257

namespace SkipD6

open HalfCylinderIntegerGreedy
open Set Filter

/-! ## One late skipped rank produces a late largest false rank -/

/-- If any rank strictly beyond two thirds of the row is skipped, then the
row's *largest* false rank is itself beyond two thirds.  This is the whole
content of `LargestSkipLateAt`: it does not ask for the witness to be maximal,
only for one late skip to exist. -/
theorem largestSkipLateAt_of_lateSkip {s d : ℕ}
    (hds : d < s) (hlate : 2 * s < 3 * d)
    (hd : d ∉ seamWordSupport (seamGreedyWord s)) :
    LargestSkipLateAt s := by
  classical
  have hd2 : 2 ≤ d := by omega
  set F : Finset ℕ :=
    (Finset.Ico 2 s).filter (fun e => e ∉ seamWordSupport (seamGreedyWord s))
    with hF
  have hdF : d ∈ F := by
    rw [hF]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hd2, hds⟩, hd⟩
  have hne : F.Nonempty := ⟨d, hdF⟩
  have hmF : F.max' hne ∈ F := F.max'_mem hne
  have hmdata := Finset.mem_filter.mp hmF
  have hmIco := Finset.mem_Ico.mp hmdata.1
  have hdm : d ≤ F.max' hne := Finset.le_max' F d hdF
  refine ⟨F.max' hne, ⟨hmIco.1, hmIco.2, hmdata.2, ?_⟩, by omega⟩
  intro e hme hes
  by_contra hnot
  have heF : e ∈ F := by
    rw [hF]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hes⟩, hnot⟩
  have := Finset.le_max' F e heF
  omega

/-- Conversely, a late largest false rank is in particular a late skip. -/
theorem lateSkip_of_largestSkipLateAt {s : ℕ} (h : LargestSkipLateAt s) :
    ∃ d : ℕ, d < s ∧ 2 * s < 3 * d ∧
      d ∉ seamWordSupport (seamGreedyWord s) := by
  obtain ⟨d, hmax, hmargin⟩ := h
  exact ⟨d, hmax.2.1, hmargin, hmax.2.2.1⟩

/-! ## The minimal input for the positive branch -/

/-- An unbounded supply of skipped seam ranks, at arbitrary rows, is already a
`SeamGreedyUnboundedSkippedRanksAlong` datum. -/
theorem seamGreedyUnboundedSkippedRanksAlong_of_unboundedSkip
    (S D : ℕ → ℕ)
    (hND : ∀ N : ℕ, N ≤ D N) (hDS : ∀ N : ℕ, D N < S N)
    (hmiss : ∀ N : ℕ, D N ∉ seamWordSupport (seamGreedyWord (S N))) :
    SeamGreedyUnboundedSkippedRanksAlong (fun j => S (j + 2)) := by
  have hidx : ∀ j : ℕ, D (j + 2) - 2 < S (j + 2) - 2 := by
    intro j
    have h1 := hND (j + 2)
    have h2 := hDS (j + 2)
    omega
  refine ⟨fun j => ⟨D (j + 2) - 2, hidx j⟩, ?_, ?_, ?_⟩
  · refine tendsto_atTop_mono (fun j => ?_) tendsto_id
    have h1 := hND (j + 2)
    have h2 := hDS (j + 2)
    show j ≤ S (j + 2)
    omega
  · refine tendsto_atTop_mono (fun j => ?_) tendsto_id
    have h1 := hND (j + 2)
    show j ≤ D (j + 2) - 2 + 2
    omega
  · intro j
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    refine hmiss (j + 2) (mem_seamWordSupport_iff.mpr
      ⟨⟨D (j + 2) - 2, hidx j⟩, htrue, ?_⟩)
    have h1 := hND (j + 2)
    show D (j + 2) = D (j + 2) - 2 + 2
    omega

/-- **The genuinely minimal producer.**  Skipped seam ranks of unbounded size,
at any rows at all, give the `#257` half-membership endpoint.  No step socket,
no lateness, no maximality. -/
theorem half_mem_of_unboundedSkip
    (h : ∀ N : ℕ, ∃ s d : ℕ, N ≤ d ∧ d < s ∧
      d ∉ seamWordSupport (seamGreedyWord s)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  choose S D hND hDS hmiss using h
  exact half_mem_mersenneAchievementSet_of_unboundedSkippedRanks _
    (seamGreedyUnboundedSkippedRanksAlong_of_unboundedSkip S D hND hDS hmiss)

/-- A late skip at every row from `14` on gives the endpoint. -/
theorem half_mem_of_forall_lateSkip
    (h : ∀ s : ℕ, 14 ≤ s → ∃ d : ℕ, d < s ∧ 2 * s < 3 * d ∧
      d ∉ seamWordSupport (seamGreedyWord s)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_of_unboundedSkip
  intro N
  obtain ⟨d, hds, hlate, hmiss⟩ := h (max 14 (3 * N + 3)) (le_max_left _ _)
  have hge : 3 * N + 3 ≤ max 14 (3 * N + 3) := le_max_right _ _
  exact ⟨max 14 (3 * N + 3), d, by omega, hds, hmiss⟩

/-- `LargestSkipLateAt` on every row from `14` on already removes the step
socket of `HalfCylinderLargestSkipInduction`: the socket was only ever used to
produce this pointwise statement. -/
theorem half_mem_of_forall_largestSkipLateAt
    (hlate : ∀ s : ℕ, 14 ≤ s → LargestSkipLateAt s) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_of_forall_lateSkip
  intro s hs
  exact lateSkip_of_largestSkipLateAt (hlate s hs)

/-- The socket route factors through the pointwise route. -/
theorem half_mem_of_largestSkipLateStepSocket
    (hstep : LargestSkipLateStepSocket) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_of_forall_largestSkipLateAt
    (fun s hs => largestSkipLateAt_of_stepSocket hstep s hs)

/-! ## The cofactor ranks split by lateness -/

/-- The cofactor ranks of `AngleB2` that lie in the late zone `2 * s < 3 * d`. -/
def cofRanksLate (s : ℕ) : Finset ℕ :=
  (AngleB2.cofRanks s).filter (fun d => 2 * s < 3 * d)

theorem mem_cofRanksLate_iff {s d : ℕ} :
    d ∈ cofRanksLate s ↔ d ∈ AngleB2.cofRanks s ∧ 2 * s < 3 * d :=
  Finset.mem_filter

/-- **The sharp negative.**  The cofactor-`4` rank `(s+1)/2` is never late: it
sits at half the row, and the late zone starts at two thirds.  So a failure of
selection at `(s+1)/2` carries no information about `LargestSkipLateAt`. -/
theorem halfCofactor_not_late (s : ℕ) (hs : 3 ≤ s) :
    ¬ 2 * s < 3 * ((s + 1) / 2) := by
  omega

/-- Consequently `(s+1)/2` is never a member of the late cofactor set. -/
theorem halfCofactor_notMem_cofRanksLate (s : ℕ) (hs : 3 ≤ s) :
    (s + 1) / 2 ∉ cofRanksLate s := by
  intro hmem
  exact halfCofactor_not_late s hs (mem_cofRanksLate_iff.mp hmem).2

/-- The cofactor-`3` ranks are late.  Every cofactor rank is therefore either
late or equal to `(s+1)/2`; there is no third case. -/
theorem cofRanks_late_or_half {s d : ℕ} (hd : d ∈ AngleB2.cofRanks s) :
    2 * s < 3 * d ∨ d = (s + 1) / 2 := by
  unfold AngleB2.cofRanks at hd
  split_ifs at hd with h1 h2 h3 h4 h5 <;>
    simp only [Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty] at hd <;>
    rcases hd with rfl | rfl <;> omega

/-- The late cofactor ranks are exactly the cofactor-`3` ranks: for `s ≥ 3`,
membership in `cofRanksLate` forces the `2s+1` or `2s+2` shape. -/
theorem cofRanksLate_cases {s d : ℕ} (hs : 3 ≤ s) (hd : d ∈ cofRanksLate s) :
    d = (2 * s + 1) / 3 ∨ d = 2 * (s + 1) / 3 := by
  have hmem := mem_cofRanksLate_iff.mp hd
  rcases AngleB2.cofRanks_cases hmem.1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (h ▸ hmem.2) (halfCofactor_not_late s hs)

/-- **The second sharp negative.**  On a third of all rows there is no late
cofactor rank whatsoever: `3` divides neither `2s+1` nor `2s+2` when `3 ∣ s`, so
`cofRanksLate s = ∅` and the unconditional dichotomy has nothing to offer at
those rows.  Since divisors of `2s+1` or `2s+2` exceeding `2s/3` come only from
the cofactor `3` (cofactors `1` and `2` give ranks `≥ s`, cofactor `4` gives
`(s+1)/2`), this is not an artefact of the chosen certificate: it is the
complete list.  The late pulse available to `AngleB2` is therefore
`![0,2,1,0,2,1]` indexed by `s % 6`, against the full `cofFloor` of
`![0,3,1,1,2,2]`; the deficit `![0,1,0,1,0,1]` is exactly the `(s+1)/2`
contribution on the odd rows. -/
theorem cofRanksLate_eq_empty_of_three_dvd (s : ℕ) (hs : 3 ≤ s) (h : s % 3 = 0) :
    cofRanksLate s = ∅ := by
  refine Finset.eq_empty_of_forall_notMem (fun d hd => ?_)
  have hlate := (mem_cofRanksLate_iff.mp hd).2
  rcases cofRanksLate_cases hs hd with rfl | rfl <;> omega

/-! ## The skip dichotomy -/

/-- **The unconditional skip dichotomy.**  At every row `s ≥ 61`, either all
the *late* cofactor ranks are selected by the integer seam greedy — which is
what `AngleB2`'s exclusion ratchet consumes — or the row has a late largest
false rank, which is what the positive `1/2`-membership route consumes. -/
theorem cofRanksLate_subset_or_largestSkipLateAt (s : ℕ) (hs : 61 ≤ s) :
    cofRanksLate s ⊆ seamWordSupport (seamGreedyWord s) ∨ LargestSkipLateAt s := by
  by_cases hsub : cofRanksLate s ⊆ seamWordSupport (seamGreedyWord s)
  · exact Or.inl hsub
  right
  rw [Finset.not_subset] at hsub
  obtain ⟨d, hd, hdnot⟩ := hsub
  have hdata := mem_cofRanksLate_iff.mp hd
  exact largestSkipLateAt_of_lateSkip
    (AngleB2.cofRanks_lt s (by omega) hdata.1) hdata.2 hdnot

/-- **The full dichotomy, with its exact residue.**  The dichotomy over *all*
of `cofRanks s` holds granted the single membership `(s+1)/2 ∈ support`, and
that hypothesis is unavoidable by `halfCofactor_not_late`. -/
theorem cofRanks_subset_or_largestSkipLateAt (s : ℕ) (hs : 61 ≤ s)
    (hhalf : (s + 1) / 2 ∈ AngleB2.cofRanks s →
      (s + 1) / 2 ∈ seamWordSupport (seamGreedyWord s)) :
    AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) ∨
      LargestSkipLateAt s := by
  by_cases hsub : AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)
  · exact Or.inl hsub
  right
  rw [Finset.not_subset] at hsub
  obtain ⟨d, hd, hdnot⟩ := hsub
  rcases cofRanks_late_or_half hd with hlate | rfl
  · exact largestSkipLateAt_of_lateSkip
      (AngleB2.cofRanks_lt s (by omega) hd) hlate hdnot
  · exact absurd (hhalf hd) hdnot

/-! ## Exact complementarity with the all-right tail -/

/-- On an all-right tail from `S`, every rank in `[S, t)` has been appended as a
`true` bit, so the whole block lies in the support. -/
theorem Ico_subset_seamWordSupport_of_rightTail
    {S : ℕ} (hS : 3 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ∀ t : ℕ, S ≤ t → Finset.Ico S t ⊆ seamWordSupport (seamGreedyWord t) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
      intro d hd
      rw [hright t ht, seamWordSupport_extend_true (by omega) (seamGreedyWord t)]
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hd
      rcases Nat.lt_or_ge d t with h | h
      · exact Finset.mem_insert_of_mem (ih (Finset.mem_Ico.mpr ⟨h1, h⟩))
      · have hdt : d = t := by omega
        exact hdt ▸ Finset.mem_insert_self _ _

/-- **The two branches are exclusive.**  An all-right tail from `S` kills
`LargestSkipLateAt` at every row `s` with `3 * S ≤ 2 * s`: the late zone
`(2s/3, s)` is then contained in the appended all-`true` block.  This is why
`AngleB2`'s `hright` and the positive `1/2`-membership route can never both
apply at a large row, and it is the exact reason a late skip is worth as much
as an exclusion. -/
theorem not_largestSkipLateAt_of_rightTail
    {S : ℕ} (hS : 3 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s : ℕ} (hSs : S ≤ s) (hs : 3 * S ≤ 2 * s) :
    ¬ LargestSkipLateAt s := by
  rintro ⟨d, hmax, hlate⟩
  exact hmax.2.2.1
    (Ico_subset_seamWordSupport_of_rightTail hS hright s hSs
      (Finset.mem_Ico.mpr ⟨by omega, hmax.2.1⟩))

/-- Contrapositive, in the form a search consumes: a single late largest false
rank at a row `s ≥ 3 * S / 2` refutes the all-right tail from `S` outright. -/
theorem not_rightTail_of_largestSkipLateAt
    {S s : ℕ} (hS : 3 ≤ S) (hSs : S ≤ s) (hs : 3 * S ≤ 2 * s)
    (hlate : LargestSkipLateAt s) :
    ¬ ∀ t : ℕ, S ≤ t →
      seamGreedyWord (t + 1) = (seamGreedyWord t).extend true := by
  intro hright
  exact not_largestSkipLateAt_of_rightTail hS hright hSs hs hlate

/-! ## The two branches at programme level -/

/-- **The positive half of the dichotomy.**  If the late cofactor ranks fail to
be selected at infinitely many rows, then `1/2` lies in the Mersenne
achievement set.  The measurement says the failure rate is about one half at
every scale, so this is the disjunct that empirically fires — what is missing
is a proof that it fires infinitely often. -/
theorem half_mem_of_cofRanksLate_cofinal_miss
    (h : ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧
      ¬ cofRanksLate s ⊆ seamWordSupport (seamGreedyWord s)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_of_unboundedSkip
  intro N
  obtain ⟨s, hsN, hns⟩ := h (max 61 (3 * N + 3))
  have h61 : 61 ≤ s := le_trans (le_max_left _ _) hsN
  have hbig : 3 * N + 3 ≤ s := le_trans (le_max_right _ _) hsN
  rw [Finset.not_subset] at hns
  obtain ⟨d, hd, hdnot⟩ := hns
  have hdata := mem_cofRanksLate_iff.mp hd
  exact ⟨s, d, by omega, AngleB2.cofRanks_lt s h61 hdata.1, hdnot⟩

/-- **The unconditional global dichotomy.**  Either `1/2` is in the Mersenne
achievement set, or from some row on the integer seam greedy selects *every*
rank in the late zone.  Nothing is assumed. -/
theorem half_mem_or_eventually_late_selected :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S₀ : ℕ, ∀ s : ℕ, S₀ ≤ s → ∀ d : ℕ, d < s → 2 * s < 3 * d →
        d ∈ seamWordSupport (seamGreedyWord s) := by
  by_cases h : ∀ N : ℕ, ∃ s d : ℕ, N ≤ d ∧ d < s ∧
      d ∉ seamWordSupport (seamGreedyWord s)
  · exact Or.inl (half_mem_of_unboundedSkip h)
  right
  push Not at h
  obtain ⟨N, hN⟩ := h
  refine ⟨2 * N + 2, fun s hs d hds hlate => hN s d ?_ hds⟩
  omega

/-- In the second branch of `half_mem_or_eventually_late_selected` the late
cofactor ranks are certified for free, so `AngleB2`'s `hcof` degenerates to the
single even cofactor. -/
theorem eventually_cofRanksLate_subset_of_late_selected
    {S₀ : ℕ}
    (hsel : ∀ s : ℕ, S₀ ≤ s → ∀ d : ℕ, d < s → 2 * s < 3 * d →
      d ∈ seamWordSupport (seamGreedyWord s))
    (s : ℕ) (hs : 61 ≤ s) (hs₀ : S₀ ≤ s) :
    cofRanksLate s ⊆ seamWordSupport (seamGreedyWord s) := by
  intro d hd
  have hdata := mem_cofRanksLate_iff.mp hd
  exact hsel s hs₀ d (AngleB2.cofRanks_lt s (by omega) hdata.1) hdata.2

/-- **The wave statement.**  Either the positive branch fires outright, or the
all-right-tail branch of `#257` is contradictory for every sufficiently large
class `D`, granted *only* the even cofactor memberships `(s+1)/2` at the at most
three rows `D+1, D+2, D+3`.  The cofactor-`3` half of `AngleB2`'s `hcof` is
discharged unconditionally by the dichotomy. -/
theorem half_mem_or_eventually_allRight_landingExcess_two_impossible :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S₀ : ℕ, ∀ D : ℕ, 60 ≤ D → S₀ ≤ D →
        (∀ s : ℕ, D + 1 ≤ s →
          seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) →
        Recon257.seamExcess (D + 1) = 2 →
        (∀ s : ℕ, D + 1 ≤ s → s < D + 4 →
          (s + 1) / 2 ∈ AngleB2.cofRanks s →
            (s + 1) / 2 ∈ seamWordSupport (seamGreedyWord s)) →
        False := by
  rcases half_mem_or_eventually_late_selected with hhalf | ⟨S₀, hsel⟩
  · exact Or.inl hhalf
  refine Or.inr ⟨S₀, fun D hD hDS₀ hright hlanding hhalfcof => ?_⟩
  refine AngleB2.allRight_landingExcess_two_impossible D hD hright hlanding ?_
  intro s h1 h2 d hd
  rcases cofRanks_late_or_half hd with hlate | rfl
  · exact hsel s (by omega) d (AngleB2.cofRanks_lt s (by omega) hd) hlate
  · exact hhalfcof s h1 h2 hd

/-- **PROVED CONDITIONAL.**  On an all-right tail landing at excess `2`, granted the even
cofactor memberships, one of the three rows `D+1, D+2, D+3` carries a late
largest false rank.  This is one finite witness under an uninstantiated landing
premise, not a positive membership trigger; the endpoint requires a cofinal
supply. -/
theorem allRight_landingExcess_two_lateSkip
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (hhalfcof : ∀ s : ℕ, D + 1 ≤ s → s < D + 4 →
      (s + 1) / 2 ∈ AngleB2.cofRanks s →
        (s + 1) / 2 ∈ seamWordSupport (seamGreedyWord s)) :
    ∃ s : ℕ, D + 1 ≤ s ∧ s < D + 4 ∧ LargestSkipLateAt s := by
  by_contra hcon
  push Not at hcon
  refine AngleB2.allRight_landingExcess_two_impossible D hD hright hlanding ?_
  intro s h1 h2
  rcases cofRanks_subset_or_largestSkipLateAt s (by omega) (hhalfcof s h1 h2) with
    hsub | hlate
  · exact hsub
  · exact absurd hlate (hcon s h1 h2)

/-
Axiom audit.  Uncommenting the block below and re-running
`lake env lean ErdosProblems/Skip/D6.lean` reports, for every theorem here,

  depends on axioms: [propext, Classical.choice, Quot.sound]

(and `[propext, Quot.sound]` for the two purely arithmetic ones,
`halfCofactor_not_late` and `cofRanks_late_or_half`).  No `sorryAx`, no new
axiom.  The block is left commented so that the file checks with empty output.

#print axioms largestSkipLateAt_of_lateSkip
#print axioms half_mem_of_unboundedSkip
#print axioms half_mem_of_forall_largestSkipLateAt
#print axioms half_mem_of_largestSkipLateStepSocket
#print axioms halfCofactor_not_late
#print axioms cofRanks_late_or_half
#print axioms cofRanksLate_subset_or_largestSkipLateAt
#print axioms cofRanks_subset_or_largestSkipLateAt
#print axioms Ico_subset_seamWordSupport_of_rightTail
#print axioms not_largestSkipLateAt_of_rightTail
#print axioms half_mem_of_cofRanksLate_cofinal_miss
#print axioms half_mem_or_eventually_late_selected
#print axioms half_mem_or_eventually_allRight_landingExcess_two_impossible
#print axioms allRight_landingExcess_two_lateSkip
-/

end SkipD6

end Erdos249257
