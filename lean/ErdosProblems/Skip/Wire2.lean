/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleB2
import Erdos249257.HalfCylinderSkippedRankLimit

/-!
# Wire 2: conditional scale exclusions from an all-right tail

**RETRACTED:** this file does not close the all-right-tail branch of the `-2`
final middle cell.  `ErdosProblems/Lift/AngleB2.lean` proves a contradiction
only after assuming

  `hcof : ∀ s, D+1 ≤ s → s < D+4 → cofRanks s ⊆ seamWordSupport (seamGreedyWord s)`

as well as `Recon257.seamExcess (D+1) = 2`.  The cofactor assumption is not
unconditionally true.  **MEASURED:** the landing equality has no instance for
`5 ≤ D+1 ≤ 102`.  Thus no theorem below has an audited source class satisfying
all of the branch hypotheses.

**PROVED:** an all-right tail supplies `hcof` for sufficiently later rows.  This
gives explicit conditional exclusions at scales beyond twice the tail's start,
and at ratio `3/2` for the phases killed by a finite ratchet.  It does not
exclude the class where the tail starts, prove that such a tail exists, produce
a cofinal theorem, or decide whether `1/2` belongs to the Mersenne achievement
set.

## The mechanism

`hright` at start `S` says every row `s ≥ S` appends a `true` bit.  Hence
(`seamWordSupport_rightTail_eq`) the support of row `t` is the support of row
`s` together with the whole appended block `[s, t)`, for all `S ≤ s ≤ t`.  Two
consequences, and this file uses both:

* the block is *selected* — `Ico_subset_seamWordSupport_of_rightTail`;
* everything below `s` is *frozen* — `notMem_seamWordSupport_of_rightTail`.

Every one of AngleB2's cofactor ranks satisfies `s ≤ 2 * d`
(`cofRanks_two_mul_ge`), so as soon as `2 * S ≤ s` the cofactor ranks of row `s`
lie inside the block and are selected for free.  `hcof` is therefore discharged
by `hright` alone whenever the tail starts at or before half the row:

* `cofRanks_subset_of_rightTail` — `hright` from `S` gives `hcof` at every row
  `s ≥ max 61 (2 * S)`, with no further empirical premise;
* `allRight_landingExcess_two_impossible_of_earlyRightTail`,
  `finalMiddleCell_neg_two_impossible_of_earlyRightTail` — **PROVED
  CONDITIONAL**, without a separate `hcof` hypothesis, but still requiring the
  all-right tail, the scale inequality, and the landing or middle-cell data.

## What is proved, stated exactly

In the branch as it actually arises (`HalfCylinderFinalMiddleCellEscape`,
`AngleB2`) the tail starts at `S = D + 1`, so `2 * S ≤ D + 1` is unsatisfiable
*within one class*: the theorems above do **not** exclude the class that carries
the tail.  They exclude landing excess `2` in sufficiently later classes,
because `hright` at `D₁ + 1` is inherited by every `D₂ ≥ D₁`:

* `no_landing_beyond_double` — an all-right tail from `D₁ + 1` forces
  `Recon257.seamExcess (D₂ + 1) ≠ 2` for **every** `D₂ ≥ 2 * D₁ + 1`.  This is
  a statement about the actual seam greedy with no hypothesis on `D₂`.
* `allRight_landing_scale_rigidity` — **PROVED CONDITIONAL:** if a class carries
  the assumed all-right tail, any class with landing excess `2` lies at most at
  twice its scale.  This is not an existence theorem for either class.
* `finalMiddleCell_neg_two_unique_scale` — the same in middle-cell idiom: two
  final middle cells of charge `-2` with all-right tails cannot sit more than a
  factor `2` apart under the stated hypotheses.

Off `87` explicit residue classes mod `2730` the factor improves to `3/2`
(`no_landing_beyond_threeHalves`), because the cofactor-`3` ranks enter the
block already at `3 * S ≤ 2 * s`; `cof3Ratchet_survivor_count` is the
`decide +kernel` count of phases whose run is still nonzero after six steps
under that weaker floor.

## Limits of these certificate methods, and what remains

`largestCertifiableRank_le` proves that a divisor `d < s` of `2s+1` or `2s+2`
has cofactor at least `3`, hence `3 * d ≤ 2 * s + 2`.  So no rank certifiable
from these divisibility conditions exceeds `(2s+2)/3`; this particular
divisibility-certificate method cannot justify a ratio below `3/2`.

**PROVED CONDITIONAL:** under the displayed middle-cell and all-right-tail
hypotheses, the factor `2` cannot be lowered for the cofactor-`{3,4}`
certificate.  The terminal bit at row `D+1` is `false`, so rank `D` is skipped
and stays skipped (`middleCell_rank_notMem_seamWordSupport`).  That rank is the
cofactor-`4` rank `(s+1)/2` of row `s = 2 * D - 1`, so `hcof` fails there
(`cofRanks_not_subset_at_double`), three rows below the threshold
`2 * D + 2` at which the free certificate starts.

The proof method leaves the diagonal window untreated: a hypothetical class
`D` whose all-right tail starts at `D + 1`.  For that window the certificate
would have to come from the frozen prefix of row `D + 1`, which `hright` does
not see.  The positive `1/2`-membership route does not follow from this file:
`allRight_forces_frozen_skip` shows the branch produces exactly one skipped
rank, bounded by `D`, repeated at every row — a bounded family, whereas
`half_mem_mersenneAchievementSet_of_unboundedSkippedRanks` needs an unbounded
one.  Because the landing premise has no audited instance, this is a
description of the conditional proof's residual case, not evidence that a
live residual class exists.
-/

namespace Erdos249257

namespace Wire2

open HalfCylinderIntegerGreedy
open Set Filter

/-! ## The right tail freezes the word below its start -/

/-- **The exact shape of an all-right tail.**  On a right tail from `S`, the
support of row `t` is the support of row `s` together with the whole appended
block `[s, t)`, for every `S ≤ s ≤ t`.  Both halves of this are used below: the
block is *selected*, and everything below `s` is *frozen*. -/
theorem seamWordSupport_rightTail_eq
    {S : ℕ} (hS : 3 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s : ℕ} (hSs : S ≤ s) :
    ∀ t : ℕ, s ≤ t →
      seamWordSupport (seamGreedyWord t)
        = seamWordSupport (seamGreedyWord s) ∪ Finset.Ico s t := by
  intro t hst
  induction t, hst using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
      rw [hright t (by omega), seamWordSupport_extend_true (by omega) (seamGreedyWord t), ih]
      ext d
      constructor
      · intro hd
        rcases Finset.mem_insert.mp hd with rfl | hd'
        · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨ht, by omega⟩)
        · rcases Finset.mem_union.mp hd' with h | h
          · exact Finset.mem_union_left _ h
          · have h2 := Finset.mem_Ico.mp h
            exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨h2.1, by omega⟩)
      · intro hd
        rcases Finset.mem_union.mp hd with h | h
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
        · have h2 := Finset.mem_Ico.mp h
          rcases Nat.lt_or_ge d t with hlt | hge
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨h2.1, hlt⟩))
          · have hdt : d = t := by omega
            exact hdt ▸ Finset.mem_insert_self _ _

/-- The appended block of an all-right tail is entirely selected. -/
theorem Ico_subset_seamWordSupport_of_rightTail
    {S : ℕ} (hS : 3 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {t : ℕ} (ht : S ≤ t) :
    Finset.Ico S t ⊆ seamWordSupport (seamGreedyWord t) := by
  rw [seamWordSupport_rightTail_eq hS hright le_rfl t ht]
  exact fun d hd => Finset.mem_union_right _ hd

/-- **The frozen prefix.**  On an all-right tail a rank skipped once below the
current row is skipped at every later row: the tail never revisits it. -/
theorem notMem_seamWordSupport_of_rightTail
    {S : ℕ} (hS : 3 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s t d : ℕ} (hSs : S ≤ s) (hst : s ≤ t) (hds : d < s)
    (hd : d ∉ seamWordSupport (seamGreedyWord s)) :
    d ∉ seamWordSupport (seamGreedyWord t) := by
  rw [seamWordSupport_rightTail_eq hS hright hSs t hst]
  intro hc
  rcases Finset.mem_union.mp hc with h | h
  · exact hd h
  · exact absurd (Finset.mem_Ico.mp h).1 (by omega)

/-! ## Every cofactor rank is at least half the row -/

/-- Each of AngleB2's cofactor ranks satisfies `s ≤ 2 * d`.  This is the only
size fact needed to place them inside the appended block. -/
theorem cofRanks_two_mul_ge {s d : ℕ} (hd : d ∈ AngleB2.cofRanks s) : s ≤ 2 * d := by
  rcases AngleB2.cofRanks_cases hd with rfl | rfl | rfl <;> omega

/-- **Sharpness of the exponent `3/2`.**  No rank certifiable from divisibility
alone ever exceeds `2 s / 3`: a divisor `d` of `2s+1` or `2s+2` with `d < s`
has cofactor at least `3`.  So a block starting at `S` can contain a certified
rank of row `s` only when `3 * S ≤ 2 * s + 2`, and the method below cannot be
pushed past that. -/
theorem largestCertifiableRank_le {s d : ℕ} (hds : d < s) (hd0 : 0 < d)
    (hdvd : d ∣ 2 * s + 1 ∨ d ∣ 2 * s + 2) : 3 * d ≤ 2 * s + 2 := by
  rcases hdvd with ⟨c, hc⟩ | ⟨c, hc⟩
  · have hc3 : 3 ≤ c := by
      rcases Nat.lt_or_ge c 3 with h | h
      · interval_cases c <;> omega
      · exact h
    nlinarith
  · have hc3 : 3 ≤ c := by
      rcases Nat.lt_or_ge c 3 with h | h
      · interval_cases c <;> omega
      · exact h
    nlinarith

/-! ## The right tail discharges `hcof` -/

/-- **The certificate is free on an early right tail.**  If the all-right tail
starts at `S` and the row `s` is at least `2 * S`, then AngleB2's cofactor ranks
of row `s` lie in the appended block and are selected.  No measurement, no
hypothesis. -/
theorem cofRanks_subset_of_rightTail
    {S : ℕ} (hS : 3 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s : ℕ} (hs61 : 61 ≤ s) (hSs : 2 * S ≤ s) :
    AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  intro d hd
  have hlt : d < s := AngleB2.cofRanks_lt s hs61 hd
  have hhalf : s ≤ 2 * d := cofRanks_two_mul_ge hd
  exact Ico_subset_seamWordSupport_of_rightTail hS hright (by omega : S ≤ s)
    (Finset.mem_Ico.mpr ⟨by omega, hlt⟩)

/-! ## Conditional contradictions without a separate `hcof` hypothesis -/

/-- **PROVED CONDITIONAL.**  A landing with excess `2` at rank `D ≥ 60` is
contradictory if an all-right tail starts at or before `(D+1)/2`.  AngleB2's
separate `hcof` hypothesis is derived from the tail and the scale inequality.
The landing equality itself has no instance in the audited range
`5 ≤ D+1 ≤ 102`. -/
theorem allRight_landingExcess_two_impossible_of_earlyRightTail
    (S D : ℕ) (hS : 3 ≤ S) (hD : 60 ≤ D) (hle : 2 * S ≤ D + 1)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    False := by
  refine AngleB2.allRight_landingExcess_two_impossible D hD
    (fun s hs => hright s (by omega)) hlanding ?_
  intro s h1 _
  exact cofRanks_subset_of_rightTail hS hright (by omega) (by omega)

/-- **PROVED CONDITIONAL.**  The same implication in the shape used by
`HalfFinalMiddlePhaseSieve`: the stated middle-cell data and sufficiently early
all-right tail imply a contradiction, with no separate `hcof` hypothesis. -/
theorem finalMiddleCell_neg_two_impossible_of_earlyRightTail
    (S D : ℕ) (hS : 3 ≤ S) (hD : 60 ≤ D) (hle : 2 * S ≤ D + 1)
    (hncarry : ¬ (seamAdjacentCut D (by omega : 5 ≤ D)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega : 5 ≤ D)).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse <
          (seamAdjacentCut D (by omega : 5 ≤ D)).terminalWeight)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hcell :
      4 * ((seamAdjacentCut D (by omega : 5 ≤ D)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse : ℤ) - 4 = -2) :
    False :=
  allRight_landingExcess_two_impossible_of_earlyRightTail S D hS hD hle hright
    (Recon257.seamExcess_landing_eq_two D (by omega) hncarry hmiddle hcell)

/-! ## One right tail excludes landing excess `2` beyond twice its start -/

/-- **No landing beyond the double.**  A single all-right tail from `D₁ + 1`
forbids the landing excess `2` at *every* class `D₂ ≥ 2 * D₁ + 1`.  Apart from
the inequality and the standing range condition `60 ≤ D₂` inherited from
`AngleB2`, there is no hypothesis on `D₂`: in particular no `hcof`, no `hright`
at `D₂` (it is inherited from `D₁`), and no threshold obtained by negating a
cofinality statement. -/
theorem no_landing_beyond_double
    (D₁ D₂ : ℕ) (h₁ : 3 ≤ D₁) (h₂ : 60 ≤ D₂) (hle : 2 * D₁ + 1 ≤ D₂)
    (hright : ∀ s : ℕ, D₁ + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    Recon257.seamExcess (D₂ + 1) ≠ 2 := by
  intro hlanding
  exact allRight_landingExcess_two_impossible_of_earlyRightTail (D₁ + 1) D₂
    (by omega) (by omega) (by omega) hright hlanding

/-- **PROVED CONDITIONAL (scale exclusion).**  If a class `D₁ ≥ 60` carries an
all-right tail, then every class with landing excess `2` is at most `2 * D₁`.
This does not prove that a source class with the required tail or landing
exists. -/
theorem allRight_landing_scale_rigidity
    (D₁ D₂ : ℕ) (h₁ : 60 ≤ D₁)
    (hright₁ : ∀ s : ℕ, D₁ + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding₂ : Recon257.seamExcess (D₂ + 1) = 2) :
    D₂ ≤ 2 * D₁ := by
  by_contra hcon
  exact no_landing_beyond_double D₁ D₂ (by omega) (by omega) (by omega) hright₁ hlanding₂

/-- **PROVED CONDITIONAL (legacy name).**  If an all-right tail starts at
`D+1`, then no class beyond `2 * D` has landing excess `2`.  The landing
hypothesis in this declaration is unused; the result neither excludes the
starting class nor resolves the branch. -/
theorem allRight_branch_resolved
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (_hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∀ D' : ℕ, 2 * D + 1 ≤ D' → Recon257.seamExcess (D' + 1) ≠ 2 :=
  fun D' hD' => no_landing_beyond_double D D' (by omega) (by omega) hD' hright

/-- **PROVED CONDITIONAL.**  A disjunctive packaging of the same later-scale
exclusion.  The proof always supplies the left disjunct; it does not establish
the positive membership statement on the right. -/
theorem allRight_branch_resolved_or_half
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    (∀ D' : ℕ, 2 * D + 1 ≤ D' → Recon257.seamExcess (D' + 1) ≠ 2) ∨
      (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  Or.inl (allRight_branch_resolved D hD hright hlanding)

/-! ## What the residual window looks like -/

/-- **PROVED CONDITIONAL.**  An all-right tail together with landing excess `2`
forces a cofactor skip in its first three rows.  This is AngleB2 read
contrapositively.  Since the landing equality has no audited instance, the
theorem does not establish that the residual window contains a live class. -/
theorem allRight_forces_cofSkip
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ s : ℕ, D + 1 ≤ s ∧ s < D + 4 ∧
      ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  by_contra hcon
  refine AngleB2.allRight_landingExcess_two_impossible D hD hright hlanding ?_
  intro s h1 h2
  by_contra hsub
  exact hcon ⟨s, h1, h2, hsub⟩

/-- **PROVED CONDITIONAL: the forced skip is frozen and boxed in.**  Under the
all-right-tail and landing hypotheses, the rank lies in
`[(D+1)/2, D]` — above half the row, because it is a cofactor rank; at most `D`,
because everything above `D` is in the appended all-`true` block — and it is
skipped at *every* row from `D+1` on.  This is the exact obstruction: the skip
supply produced by the branch is a single bounded rank, never an unbounded
family, so it cannot feed `half_mem_mersenneAchievementSet_of_unboundedSkippedRanks`. -/
theorem allRight_forces_frozen_skip
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ d : ℕ, D + 1 ≤ 2 * d ∧ d ≤ D ∧
      ∀ t : ℕ, D + 4 ≤ t → d ∉ seamWordSupport (seamGreedyWord t) := by
  obtain ⟨s, h1, h2, hns⟩ := allRight_forces_cofSkip D hD hright hlanding
  rw [Finset.not_subset] at hns
  obtain ⟨d, hd, hdns⟩ := hns
  have hlt : d < s := AngleB2.cofRanks_lt s (by omega) hd
  have hhalf : s ≤ 2 * d := cofRanks_two_mul_ge hd
  have hdD : d ≤ D := by
    by_contra hcon
    exact hdns (Ico_subset_seamWordSupport_of_rightTail (S := D + 1) (by omega) hright
      (by omega : D + 1 ≤ s) (Finset.mem_Ico.mpr ⟨by omega, hlt⟩))
  refine ⟨d, by omega, hdD, fun t ht => ?_⟩
  exact notMem_seamWordSupport_of_rightTail (S := D + 1) (by omega) hright
    (by omega : D + 1 ≤ s) (by omega : s ≤ t) hlt hdns

/-! ## The middle cell skips its own rank, and the factor `2` is sharp -/

/-- On the middle branch the terminal bit of row `D + 1` is `false`: the rank
`D` itself is not selected.  On an all-right tail it is therefore never
selected at any later row either. -/
theorem middleCell_rank_notMem_seamWordSupport
    (D : ℕ) (hD : 5 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D hD).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D hD).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D hD).belowPulse <
          (seamAdjacentCut D hD).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ∀ t : ℕ, D + 1 ≤ t → D ∉ seamWordSupport (seamGreedyWord t) := by
  have hbase : D ∉ seamWordSupport (seamGreedyWord (D + 1)) := by
    rw [seamGreedyWord_succ_eq_middleBranch D hD hncarry hmiddle,
      seamWordSupport_extend_false (by omega)]
    intro hc
    exact absurd (seamWordSupport_below hc).2 (by omega)
  intro t ht
  exact notMem_seamWordSupport_of_rightTail (S := D + 1) (by omega) hright
    (le_refl (D + 1)) ht (by omega) hbase

/-- **The factor `2` is sharp for the cofactor-`{3,4}` certificate.**  The rank
`D` skipped by the middle cell is exactly the cofactor-`4` rank `(s+1)/2` of the
row `s = 2 * D - 1`, so AngleB2's `hcof` genuinely fails there — three rows
below `2 * D + 2`, where `cofRanks_subset_of_rightTail` first bites.  The
threshold cannot be lowered by sharper bookkeeping. -/
theorem cofRanks_not_subset_at_double
    (D : ℕ) (hD : 5 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D hD).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D hD).remainder +
            (seamPerturbedFamily D (by omega : 3 ≤ D)).gap -
            (seamAdjacentCut D hD).belowPulse <
          (seamAdjacentCut D hD).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ¬ AngleB2.cofRanks (2 * D - 1) ⊆ seamWordSupport (seamGreedyWord (2 * D - 1)) := by
  intro hsub
  have hmem : D ∈ AngleB2.cofRanks (2 * D - 1) := by
    have hodd : (2 * D - 1) % 6 = 1 ∨ (2 * D - 1) % 6 = 3 ∨ (2 * D - 1) % 6 = 5 := by omega
    unfold AngleB2.cofRanks
    rcases hodd with h | h | h
    · rw [if_pos h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (by omega))
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]
      exact Finset.mem_singleton.mpr (by omega)
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (by omega))
  exact middleCell_rank_notMem_seamWordSupport D hD hncarry hmiddle hright
    (2 * D - 1) (by omega) (hsub hmem)

/-! ## Pushing the constant from `2` to `3/2`

The block `[S, s)` contains the cofactor-`3` ranks `(2s+1)/3`, `2(s+1)/3`
already when `3 * S ≤ 2 * s`, a full half-step earlier than it contains the
cofactor-`4` rank `(s+1)/2`.  Dropping `(s+1)/2` from the certificate weakens
the certified floor from `![0,3,1,1,2,2]` (mod `6`) to `![0,2,1]` (mod `3`), and
the resulting ratchet no longer empties the phase set at depth `6`: exactly
`87` of the `2730` joint phases remain nonzero at that depth.  The theorem below
does not assert that all `87` remain nonzero forever.  For the other `2643` the
run has reached zero by depth `6`.

By `largestCertifiableRank_le` the exponent `3/2` cannot be improved: no rank
certifiable from divisibility alone exceeds `(2s+2)/3`. -/

/-- The cofactor-`3` rank of row `s`. -/
def cof3Ranks (s : ℕ) : Finset ℕ :=
  if s % 3 = 1 then {(2 * s + 1) / 3}
  else if s % 3 = 2 then {2 * (s + 1) / 3}
  else ∅

/-- The pulse the cofactor-`3` rank is guaranteed to contribute. -/
def cof3Floor (s : ℕ) : ℕ := if s % 3 = 1 then 2 else if s % 3 = 2 then 1 else 0

theorem cof3Ranks_lower {s d : ℕ} (hd : d ∈ cof3Ranks s) : 2 * s ≤ 3 * d := by
  unfold cof3Ranks at hd
  split_ifs at hd <;>
    simp only [Finset.mem_singleton, Finset.notMem_empty] at hd <;> omega

theorem cof3Ranks_upper {s d : ℕ} (hd : d ∈ cof3Ranks s) : 3 * d ≤ 2 * s + 2 := by
  unfold cof3Ranks at hd
  split_ifs at hd <;>
    simp only [Finset.mem_singleton, Finset.notMem_empty] at hd <;> omega

theorem cof3Ranks_lt (s : ℕ) (hs : 61 ≤ s) {d : ℕ} (hd : d ∈ cof3Ranks s) : d < s := by
  have := cof3Ranks_upper hd; omega

theorem cof3Ranks_ge (s : ℕ) (hs : 61 ≤ s) {d : ℕ} (hd : d ∈ cof3Ranks s) : 27 ≤ d := by
  have := cof3Ranks_lower hd; omega

theorem cof3Ranks_disjoint (s : ℕ) (hs : 61 ≤ s) :
    Disjoint ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) (cof3Ranks s) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have h27 := cof3Ranks_ge s hs hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem cof3Floor_le_pulse (s : ℕ) : cof3Floor s ≤ ∑ d ∈ cof3Ranks s, rowPulse s d := by
  have h3 : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases h3 with h | h | h
  · simp only [cof3Floor, cof3Ranks, h]; norm_num
  · obtain ⟨q, rfl⟩ : ∃ q, s = 3 * q + 1 := ⟨s / 3, by omega⟩
    have e1 : (2 * (3 * q + 1) + 1) / 3 = 2 * q + 1 := by omega
    have hset : cof3Ranks (3 * q + 1) = {2 * q + 1} := by
      unfold cof3Ranks; rw [if_pos h, e1]
    have r1 : 2 ≤ rowPulse (3 * q + 1) (2 * q + 1) := by
      have hdv : (2 * q + 1) ∣ 2 * (3 * q + 1) + 1 := ⟨3, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold cof3Floor
    rw [if_pos h]
    omega
  · obtain ⟨q, rfl⟩ : ∃ q, s = 3 * q + 2 := ⟨s / 3, by omega⟩
    have e1 : 2 * (3 * q + 2 + 1) / 3 = 2 * q + 2 := by omega
    have hset : cof3Ranks (3 * q + 2) = {2 * q + 2} := by
      unfold cof3Ranks; rw [if_neg (by omega), if_pos h, e1]
    have r1 : 1 ≤ rowPulse (3 * q + 2) (2 * q + 2) := by
      have hdv : (2 * q + 2) ∣ 2 * (3 * q + 2) + 2 := ⟨3, by ring⟩
      simp only [rowPulse, if_pos hdv]
      split_ifs <;> omega
    rw [hset, Finset.sum_singleton]
    unfold cof3Floor
    rw [if_neg (by omega), if_pos h]
    omega

/-- The cofactor-`3` certified floor. -/
def totalFloor3 (s : ℕ) : ℕ := Recon257.pulseFloor s + cof3Floor s

theorem one_le_totalFloor3 (s : ℕ) : 1 ≤ totalFloor3 s := by
  have := Recon257.one_le_pulseFloor s
  unfold totalFloor3
  omega

theorem totalFloor3_add_period (s : ℕ) : totalFloor3 (s + 2730) = totalFloor3 s := by
  unfold totalFloor3 cof3Floor
  rw [Recon257.pulseFloor_add_period, show (s + 2730) % 3 = s % 3 by omega]

theorem totalFloor3_le_belowPulse (s : ℕ) (hs : 61 ≤ s)
    (hcof : cof3Ranks s ⊆ seamWordSupport (seamGreedyWord s)) :
    totalFloor3 s ≤ (seamAdjacentCut s (by omega : 5 ≤ s)).belowPulse := by
  classical
  have h236 := two_three_six_mem_seamGreedySupport s (by omega)
  have h7 := seven_mem_seamGreedySupport s (by omega)
  have h14 := fourteen_mem_seamGreedySupport s (by omega)
  have h20 := twenty_mem_seamGreedySupport s (by omega)
  have h21 := twentyOne_mem_seamGreedySupport s (by omega)
  have h26 := twentySix_mem_seamGreedySupport s (by omega)
  have hsmall : ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ⊆
      seamWordSupport (seamGreedyWord s) := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h236.1
    · exact h236.2.1
    · exact h236.2.2
    · exact h7
    · exact h14
    · exact h20
    · exact h21
    · exact h26
  have hsub : (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cof3Ranks s) ⊆
      seamWordSupport (seamGreedyWord s) := Finset.union_subset hsmall hcof
  have hsum :
      ∑ d ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cof3Ranks s), rowPulse s d ≤
        ∑ d ∈ seamWordSupport (seamGreedyWord s), rowPulse s d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  have hsplit :
      ∑ d ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ cof3Ranks s), rowPulse s d =
        (∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d) +
          ∑ d ∈ cof3Ranks s, rowPulse s d :=
    Finset.sum_union (cof3Ranks_disjoint s hs)
  have hexp : ∑ d ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s d =
      Recon257.pulseFloor s := by
    rw [Recon257.pulseFloor_eq_rowPulseSum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hcofp := cof3Floor_le_pulse s
  change totalFloor3 s ≤ wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  unfold totalFloor3
  rw [hsplit, hexp] at hsum
  omega

/-- **The cofactor-`3` ranks are free from a `3/2`-early right tail.** -/
theorem cof3Ranks_subset_of_rightTail
    {S : ℕ} (hS : 3 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s : ℕ} (hs61 : 61 ≤ s) (hSs : 3 * S ≤ 2 * s) :
    cof3Ranks s ⊆ seamWordSupport (seamGreedyWord s) := by
  intro d hd
  have hlt : d < s := cof3Ranks_lt s hs61 hd
  have hlow : 2 * s ≤ 3 * d := cof3Ranks_lower hd
  exact Ico_subset_seamWordSupport_of_rightTail hS hright (by omega : S ≤ s)
    (Finset.mem_Ico.mpr ⟨by omega, hlt⟩)

/-! ### The cofactor-`3` ratchet -/

def cof3Step (s b : ℕ) : ℕ :=
  if 3 * totalFloor3 s + 4 ≤ 4 * b then 4 * b - (3 * totalFloor3 s + 3) else 0

def cof3Run (D : ℕ) : ℕ → ℕ
  | 0 => 3
  | k + 1 => cof3Step (D + 1 + k) (cof3Run D k)

@[simp] theorem cof3Run_zero (D : ℕ) : cof3Run D 0 = 3 := rfl

theorem cof3Run_succ (D k : ℕ) : cof3Run D (k + 1) = cof3Step (D + 1 + k) (cof3Run D k) := rfl

theorem cof3Run_add_period (D k : ℕ) : cof3Run (D + 2730) k = cof3Run D k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [cof3Run_succ, cof3Run_succ, ih]
      unfold cof3Step
      rw [show D + 2730 + 1 + k = (D + 1 + k) + 2730 by ring, totalFloor3_add_period]

theorem cof3Run_add_mul_period (D k n : ℕ) : cof3Run (D + 2730 * n) k = cof3Run D k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show D + 2730 * (n + 1) = (D + 2730 * n) + 2730 by ring, cof3Run_add_period, ih]

theorem cof3Run_mod (D k : ℕ) : cof3Run D k = cof3Run (D % 2730) k := by
  conv_lhs => rw [show D = D % 2730 + 2730 * (D / 2730) by
    rw [Nat.add_comm]; exact (Nat.div_add_mod D 2730).symm]
  exact cof3Run_add_mul_period _ _ _

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
/-- **PROVED by finite reduction:** exactly `87` of the `2730` joint phases
remain nonzero after six cofactor-`3` ratchet steps.  Compare
`AngleB2.cofRatchet_finite_core`, where adjoining the cofactor-`4` rank
`(s+1)/2` brings the count to `0` at depth `3`.  This theorem makes no claim
about the later fate of the `87` phases. -/
theorem cof3Ratchet_survivor_count :
    ((Finset.range 2730).filter (fun D => cof3Run D 6 ≠ 0)).card = 87 := by
  decide +kernel

/-! ### Soundness of the cofactor-`3` ratchet -/

theorem cof3Step_zero (s : ℕ) : cof3Step s 0 = 0 := by
  unfold cof3Step
  rw [if_neg (by have := one_le_totalFloor3 s; omega)]

theorem cof3Run_bound
    (S D : ℕ) (hS : 3 ≤ S) (hD : 60 ≤ D) (hle : 3 * S ≤ 2 * D + 2)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∀ k, 3 * Recon257.seamExcess (D + 1 + k) - 3 ≤ (cof3Run D k : ℤ) := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) (fun s hs => hright s (by omega))
  intro k
  induction k with
  | zero =>
      simp only [Nat.add_zero, cof3Run_zero, hlanding]
      norm_num
  | succ k ih =>
      have hs : D + 1 ≤ D + 1 + k := by omega
      have hstep := (horbit (D + 1 + k) hs).2
      have hrec : Recon257.seamExcess (D + 1 + (k + 1)) =
          4 * Recon257.seamExcess (D + 1 + k) -
            ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) - 4 := by
        simpa [Recon257.seamExcess, show D + 1 + (k + 1) = (D + 1 + k) + 1 by ring] using hstep
      have hfloor : (totalFloor3 (D + 1 + k) : ℤ) ≤
          ((seamAdjacentCut (D + 1 + k) (by omega : 5 ≤ D + 1 + k)).belowPulse : ℤ) := by
        exact_mod_cast totalFloor3_le_belowPulse (D + 1 + k) (by omega)
          (cof3Ranks_subset_of_rightTail hS hright (by omega) (by omega))
      have hmain : 3 * Recon257.seamExcess (D + 1 + (k + 1)) - 3 ≤
          4 * (cof3Run D k : ℤ) - (3 * (totalFloor3 (D + 1 + k) : ℤ) + 3) := by
        rw [hrec]; omega
      rw [cof3Run_succ]
      unfold cof3Step
      split_ifs with hcond
      · have hle' : 3 * totalFloor3 (D + 1 + k) + 3 ≤ 4 * cof3Run D k := by omega
        have hcast :
            ((4 * cof3Run D k - (3 * totalFloor3 (D + 1 + k) + 3) : ℕ) : ℤ) =
              4 * (cof3Run D k : ℤ) - (3 * (totalFloor3 (D + 1 + k) : ℤ) + 3) := by
          push_cast [Nat.cast_sub hle']
          ring
        rw [hcast]
        exact hmain
      · have hcondZ : 4 * (cof3Run D k : ℤ) ≤ 3 * (totalFloor3 (D + 1 + k) : ℤ) + 3 := by
          have hnat : 4 * cof3Run D k ≤ 3 * totalFloor3 (D + 1 + k) + 3 := by omega
          exact_mod_cast hnat
        simp only [Nat.cast_zero]
        omega

/-- **PROVED CONDITIONAL.**  On a phase whose six-step cofactor-`3` run reaches
zero, the stated sufficiently early all-right tail is incompatible with
landing excess `2`.  No separate `hcof` hypothesis is needed: the tail
certifies its own cofactor-`3` ranks. -/
theorem allRight_landingExcess_two_impossible_of_threeHalvesRightTail
    (S D : ℕ) (hS : 3 ≤ S) (hD : 60 ≤ D) (hle : 3 * S ≤ 2 * D + 2)
    (hdead : cof3Run (D % 2730) 6 = 0)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    False := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) (fun s hs => hright s (by omega))
  have hbound := cof3Run_bound S D hS hD hle hright hlanding 6
  rw [cof3Run_mod D 6, hdead] at hbound
  have hpos : 0 < Recon257.seamExcess (D + 1 + 6) := by
    have := (horbit (D + 1 + 6) (by omega)).1
    simpa [Recon257.seamExcess] using this
  have hone : Recon257.seamExcess (D + 1 + 6) = 1 := by
    simp only [Nat.cast_zero] at hbound
    omega
  have hstep := (horbit (D + 1 + 6) (by omega)).2
  have hrec : Recon257.seamExcess (D + 1 + 6 + 1) =
      4 * Recon257.seamExcess (D + 1 + 6) -
        ((seamAdjacentCut (D + 1 + 6) (by omega : 5 ≤ D + 1 + 6)).belowPulse : ℤ) - 4 := by
    simpa [Recon257.seamExcess] using hstep
  have hnext : 0 < Recon257.seamExcess (D + 1 + 6 + 1) := by
    have := (horbit (D + 1 + 6 + 1) (by omega)).1
    simpa [Recon257.seamExcess] using this
  have hfloor : (Recon257.pulseFloor (D + 1 + 6) : ℤ) ≤
      ((seamAdjacentCut (D + 1 + 6) (by omega : 5 ≤ D + 1 + 6)).belowPulse : ℤ) := by
    exact_mod_cast Recon257.pulseFloor_le_belowPulse (D + 1 + 6) (by omega)
  have hone' : (1 : ℤ) ≤ (Recon257.pulseFloor (D + 1 + 6) : ℤ) := by
    exact_mod_cast Recon257.one_le_pulseFloor (D + 1 + 6)
  rw [hone] at hrec
  omega

/-- **PROVED CONDITIONAL (scale exclusion at ratio `3/2`).**  On the phases
whose six-step run is zero, an all-right tail from `D₁ + 1` forbids landing
excess `2` at every class satisfying the displayed scale inequality. -/
theorem no_landing_beyond_threeHalves
    (D₁ D₂ : ℕ) (h₁ : 3 ≤ D₁) (h₂ : 60 ≤ D₂) (hle : 3 * D₁ + 1 ≤ 2 * D₂)
    (hdead : cof3Run (D₂ % 2730) 6 = 0)
    (hright : ∀ s : ℕ, D₁ + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    Recon257.seamExcess (D₂ + 1) ≠ 2 := by
  intro hlanding
  exact allRight_landingExcess_two_impossible_of_threeHalvesRightTail (D₁ + 1) D₂
    (by omega) (by omega) (by omega) hdead hright hlanding

/-! ## A factor-`2` exclusion in middle-cell idiom -/

/-- **PROVED CONDITIONAL.**  A smaller class carrying the stated all-right tail
and a larger class carrying the displayed middle-cell data are incompatible
when separated by more than a factor `2`.  Only the tail of the smaller class
is used.  The theorem is a scale exclusion, not a proof that the branch has at
most one class or that either hypothetical cell exists. -/
theorem finalMiddleCell_neg_two_unique_scale
    (D₁ D₂ : ℕ) (h₁ : 60 ≤ D₁) (h₂ : 60 ≤ D₂) (hle : 2 * D₁ + 1 ≤ D₂)
    (hright₁ : ∀ s : ℕ, D₁ + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hncarry : ¬ (seamAdjacentCut D₂ (by omega : 5 ≤ D₂)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D₂ (by omega : 5 ≤ D₂)).remainder +
            (seamPerturbedFamily D₂ (by omega : 3 ≤ D₂)).gap -
            (seamAdjacentCut D₂ (by omega : 5 ≤ D₂)).belowPulse <
          (seamAdjacentCut D₂ (by omega : 5 ≤ D₂)).terminalWeight)
    (hcell :
      4 * ((seamAdjacentCut D₂ (by omega : 5 ≤ D₂)).remainder : ℤ) -
          ((seamAdjacentCut D₂ (by omega : 5 ≤ D₂)).belowPulse : ℤ) - 4 = -2) :
    False :=
  no_landing_beyond_double D₁ D₂ (by omega) h₂ hle hright₁
    (Recon257.seamExcess_landing_eq_two D₂ (by omega) hncarry hmiddle hcell)

/-
Axiom audit.  Re-running this file with the block below uncommented reports,
for every theorem in it,

  depends on axioms: [propext, Classical.choice, Quot.sound]

(and `[propext, Quot.sound]` for the purely arithmetic `cof3Floor_le_pulse`).
No `sorryAx`, no `Lean.ofReduceBool`, no `native_decide`.  The block is left
commented so that `lake env lean` produces empty output.

#print axioms seamWordSupport_rightTail_eq
#print axioms Ico_subset_seamWordSupport_of_rightTail
#print axioms notMem_seamWordSupport_of_rightTail
#print axioms cofRanks_two_mul_ge
#print axioms largestCertifiableRank_le
#print axioms cofRanks_subset_of_rightTail
#print axioms allRight_landingExcess_two_impossible_of_earlyRightTail
#print axioms finalMiddleCell_neg_two_impossible_of_earlyRightTail
#print axioms no_landing_beyond_double
#print axioms allRight_landing_scale_rigidity
#print axioms allRight_branch_resolved
#print axioms allRight_branch_resolved_or_half
#print axioms allRight_forces_cofSkip
#print axioms allRight_forces_frozen_skip
#print axioms middleCell_rank_notMem_seamWordSupport
#print axioms cofRanks_not_subset_at_double
#print axioms cof3Ratchet_survivor_count
#print axioms allRight_landingExcess_two_impossible_of_threeHalvesRightTail
#print axioms no_landing_beyond_threeHalves
#print axioms finalMiddleCell_neg_two_unique_scale
-/

end Wire2

end Erdos249257
