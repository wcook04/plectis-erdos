/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleB2
import Erdos249257.HalfCylinderSkippedRankLimit

/-!
# Skip Wire3: conditional consequences of an auxiliary all-right-tail branch

This file studies the **concrete** `seamGreedyWord` under two simultaneous
assumptions:

* `hright`: every later concrete seam row extends to the right;
* `hlanding`: the auxiliary quantity
  `Recon257.seamExcess (D+1)` is exactly `2`.

These are not a proof of the corpus-level hypothetical-support branch for
Erdős #257.  In particular, `seamExcess` is an auxiliary definition introduced
in `Lift/Recon257.lean`, not a hypothesis already present in the original
reduction.

**PROVED, CONDITIONAL:** under `hright`, later support is the frozen landing
support plus the free block.  Consequently the candidate cofactor ranks are
selected from row `2*D+1` onward.

**PROVED, CONDITIONAL:** after also assuming `hlanding`, the file derives bounds
on the landing pulse and several permanent-skip implications.  These are
implications from the displayed assumptions, not exclusions of concrete
residue classes.

**MEASURED:** `Recon257.seamExcess s = 2` has no instance for
`s ∈ [5,102]`.  Thus none of the `hlanding`-dependent results is instantiated
in that audited range.

**PROVED VACUOUS:** `Skip/verify/V9.lean` proves that the additional hypothesis
`2 ≤ AngleB2.cofFloor (D+1)` contradicts `hright` and `hlanding`: the latter
force `pulseFloor (D+1) ≤ 2`, while that cofactor-floor bound forces
`3 ≤ pulseFloor (D+1)`.  Therefore `rightTail_landing_cofSkip`,
`rightTail_frozen_skipped_rank`, `rightTail_frozen_skip_cofactorThree`,
`rightTail_frozen_skipped_rank_of_residue`, and the corresponding final
conjunct of `allRight_branch_resolved` have no satisfiable hypothesis block.

**RETRACTED:** earlier prose said this file closed or resolved the all-right
branch.  It does not.  The classical cofactor dichotomy below does not decide
which disjunct holds, and the landing-dependent conclusions do not close a
class that occurs in the audited concrete orbit.

## The frozen-support law

Under `hright` the support of every later row is the **frozen landing support
together with the whole free block**:

  `seamWordSupport (seamGreedyWord (D+1+k))
      = seamWordSupport (seamGreedyWord (D+1)) ∪ Finset.Ico (D+1) (D+1+k)`

(`rightTail_support_eq`).  Every cofactor rank of row `s` is at least `(s+1)/2`,
so once `s ≥ 2*D+1` the whole of `cofRanks s` lies inside the free block and is
therefore selected (`rightTail_cofRanks_subset`).  Two consequences follow
from `hright`:

* `rightTail_not_cofinal_cofSkip` — under `hright` there is no cofinal family of
  rows skipping a cofactor rank: all skips happen inside the finite window
  `[D+1, 2*D]`.  This makes the particular sufficient route
  `half_mem_of_cofinal_cofSkip` unavailable.  It does not refute half-value
  membership.  The explicit eventual-subset threshold `2*D+1` also comes after
  the three rows `D+1, D+2, D+3` consumed by the ratchet.

* `rightTail_landingExcess_two_impossible` — **a conditional incompatibility.**
  If the seam has an all-right tail from `D₀+1` and a row `D+1` satisfies the
  auxiliary landing equation, then `D < 2*D₀`.  This removes `hcof`; it does not
  remove `hright` or the uninstantiated landing equation.

## What the branch forces at the landing row

The first two steps of the affine excess orbit are rigid.  Positivity at rows
`D+2` and `D+3` pins the landing below-pulse:

* `rightTail_landing_belowPulse_le_two` — `belowPulse (D+1) ≤ 2`;
* `rightTail_landing_pulseFloor_le_two` — hence `pulseFloor (D+1) ≤ 2`, an
  explicit congruence obstruction on `D` mod `2730`;
* `rightTail_landing_cofSkip` — formally, whenever `cofFloor (D+1) ≥ 2` (that is
  `(D+1) % 6 ∈ {1, 4, 5}`, i.e. `D ≡ 0, 3, 4 (mod 6)`), the cofactor ranks at
  the landing row are skipped; however, `Skip/verify/V9.lean` proves that this
  residue sub-branch is contradictory;
* `rightTail_frozen_skipped_rank` — in that same contradictory sub-branch, the
  conclusion supplies an explicit
  `d` with `D+1 ≤ 2*d` and `d ≤ D` that is missing from the support of *every*
  row of the tail.

The bound `belowPulse (D+1) ≤ 2` is a bound on the pulse of the whole support,
so it freezes far more than the cofactor ranks:

* `rightTail_frozen_skip_of_dvd` — **every** divisor of `2*D+3` that is at most
  `D` and is not one of the odd forced ranks `3, 7, 21` is missing from the
  support of every row of the tail (a divisor of `2*D+3` has row pulse `2`, and
  the certified floor already spends one of the two available units);
* `rightTail_frozen_skip_pair` — among any two distinct non-forced ranks of
  positive landing pulse, at least one is permanently skipped.

The unrestricted permanent-skip implications remain conditional on `hright`
and `hlanding`.  The special claims for `D ≡ 0 (mod 3)` and
`D % 6 ∈ {0,3,4}` are vacuous by `Skip/verify/V9.lean`; they should not be read
as observed failures of a live certificate.
-/

namespace Erdos249257

namespace Wire3

open HalfCylinderIntegerGreedy
open Filter
open scoped BigOperators

/-! ## The frozen-support law of an all-right tail -/

/-- Under an all-right tail from `D+1`, the support of row `D+1+k` is exactly
the frozen landing support together with the free block `[D+1, D+1+k)`. -/
theorem rightTail_support_eq (D : ℕ) (hD : 2 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (k : ℕ) :
    seamWordSupport (seamGreedyWord (D + 1 + k)) =
      seamWordSupport (seamGreedyWord (D + 1)) ∪ Finset.Ico (D + 1) (D + 1 + k) := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : seamGreedyWord (D + 1 + k + 1) =
          (seamGreedyWord (D + 1 + k)).extend true := hright _ (by omega)
      have hidx : D + 1 + (k + 1) = (D + 1 + k) + 1 := by ring
      rw [hidx, hstep, seamWordSupport_extend_true (by omega : 3 ≤ D + 1 + k), ih]
      ext d
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_Ico]
      constructor
      · rintro (rfl | hS | hI)
        · exact Or.inr ⟨by omega, by omega⟩
        · exact Or.inl hS
        · exact Or.inr ⟨hI.1, by omega⟩
      · rintro (hS | hI)
        · exact Or.inr (Or.inl hS)
        · by_cases h : d = D + 1 + k
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨hI.1, by omega⟩)

/-- Every rank of the free block is selected at every later row. -/
theorem rightTail_mem_support (D : ℕ) (hD : 2 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {r s : ℕ} (hr : D + 1 ≤ r) (hrs : r < s) :
    r ∈ seamWordSupport (seamGreedyWord s) := by
  obtain ⟨k, hk⟩ : ∃ k, s = D + 1 + k := ⟨s - (D + 1), by omega⟩
  subst hk
  rw [rightTail_support_eq D hD hright k]
  exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨hr, hrs⟩)

/-- Ranks outside the free block keep their landing value for ever. -/
theorem rightTail_not_mem_support (D : ℕ) (hD : 2 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {d : ℕ} (hd : d ≤ D) (hdns : d ∉ seamWordSupport (seamGreedyWord (D + 1)))
    {s : ℕ} (hs : D + 1 ≤ s) :
    d ∉ seamWordSupport (seamGreedyWord s) := by
  obtain ⟨k, hk⟩ : ∃ k, s = D + 1 + k := ⟨s - (D + 1), by omega⟩
  subst hk
  rw [rightTail_support_eq D hD hright k]
  simp only [Finset.mem_union, Finset.mem_Ico, not_or, not_and, not_lt]
  exact ⟨hdns, fun h => by omega⟩

/-! ## The cofactor certificate is free above `2 * D + 1` -/

/-- Every cofactor rank of row `s` is at least half the row, hence lies in the
free block as soon as `s ≥ 2*D+1`. -/
theorem cofRanks_ge_half (s : ℕ) (_hs : 3 ≤ s) {d : ℕ} (hd : d ∈ AngleB2.cofRanks s) :
    s ≤ 2 * d := by
  rcases AngleB2.cofRanks_cases hd with rfl | rfl | rfl <;> omega

/-- **The all-right tail certifies its own cofactor ranks from row `2*D+1` on.**
No hypothesis beyond the tail. -/
theorem rightTail_cofRanks_subset (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s : ℕ} (hs : 2 * D + 1 ≤ s) :
    AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  intro d hd
  have hlt : d < s := AngleB2.cofRanks_lt s (by omega) hd
  have hge : D + 1 ≤ d := by
    have := cofRanks_ge_half s (by omega) hd
    omega
  exact rightTail_mem_support D (by omega) hright hge hlt

/-- **PROVED, CONDITIONAL.**  Under an all-right tail, rows at which a cofactor
rank is skipped are confined to the finite window `[D+1, 2*D]`.  Thus there is
no cofinal family of skips and the sufficient route
`half_mem_mersenneAchievementSet_of_unboundedSkippedRanks` is unavailable. -/
theorem rightTail_not_cofinal_cofSkip (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ¬ ∀ S : ℕ, ∃ s : ℕ, S ≤ s ∧
        ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  intro h
  obtain ⟨s, hs, hns⟩ := h (2 * D + 1)
  exact hns (rightTail_cofRanks_subset D hD hright hs)

/-- The same statement positively: every skip row of an all-right tail lies
below `2 * D + 1`. -/
theorem rightTail_cofSkip_lt (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    {s : ℕ} (hns : ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) :
    s < 2 * D + 1 := by
  by_contra h
  exact hns (rightTail_cofRanks_subset D hD hright (by omega))

/-! ## Conditional incompatibility far out in the tail -/

/-- **PROVED, CONDITIONAL.**  If the concrete seam greedy has an all-right tail
from row `D₀ + 1`, then no row `D + 1` with `D ≥ 2 * D₀` can also satisfy the
auxiliary landing equation.  This removes `hcof`, but still assumes the
all-right tail and derives its contradiction only after `hlanding` is supplied.
-/
theorem rightTail_landingExcess_two_impossible (D₀ : ℕ) (hD₀ : 60 ≤ D₀)
    (hright : ∀ s : ℕ, D₀ + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (D : ℕ) (hD : 2 * D₀ ≤ D)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    False := by
  refine AngleB2.allRight_landingExcess_two_impossible D (by omega)
    (fun s hs => hright s (by omega)) hlanding ?_
  intro s hs1 _
  exact rightTail_cofRanks_subset D₀ hD₀ hright (by omega)

/-- **PROVED, CONDITIONAL.**  A row satisfying the auxiliary landing equation
forces any assumed all-right tail to start above its half. -/
theorem allRight_tailStart_gt_half (D₀ D : ℕ) (hD₀ : 60 ≤ D₀)
    (hright : ∀ s : ℕ, D₀ + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    D < 2 * D₀ := by
  by_contra h
  exact rightTail_landingExcess_two_impossible D₀ hD₀ hright D (by omega) hlanding

/-- **PROVED, CONDITIONAL.**  Restated as a producer-location implication:
given the auxiliary landing equation at `D+1` and `2 * D₀ ≤ D`, some row at or
above `D₀ + 1` takes an upper or middle branch. -/
theorem allRight_producer_above (D₀ D : ℕ) (hD₀ : 60 ≤ D₀) (hD : 2 * D₀ ≤ D)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ s : ℕ, ∃ hs5 : 5 ≤ s, D₀ + 1 ≤ s ∧ SeamGreedyUpperOrMiddleAt s hs5 := by
  by_contra h
  refine rightTail_landingExcess_two_impossible D₀ hD₀ (fun s hs => ?_) D hD hlanding
  have hs5 : 5 ≤ s := by omega
  have hUM : ¬ SeamGreedyUpperOrMiddleAt s hs5 := fun hUM => h ⟨s, hs5, hs, hUM⟩
  by_cases hb : SeamRowWord.terminal (show 3 ≤ s by omega) (seamGreedyWord (s + 1)) = true
  · exact (seamGreedyWord_succ_eq_extend_true_iff_terminal_true s hs5).2 hb
  · exact absurd ((seamGreedy_terminal_false_iff_upperOrMiddle s hs5).1
      (by simpa using hb)) hUM

/-! ## What the branch forces at the landing row -/

/-- **PROVED, CONDITIONAL.**  Under `hright` and the auxiliary landing equation,
positivity of the affine excess orbit at the next two rows bounds the landing
below-pulse by `2`. -/
theorem rightTail_landing_belowPulse_le_two (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    (seamAdjacentCut (D + 1) (by omega : 5 ≤ D + 1)).belowPulse ≤ 2 := by
  have horbit := eventualRightTail_positive_affineExcess
    (S := D + 1) (by omega) hright
  have hrec1 : Recon257.seamExcess (D + 1 + 1) =
      4 * Recon257.seamExcess (D + 1) -
        ((seamAdjacentCut (D + 1) (by omega : 5 ≤ D + 1)).belowPulse : ℤ) - 4 := by
    simpa [Recon257.seamExcess] using (horbit (D + 1) le_rfl).2
  have hrec2 : Recon257.seamExcess (D + 1 + 1 + 1) =
      4 * Recon257.seamExcess (D + 1 + 1) -
        ((seamAdjacentCut (D + 1 + 1)
          (by omega : 5 ≤ D + 1 + 1)).belowPulse : ℤ) - 4 := by
    simpa [Recon257.seamExcess] using (horbit (D + 1 + 1) (by omega)).2
  have hpos3 : 0 < Recon257.seamExcess (D + 1 + 1 + 1) := by
    simpa [Recon257.seamExcess] using (horbit (D + 1 + 1 + 1) (by omega)).1
  have hfl : 1 ≤ (seamAdjacentCut (D + 1 + 1)
      (by omega : 5 ≤ D + 1 + 1)).belowPulse := by
    have h1 := Recon257.one_le_pulseFloor (D + 1 + 1)
    have h2 := Recon257.pulseFloor_le_belowPulse (D + 1 + 1) (by omega)
    omega
  have hflZ : (1 : ℤ) ≤ ((seamAdjacentCut (D + 1 + 1)
      (by omega : 5 ≤ D + 1 + 1)).belowPulse : ℤ) := by exact_mod_cast hfl
  have hnn : (0 : ℤ) ≤ ((seamAdjacentCut (D + 1)
      (by omega : 5 ≤ D + 1)).belowPulse : ℤ) := Int.natCast_nonneg _
  rw [hlanding] at hrec1
  have hgoal : ((seamAdjacentCut (D + 1)
      (by omega : 5 ≤ D + 1)).belowPulse : ℤ) ≤ 2 := by omega
  exact_mod_cast hgoal

/-- **PROVED, CONDITIONAL.**  Under the same assumptions, the forced pulse
floor at the landing row is at most `2`. -/
theorem rightTail_landing_pulseFloor_le_two (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    Recon257.pulseFloor (D + 1) ≤ 2 :=
  le_trans (Recon257.pulseFloor_le_belowPulse (D + 1) (by omega))
    (rightTail_landing_belowPulse_le_two D hD hright hlanding)

/-- The cofactor floor is at least `2` exactly on the residues `1, 4, 5` mod
`6`. -/
theorem two_le_cofFloor (s : ℕ) (h : s % 6 = 1 ∨ s % 6 = 4 ∨ s % 6 = 5) :
    2 ≤ AngleB2.cofFloor s := by
  unfold AngleB2.cofFloor
  split_ifs <;> omega

/-- **PROVED VACUOUS.**  The conclusion says that if the landing row also has
cofactor floor `≥ 2`, then its cofactor ranks are not all selected.
`Skip/verify/V9.cofFloor_branch_vacuous` proves that `hright`, `hlanding`, and
this cofactor-floor hypothesis are mutually inconsistent, so this theorem does
not exhibit a skipped rank on a live branch. -/
theorem rightTail_landing_cofSkip (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (hcf : 2 ≤ AngleB2.cofFloor (D + 1)) :
    ¬ AngleB2.cofRanks (D + 1) ⊆ seamWordSupport (seamGreedyWord (D + 1)) := by
  intro hcof
  have h := AngleB2.totalFloor_le_belowPulse (D + 1) (by omega) hcof
  have hb := rightTail_landing_belowPulse_le_two D hD hright hlanding
  have h1 := Recon257.one_le_pulseFloor (D + 1)
  unfold AngleB2.totalFloor at h
  omega

/-- **PROVED VACUOUS.**  Under the same inconsistent hypothesis block as
`rightTail_landing_cofSkip`, the conclusion supplies a rank `d` in the upper
half of the frozen block that is absent from every later support. -/
theorem rightTail_frozen_skipped_rank (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (hcf : 2 ≤ AngleB2.cofFloor (D + 1)) :
    ∃ d : ℕ, D + 1 ≤ 2 * d ∧ d ≤ D ∧
      ∀ s : ℕ, D + 1 ≤ s → d ∉ seamWordSupport (seamGreedyWord s) := by
  classical
  have hns := rightTail_landing_cofSkip D hD hright hlanding hcf
  rw [Finset.not_subset] at hns
  obtain ⟨d, hd, hdns⟩ := hns
  have hlt : d < D + 1 := AngleB2.cofRanks_lt (D + 1) (by omega) hd
  have hhalf : D + 1 ≤ 2 * d := by
    have := cofRanks_ge_half (D + 1) (by omega) hd
    omega
  exact ⟨d, hhalf, by omega,
    fun s hs => rightTail_not_mem_support D (by omega) hright (by omega) hdns hs⟩

/-! ### Every resonant rank of the landing row is permanently skipped

The landing bound `belowPulse (D+1) ≤ 2` is a bound on the pulse of the *whole*
support, not just of the cofactor ranks.  Since the eight forced ranks already
spend at least one unit, no other rank of the landing row can afford a pulse of
two — and a rank of pulse two is exactly a divisor of `2*D+3`. -/

/-- The eight forced ranks lie in the greedy support at every row `s ≥ 27`. -/
theorem forcedRanks_subset (s : ℕ) (hs : 27 ≤ s) :
    ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ⊆ seamWordSupport (seamGreedyWord s) := by
  have h236 := two_three_six_mem_seamGreedySupport s (by omega)
  have h7 := seven_mem_seamGreedySupport s (by omega)
  have h14 := fourteen_mem_seamGreedySupport s (by omega)
  have h20 := twenty_mem_seamGreedySupport s (by omega)
  have h21 := twentyOne_mem_seamGreedySupport s (by omega)
  have h26 := twentySix_mem_seamGreedySupport s (by omega)
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

/-- A selected rank outside the eight forced ranks adds its own row pulse on top
of the certified floor. -/
theorem pulseFloor_add_rowPulse_le_belowPulse (s : ℕ) (hs : 27 ≤ s) {d : ℕ}
    (hdnot : d ∉ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ))
    (hmem : d ∈ seamWordSupport (seamGreedyWord s)) :
    Recon257.pulseFloor s + rowPulse s d ≤
      (seamAdjacentCut s (by omega : 5 ≤ s)).belowPulse := by
  classical
  have hdisj : Disjoint ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ({d} : Finset ℕ) := by
    simp only [Finset.disjoint_singleton_right]
    exact hdnot
  have hsub : (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ {d}) ⊆
      seamWordSupport (seamGreedyWord s) :=
    Finset.union_subset (forcedRanks_subset s hs)
      (by simpa using hmem)
  have hsum :
      ∑ e ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ {d}), rowPulse s e ≤
        ∑ e ∈ seamWordSupport (seamGreedyWord s), rowPulse s e :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  have hsplit :
      ∑ e ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ {d}), rowPulse s e =
        (∑ e ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s e) +
          rowPulse s d := by
    rw [Finset.sum_union hdisj, Finset.sum_singleton]
  have hexp : ∑ e ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s e =
      Recon257.pulseFloor s := by
    rw [Recon257.pulseFloor_eq_rowPulseSum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  change Recon257.pulseFloor s + rowPulse s d ≤
    wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  rw [hsplit, hexp] at hsum
  omega

/-- Two selected ranks outside the eight forced ranks both add their row pulse
on top of the certified floor. -/
theorem pulseFloor_add_two_rowPulse_le_belowPulse (s : ℕ) (hs : 27 ≤ s) {d e : ℕ}
    (hde : d ≠ e)
    (hdnot : d ∉ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ))
    (henot : e ∉ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ))
    (hdmem : d ∈ seamWordSupport (seamGreedyWord s))
    (hemem : e ∈ seamWordSupport (seamGreedyWord s)) :
    Recon257.pulseFloor s + rowPulse s d + rowPulse s e ≤
      (seamAdjacentCut s (by omega : 5 ≤ s)).belowPulse := by
  classical
  have hdisj : Disjoint ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ)
      (({d, e} : Finset ℕ)) := by
    rw [Finset.disjoint_right]
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hdnot
    · exact henot
  have hsub : (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ ({d, e} : Finset ℕ)) ⊆
      seamWordSupport (seamGreedyWord s) := by
    refine Finset.union_subset (forcedRanks_subset s hs) ?_
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hdmem
    · exact hemem
  have hsum :
      ∑ a ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ ({d, e} : Finset ℕ)),
          rowPulse s a ≤
        ∑ a ∈ seamWordSupport (seamGreedyWord s), rowPulse s a :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  have hpair : ∑ a ∈ ({d, e} : Finset ℕ), rowPulse s a =
      rowPulse s d + rowPulse s e := by
    rw [Finset.sum_insert (by simpa using hde), Finset.sum_singleton]
  have hsplit :
      ∑ a ∈ (({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) ∪ ({d, e} : Finset ℕ)),
          rowPulse s a =
        (∑ a ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s a) +
          (rowPulse s d + rowPulse s e) := by
    rw [Finset.sum_union hdisj, hpair]
  have hexp : ∑ a ∈ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ), rowPulse s a =
      Recon257.pulseFloor s := by
    rw [Recon257.pulseFloor_eq_rowPulseSum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  change Recon257.pulseFloor s + rowPulse s d + rowPulse s e ≤
    wordPulse s (seamGreedyWord s).toNatWord
  rw [wordPulse_eq_sum_seamWordSupport]
  rw [hsplit, hexp] at hsum
  omega

/-- **PROVED, CONDITIONAL.**  Under `hright` and the auxiliary landing equation,
any rank `d ≤ D` outside the eight forced ranks whose landing row pulse would
push the certified floor past `2` is skipped at the landing row and every later
row of the tail. -/
theorem rightTail_frozen_skip (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    {d : ℕ} (hdle : d ≤ D)
    (hdnot : d ∉ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ))
    (hbig : 3 ≤ Recon257.pulseFloor (D + 1) + rowPulse (D + 1) d) :
    ∀ s : ℕ, D + 1 ≤ s → d ∉ seamWordSupport (seamGreedyWord s) := by
  have hlandingNot : d ∉ seamWordSupport (seamGreedyWord (D + 1)) := by
    intro hmem
    have h := pulseFloor_add_rowPulse_le_belowPulse (D + 1) (by omega) hdnot hmem
    have hb := rightTail_landing_belowPulse_le_two D hD hright hlanding
    omega
  exact fun s hs => rightTail_not_mem_support D (by omega) hright hdle hlandingNot hs

/-- **PROVED, CONDITIONAL.**  Under `hright` and the auxiliary landing equation,
every divisor of `2*D+3` below the landing row is permanently skipped, apart
from the forced ranks.  Such a divisor has row pulse `2`, and the certified
floor already spends one unit of the conditional total bound `2`. -/
theorem rightTail_frozen_skip_of_dvd (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    {d : ℕ} (hdvd : d ∣ 2 * D + 3) (hdle : d ≤ D)
    (hdnot : d ∉ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ)) :
    ∀ s : ℕ, D + 1 ≤ s → d ∉ seamWordSupport (seamGreedyWord s) := by
  refine rightTail_frozen_skip D hD hright hlanding hdle hdnot ?_
  have h1 := Recon257.one_le_pulseFloor (D + 1)
  have hdv : d ∣ 2 * (D + 1) + 1 := by
    have he : 2 * (D + 1) + 1 = 2 * D + 3 := by ring
    rw [he]; exact hdvd
  have hp : 2 ≤ rowPulse (D + 1) d := by
    simp only [rowPulse, if_pos hdv]
    split_ifs <;> omega
  omega

/-- **PROVED VACUOUS.**  The conclusion specializes the previous theorem to the
cofactor-`3` rank when `D ≡ 0 (mod 3)`.
`Skip/verify/V9.mod_three_branch_vacuous` proves that this residue hypothesis is
incompatible with `hright` and `hlanding`. -/
theorem rightTail_frozen_skip_cofactorThree (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    (h3 : D % 3 = 0) :
    ∀ s : ℕ, D + 1 ≤ s →
      (2 * D + 3) / 3 ∉ seamWordSupport (seamGreedyWord s) := by
  refine rightTail_frozen_skip_of_dvd D hD hright hlanding ⟨3, by omega⟩ (by omega) ?_
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **PROVED, CONDITIONAL.**  Under `hright` and the auxiliary landing equation,
if two distinct non-forced ranks below the landing row both have positive row
pulse, then at least one is permanently skipped by the whole tail. -/
theorem rightTail_frozen_skip_pair (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2)
    {d e : ℕ} (hde : d ≠ e) (hdle : d ≤ D) (hele : e ≤ D)
    (hdnot : d ∉ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ))
    (henot : e ∉ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ))
    (hdp : 1 ≤ rowPulse (D + 1) d) (hep : 1 ≤ rowPulse (D + 1) e) :
    (∀ s : ℕ, D + 1 ≤ s → d ∉ seamWordSupport (seamGreedyWord s)) ∨
      ∀ s : ℕ, D + 1 ≤ s → e ∉ seamWordSupport (seamGreedyWord s) := by
  classical
  by_cases hd : d ∈ seamWordSupport (seamGreedyWord (D + 1))
  · right
    intro s hs
    have hlandingNot : e ∉ seamWordSupport (seamGreedyWord (D + 1)) := by
      intro he
      have h := pulseFloor_add_two_rowPulse_le_belowPulse (D + 1) (by omega)
        hde hdnot henot hd he
      have hb := rightTail_landing_belowPulse_le_two D hD hright hlanding
      have h1 := Recon257.one_le_pulseFloor (D + 1)
      omega
    exact rightTail_not_mem_support D (by omega) hright hele hlandingNot hs
  · exact Or.inl fun s hs =>
      rightTail_not_mem_support D (by omega) hright hdle hd hs

/-- **PROVED VACUOUS.**  This residue form has an inconsistent hypothesis block;
see `Skip/verify/V9.residue_branch_vacuous`. -/
theorem rightTail_frozen_skipped_rank_of_residue (D : ℕ) (hD : 60 ≤ D)
    (hres : D % 6 = 0 ∨ D % 6 = 3 ∨ D % 6 = 4)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    ∃ d : ℕ, D + 1 ≤ 2 * d ∧ d ≤ D ∧
      ∀ s : ℕ, D + 1 ≤ s → d ∉ seamWordSupport (seamGreedyWord s) :=
  rightTail_frozen_skipped_rank D hD hright hlanding
    (two_le_cofFloor (D + 1) (by omega))

/-! ## The cofactor dichotomy and its limited content here

The dichotomy is a classical logical exhaustion: either cofactor skips are
cofinal, which implies half-value membership, or they are eventually absent.
It does not decide which alternative holds.  Under `hright`, the cofinal-skip
hypothesis is false and the eventual-subset alternative has an explicit
threshold; that threshold is too late for AngleB2's first three rows. -/

/-- A failure of the cofactor certificate at row `s` is an explicit false seam
coordinate whose rank is at least `s / 2`. -/
theorem exists_skipped_bit_of_not_subset {s : ℕ} (hs : 61 ≤ s)
    (hns : ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) :
    ∃ i : Fin (s - 2), seamGreedyWord s i = false ∧ s ≤ 2 * ((i : ℕ) + 2) := by
  classical
  rw [Finset.not_subset] at hns
  obtain ⟨d, hd, hdns⟩ := hns
  have hlt : d < s := AngleB2.cofRanks_lt s hs hd
  have hge : 27 ≤ d := AngleB2.cofRanks_ge s hs hd
  have hhalf : s ≤ 2 * d := cofRanks_ge_half s (by omega) hd
  refine ⟨⟨d - 2, by omega⟩, ?_, show s ≤ 2 * ((d - 2) + 2) by omega⟩
  by_contra hb
  have htrue : seamGreedyWord s ⟨d - 2, by omega⟩ = true := by
    cases h : seamGreedyWord s ⟨d - 2, by omega⟩ with
    | false => exact absurd h hb
    | true => rfl
  exact hdns (mem_seamWordSupport_iff.mpr
    ⟨⟨d - 2, by omega⟩, htrue, show d = (d - 2) + 2 by omega⟩)

/-- Cofinally many cofactor skips give the half membership. -/
theorem half_mem_of_cofinal_cofSkip
    (hskip : ∀ S : ℕ, ∃ s : ℕ, S ≤ s ∧
      ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  have hchoice : ∀ j : ℕ, ∃ s : ℕ, 61 + j ≤ s ∧
      ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := fun j => hskip (61 + j)
  choose rows hrowsBig hrowsSkip using hchoice
  have hidx : ∀ j : ℕ, ∃ i : Fin (rows j - 2),
      seamGreedyWord (rows j) i = false ∧ rows j ≤ 2 * ((i : ℕ) + 2) := by
    intro j
    exact exists_skipped_bit_of_not_subset (by have := hrowsBig j; omega) (hrowsSkip j)
  choose skip hskipFalse hskipBig using hidx
  refine half_mem_mersenneAchievementSet_of_unboundedSkippedRanks rows
    ⟨skip, ?_, ?_, hskipFalse⟩
  · refine tendsto_atTop.2 fun B => ?_
    filter_upwards [eventually_ge_atTop B] with j hj
    have := hrowsBig j
    omega
  · refine tendsto_atTop.2 fun B => ?_
    filter_upwards [eventually_ge_atTop (2 * B)] with j hj
    have h1 := hrowsBig j
    have h2 := hskipBig j
    omega

/-- **PROVED:** a classical cofactor dichotomy.  The theorem does not decide
which disjunct holds. -/
theorem half_mem_or_eventually_cofRanks_subset :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S : ℕ, ∀ s : ℕ, S ≤ s →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) := by
  classical
  by_cases h : ∀ S : ℕ, ∃ s : ℕ, S ≤ s ∧
      ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)
  · exact Or.inl (half_mem_of_cofinal_cofSkip h)
  · right
    obtain ⟨S, hS⟩ := not_forall.mp h
    refine ⟨S, fun s hs => ?_⟩
    by_contra hc
    exact hS ⟨s, hs, hc⟩

/-- **PROVED, CONDITIONAL.**  Under an all-right tail, cofactor skips are not
cofinal and the eventual-subset alternative holds with threshold `2 * D + 1`.
This threshold is after the three rows `D+1`, `D+2`, `D+3` consumed by
AngleB2, so it does not discharge AngleB2's `hcof`. -/
theorem rightTail_eventually_cofRanks_subset_explicit (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (∀ s : ℕ, 2 * D + 1 ≤ s →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) ∧
      ¬ ∀ S : ℕ, ∃ s : ℕ, S ≤ s ∧
          ¬ AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s) :=
  ⟨fun _ hs => rightTail_cofRanks_subset D hD hright hs,
    rightTail_not_cofinal_cofSkip D hD hright⟩

/-! ## The wiring -/

/-- **PROVED, CONDITIONAL; not a branch resolution.**  Under `hright` and the
auxiliary `hlanding` equation, the theorem packages:

1.  The landing below-pulse is at most `2`.
2.  The cofactor certificate holds automatically from row `2*D+1` on, so every
    cofactor skip of the tail lies in the finite window `[D+1, 2*D]`.
3.  Consequently no row `D' + 1` with `D' ≥ 2*D` can carry landing excess `2`.
4.  Every divisor of `2*D+3` below the landing row, other than the odd forced
    ranks `3, 7, 21`, is skipped by *every* row of the tail.
5.  A final implication from `cofFloor ≥ 2`; its antecedent is incompatible
    with the main hypotheses by `Skip/verify/V9.cofFloor_branch_vacuous`.

The historical theorem name is retained for compatibility.  The result does
not resolve the all-right branch or decide Erdős #257. -/
theorem allRight_branch_resolved (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hlanding : Recon257.seamExcess (D + 1) = 2) :
    (seamAdjacentCut (D + 1) (by omega : 5 ≤ D + 1)).belowPulse ≤ 2 ∧
      (∀ s : ℕ, 2 * D + 1 ≤ s →
        AngleB2.cofRanks s ⊆ seamWordSupport (seamGreedyWord s)) ∧
      (∀ D' : ℕ, 2 * D ≤ D' → Recon257.seamExcess (D' + 1) ≠ 2) ∧
      (∀ d : ℕ, d ∣ 2 * D + 3 → d ≤ D →
        d ∉ ({2, 3, 6, 7, 14, 20, 21, 26} : Finset ℕ) →
        ∀ s : ℕ, D + 1 ≤ s → d ∉ seamWordSupport (seamGreedyWord s)) ∧
      (2 ≤ AngleB2.cofFloor (D + 1) →
        ∃ d : ℕ, D + 1 ≤ 2 * d ∧ d ≤ D ∧
          ∀ s : ℕ, D + 1 ≤ s → d ∉ seamWordSupport (seamGreedyWord s)) := by
  refine ⟨rightTail_landing_belowPulse_le_two D hD hright hlanding,
    fun _ hs => rightTail_cofRanks_subset D hD hright hs, ?_, ?_, ?_⟩
  · intro D' hD' hl'
    exact rightTail_landingExcess_two_impossible D hD hright D' hD' hl'
  · intro d hdvd hdle hdnot
    exact rightTail_frozen_skip_of_dvd D hD hright hlanding hdvd hdle hdnot
  · intro hcf
    exact rightTail_frozen_skipped_rank D hD hright hlanding hcf

/-- **PROVED, BUT NON-DECISIVE.**  This pairs the classical cofactor dichotomy
with the conditional AngleB2 implication.  The theorem neither decides
half-value membership nor supplies a satisfiable landing row.  In the audited
range, `Recon257.seamExcess s = 2` has no instance for `s ∈ [5,102]`. -/
theorem half_mem_or_allRight_landingExcess_two_impossible :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S : ℕ, 60 ≤ S ∧ ∀ D : ℕ, S ≤ D →
        (∀ s : ℕ, D + 1 ≤ s →
          seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) →
        Recon257.seamExcess (D + 1) = 2 → False := by
  rcases half_mem_or_eventually_cofRanks_subset with h | ⟨S, hS⟩
  · exact Or.inl h
  · refine Or.inr ⟨max 60 S, le_max_left _ _, ?_⟩
    intro D hD hright hlanding
    have h60 : 60 ≤ D := le_trans (le_max_left 60 S) hD
    have hSD : S ≤ D := le_trans (le_max_right 60 S) hD
    exact AngleB2.allRight_landingExcess_two_impossible D h60 hright hlanding
      (fun s hs _ => hS s (by omega))

end Wire3

end Erdos249257
