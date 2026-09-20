import Erdos249257.HalfTrappingReturnCarry
import Erdos249257.HalfCylinderFinalMiddleCellEscape
import Erdos249257.HalfCylinderMiddleCarryLowerBound

/-!
Paper-form restatements of three environments of the long Erdős #257
manuscript `paper/reasoning-parts/erdos257/a257_front.tex`:

* `record:257bm-k9` (line 5234), "Vanishing of the specified linear-channel
  determinant";
* `record:257hg-k12` (line 5269), "Excluding the cell with value minus three";
* the untitled proposition at line 5298, "The unsafe middle range is exactly
  three integers".

Every quantity is the paper's.  The signed middle coordinate is
`C_s = 4 rem(s) - p_s^- - 4`, where `rem(s)` is the adjacent-cut remainder and
`p_s^-` is its below pulse.

The determinant row is stated here without the tree's auxiliary hypothesis
`∃ e, ev e = 1`: the paper assumes only that the channels vanish on `ker e`,
and the degenerate case `ev = 0` is discharged separately below.
-/

set_option autoImplicit false

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.HalfTrappingReturnCarry
open Erdos249257.HalfCylinderIntegerGreedy Erdos249257.HalfCarryReachability

/-! ## `record:257bm-k9`: the linear-channel determinant -/

/-- Long `record:257bm-k9`, rank clause.  Over `ℚ`, if every functional
`channel j` vanishes on `ker ev`, then the matrix `(channel j (row i))` has
rank at most one: it factors as `u i * w j`.  No hypothesis on `ev` beyond
linearity is used, so the degenerate case `ev = 0` is included. -/
theorem paper_relationInvariant_channels_rank_le_one
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (row : ι → V) :
    ∃ u w : ι → ℚ, ∀ i j : ι, channel j (row i) = u i * w j := by
  classical
  by_cases he : ∃ e : V, ev e = 1
  · choose c hc using fun j : ι =>
      Erdos249257.AdelicHeightObstruction.linearDescender_eq_smul_eval
        ev (channel j) (hker j) he
    refine ⟨fun i => ev (row i), c, fun i j => ?_⟩
    rw [hc j (row i)]
    simp [smul_eq_mul]
  · have hzero : ∀ j : ι, ∀ v : V, channel j v = 0 := by
      intro j v
      have hev : ev v = 0 := by
        by_contra hne
        refine he ⟨(ev v)⁻¹ • v, ?_⟩
        rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne]
      exact LinearMap.mem_ker.mp (hker j (LinearMap.mem_ker.mpr hev))
    exact ⟨0, 0, fun i j => by simp [hzero j (row i)]⟩

/-- Long `record:257bm-k9`, determinant clause.  Every square minor of size at
least two vanishes: the statement is universally quantified over the finite
index type, so it applies at every matrix size. -/
theorem paper_relationInvariant_channels_det_eq_zero
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    [Nontrivial ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (row : ι → V) :
    Matrix.det (fun i j : ι => channel j (row i)) = 0 := by
  obtain ⟨u, w, huw⟩ :=
    paper_relationInvariant_channels_rank_le_one ev channel hker row
  have hmat : (fun i j : ι => channel j (row i)) = Matrix.vecMulVec u w := by
    ext i j
    simp [Matrix.vecMulVec, huw i j]
  rw [hmat]
  exact Matrix.det_vecMulVec _ _

/-! ## The untitled proposition at line 5298: the unsafe middle range -/

/-- Long untitled proposition (line 5298).  For `s ≥ 5`, the complement of the
two safe integer ranges for the signed middle coordinate `4R - P - 4` is
exactly `{-3, -2, -1}`. -/
theorem paper_unsafe_middle_range_is_three_integers {s : ℕ} (hs : 5 ≤ s) :
    ¬ (4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≤ -4 ∨
          0 ≤ 4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4) ↔
      4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -3 ∨
        4 * ((seamAdjacentCut s hs).remainder : ℤ) -
              ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -2 ∨
          4 * ((seamAdjacentCut s hs).remainder : ℤ) -
              ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -1 :=
  seamMiddleCoordinate_not_safe_iff_three_cells hs

/-! ## `record:257hg-k12`: excluding the cell with value minus three -/

/-- Long `record:257hg-k12`, main clause.  At a middle row `D ≥ 13` followed
only by right transitions, the signed middle coordinate is never `-3`. -/
theorem paper_final_middle_cell_ne_neg_three
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
        ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ≠ -3 :=
  fun hcell => finalMiddleCell_neg_three_not_last D hD13 hncarry hmiddle hright hcell

/-- Long `record:257hg-k12`, residual clause.  With `-3` excluded under the
all-right-tail hypothesis, the values `-2` and `-1` remain among the three
exceptional negative cells, and the nonnegative range of the coordinate is
untouched. -/
theorem paper_final_middle_cell_remaining_negative_values
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ≤ -4 ∨
      0 ≤ 4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ∨
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2 ∨
        4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -1 := by
  have hne := paper_final_middle_cell_ne_neg_three D hD13 hncarry hmiddle hright
  by_cases hsafe :
      4 * ((seamAdjacentCut D (by omega : (5 : ℕ) ≤ D)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega : (5 : ℕ) ≤ D)).belowPulse : ℤ) - 4 ≤ -4 ∨
        0 ≤ 4 * ((seamAdjacentCut D (by omega : (5 : ℕ) ≤ D)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega : (5 : ℕ) ≤ D)).belowPulse : ℤ) - 4
  · rcases hsafe with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have h3 :=
      (seamMiddleCoordinate_not_safe_iff_three_cells
        (s := D) (by omega : (5 : ℕ) ≤ D)).1 hsafe
    rcases h3 with h | h | h
    · exact absurd h hne
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- Long `record:257hg-k12`, the paired centred-carry recurrence named as the
proof input: two centred half-carry steps combine into one base-four step. -/
theorem paper_mobiusCenteredHalfCarry_add_two (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N :=
  mobiusCenteredHalfCarry_add_two A N

/-- Long `record:257hg-k12`, the nonnegative-centred-carry input for a
completed support: if every rank after `D` is selected and the support value is
strictly below one half, the centred endpoint at row `2D+1` is nonzero. -/
theorem paper_cofiniteRightTail_ne_zero_centeredEndpoint
    (A : Set ℕ) (D : ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (hcofinite : Set.Ioi D ⊆ A) :
    mobiusCenteredHalfCarry A (2 * D + 1) ≠ 0 :=
  cofiniteRightTail_ne_zero_centeredEndpoint A D hone hseries hcofinite

#print axioms paper_relationInvariant_channels_rank_le_one
#print axioms paper_relationInvariant_channels_det_eq_zero
#print axioms paper_unsafe_middle_range_is_three_integers
#print axioms paper_final_middle_cell_ne_neg_three
#print axioms paper_final_middle_cell_remaining_negative_values
#print axioms paper_mobiusCenteredHalfCarry_add_two
#print axioms paper_cofiniteRightTail_ne_zero_centeredEndpoint
#print axioms Erdos249257.HalfTrappingReturnCarry.relationInvariantLinearChannels_det_eq_zero

end ErdosProblems.Erdos257.PaperCompleteR21
