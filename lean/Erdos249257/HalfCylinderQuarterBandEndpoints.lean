import Erdos249257.HalfCylinderConcreteSeamAdapter

/-!
# Exact endpoint cells for the half-cylinder quarter bands

The abstract adjacent-cut recurrence leaves two non-carry branches.  A
failure of the desired next-row upper bound in the middle branch occupies one
multiple-of-four cell; in the terminal-reset branch it occupies an explicit
finite interval constrained by the adjacent overshoot.  These are arithmetic
normal forms only: this module does not assert that the production seam word
avoids the cells.
-/

namespace Erdos249257
namespace HalfCylinderIntegerGreedy

/-! ## Pure multiple-of-four endpoint normal forms -/

/-- A four-unit slab above `4H + pulse` contains precisely the indicated
multiple-of-four cell. -/
theorem middleUpperFailure_iff_exists_pulseCell
    {H R pulse : ℕ} :
    (4 * H + pulse ≤ 4 * R ∧ 4 * R < 4 * H + pulse + 4) ↔
      ∃ k : ℕ,
        R = H + k ∧ pulse ≤ 4 * k ∧ 4 * k < pulse + 4 := by
  constructor
  · rintro ⟨hlower, hupper⟩
    have hHR : H ≤ R := by omega
    refine ⟨R - H, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨k, rfl, hlower, hupper⟩
    omega

/-- The integer cell in a four-unit pulse slab is unique. -/
theorem pulseCell_unique
    {pulse k l : ℕ}
    (hk : pulse ≤ 4 * k ∧ 4 * k < pulse + 4)
    (hl : pulse ≤ 4 * l ∧ 4 * l < pulse + 4) :
    k = l := by
  omega

/-- With adjacent remainder `R`, overshoot `U`, and separation `Delta`, a
right-reset failure is exactly a `3H+k` cell in the pulse-constrained
interval. -/
theorem rightUpperFailure_iff_exists_pulseCell
    {H R U Delta belowPulse abovePulse : ℕ}
    (hadjacent : R + U = Delta) :
    (4 * H < 4 * U + abovePulse ∧
        12 * H + belowPulse + 4 ≤ 4 * R) ↔
      ∃ k : ℕ,
        R = 3 * H + k ∧
          belowPulse + 4 ≤ 4 * k ∧
          4 * k + 16 * H < 4 * Delta + abovePulse := by
  constructor
  · rintro ⟨hnocarry, hlower⟩
    have hthree : 3 * H ≤ R := by omega
    refine ⟨R - 3 * H, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨k, rfl, hlower, hupper⟩
    constructor <;> omega

/-- If the adjacent separation is `4H + correction`, the right-reset cell
interval depends only on that correction and the two pulses. -/
theorem rightUpperFailure_iff_exists_correctedPulseCell
    {H R U Delta correction belowPulse abovePulse : ℕ}
    (hadjacent : R + U = Delta)
    (hcorrection : Delta = 4 * H + correction) :
    (4 * H < 4 * U + abovePulse ∧
        12 * H + belowPulse + 4 ≤ 4 * R) ↔
      ∃ k : ℕ,
        R = 3 * H + k ∧
          belowPulse + 4 ≤ 4 * k ∧
          4 * k < 4 * correction + abovePulse := by
  rw [rightUpperFailure_iff_exists_pulseCell hadjacent]
  constructor
  · rintro ⟨k, hk, hlower, hupper⟩
    refine ⟨k, hk, hlower, ?_⟩
    omega
  · rintro ⟨k, hk, hlower, hupper⟩
    refine ⟨k, hk, hlower, ?_⟩
    omega

/-! ## Exact failures of the adjacent-cut next-row upper bound -/

open PerturbedFamily

/-- On the non-carry middle branch, failure of `nextRemainder < 2*gap`
is exactly the unique four-unit pulse cell. -/
theorem PerturbedFamily.AdjacentCut.middleNextUpperFailure_iff_pulseCell
    {α : Type*} {F : PerturbedFamily α} {C H : ℕ}
    (K : F.AdjacentCut C)
    [Decidable K.successorCarries]
    (hgap : F.gap = 4 * H)
    (hncarry : ¬ K.successorCarries)
    (hmiddle :
      4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight) :
    ¬ K.nextRemainder < 2 * F.gap ↔
      ∃ k : ℕ,
        K.remainder = H + k ∧
          K.belowPulse ≤ 4 * k ∧
          4 * k < K.belowPulse + 4 := by
  rw [K.nextRemainder_trichotomy, if_neg hncarry, if_pos hmiddle]
  unfold PerturbedFamily.AdjacentCut.terminalWeight at hmiddle
  rw [hgap] at hmiddle ⊢
  rw [← middleUpperFailure_iff_exists_pulseCell]
  have hH : 0 < H := by
    have := F.gap_pos
    omega
  omega

/-- On the non-carry terminal-reset branch, failure of the same upper bound
is exactly a `3H+k` cell in the adjacent-separation pulse interval. -/
theorem PerturbedFamily.AdjacentCut.rightNextUpperFailure_iff_pulseCell
    {α : Type*} {F : PerturbedFamily α} {C H : ℕ}
    (K : F.AdjacentCut C)
    [Decidable K.successorCarries]
    (hgap : F.gap = 4 * H)
    (hncarry : ¬ K.successorCarries)
    (hright : K.terminalWeight ≤
      4 * K.remainder + F.gap - K.belowPulse) :
    ¬ K.nextRemainder < 2 * F.gap ↔
      ∃ k : ℕ,
        K.remainder = 3 * H + k ∧
          K.belowPulse + 4 ≤ 4 * k ∧
          4 * k + 16 * H <
            4 * (K.remainder + K.overshoot) + K.abovePulse := by
  have hnterminal :
      ¬ 4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight :=
    Nat.not_lt_of_ge hright
  have hnocarry : F.gap < 4 * K.overshoot + K.abovePulse := by
    unfold PerturbedFamily.AdjacentCut.successorCarries at hncarry
    omega
  rw [K.nextRemainder_trichotomy, if_neg hncarry, if_neg hnterminal]
  unfold PerturbedFamily.AdjacentCut.terminalWeight at hright
  rw [hgap] at hright hnocarry ⊢
  have hpure := rightUpperFailure_iff_exists_pulseCell
    (H := H) (R := K.remainder) (U := K.overshoot)
    (Delta := K.remainder + K.overshoot)
    (belowPulse := K.belowPulse) (abovePulse := K.abovePulse) rfl
  constructor
  · intro hfailure
    apply hpure.mp
    exact ⟨hnocarry, by omega⟩
  · intro hcell
    have hlower := (hpure.mpr hcell).2
    omega

/-! ## Concrete seam specialization -/

noncomputable local instance quarterBandEndpointCarriesDecidable
    {α : Type*} {F : PerturbedFamily α} {C : ℕ}
    (K : F.AdjacentCut C) : Decidable K.successorCarries :=
  Classical.propDecidable _

theorem seamAdjacentCut_middleNextUpperFailure_iff_pulseCell
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
          (seamPerturbedFamily s (by omega)).gap -
          (seamAdjacentCut s hs).belowPulse <
        (seamAdjacentCut s hs).terminalWeight) :
    ¬ (seamAdjacentCut s hs).nextRemainder <
          2 * (seamPerturbedFamily s (by omega)).gap ↔
      ∃ k : ℕ,
        (seamAdjacentCut s hs).remainder = 2 ^ (s - 1) + k ∧
          (seamAdjacentCut s hs).belowPulse ≤ 4 * k ∧
          4 * k < (seamAdjacentCut s hs).belowPulse + 4 := by
  have hgap : (seamPerturbedFamily s (by omega)).gap =
      4 * 2 ^ (s - 1) := by
    dsimp [seamPerturbedFamily]
    rw [show s + 1 = 2 + (s - 1) by omega, pow_add]
    norm_num
  exact (seamAdjacentCut s hs).middleNextUpperFailure_iff_pulseCell
    hgap hncarry hmiddle

theorem seamAdjacentCut_rightNextUpperFailure_iff_pulseCell
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hright : (seamAdjacentCut s hs).terminalWeight ≤
      4 * (seamAdjacentCut s hs).remainder +
        (seamPerturbedFamily s (by omega)).gap -
        (seamAdjacentCut s hs).belowPulse) :
    ¬ (seamAdjacentCut s hs).nextRemainder <
          2 * (seamPerturbedFamily s (by omega)).gap ↔
      ∃ k : ℕ,
        (seamAdjacentCut s hs).remainder = 3 * 2 ^ (s - 1) + k ∧
          (seamAdjacentCut s hs).belowPulse + 4 ≤ 4 * k ∧
          4 * k + 16 * 2 ^ (s - 1) <
            4 * ((seamAdjacentCut s hs).remainder +
              (seamAdjacentCut s hs).overshoot) +
                (seamAdjacentCut s hs).abovePulse := by
  have hgap : (seamPerturbedFamily s (by omega)).gap =
      4 * 2 ^ (s - 1) := by
    dsimp [seamPerturbedFamily]
    rw [show s + 1 = 2 + (s - 1) by omega, pow_add]
    norm_num
  exact (seamAdjacentCut s hs).rightNextUpperFailure_iff_pulseCell
    hgap hncarry hright

#print axioms middleUpperFailure_iff_exists_pulseCell
#print axioms pulseCell_unique
#print axioms rightUpperFailure_iff_exists_pulseCell
#print axioms rightUpperFailure_iff_exists_correctedPulseCell
#print axioms PerturbedFamily.AdjacentCut.middleNextUpperFailure_iff_pulseCell
#print axioms PerturbedFamily.AdjacentCut.rightNextUpperFailure_iff_pulseCell
#print axioms seamAdjacentCut_middleNextUpperFailure_iff_pulseCell
#print axioms seamAdjacentCut_rightNextUpperFailure_iff_pulseCell

end HalfCylinderIntegerGreedy
end Erdos249257
