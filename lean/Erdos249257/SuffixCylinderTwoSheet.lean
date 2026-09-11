import Erdos249257.SuffixCylinderGlobalProducer

/-!
# Escape-side recylindrification after a suffix-cylinder crossing
-/

namespace Erdos249257.SuffixCylinderTwoSheet

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderPromotion
open Erdos249257.SuffixCylinderThreshold
open Erdos249257.SuffixCylinderGlobalProducer

/-- Restrict a selected window to a shorter initial carry interval. -/
noncomputable def SelectedHalfWindow.take
    {N R : ℕ} (W : SelectedHalfWindow N R)
    (S : ℕ) (hSR : S ≤ R) : SelectedHalfWindow N S where
  word k hk hkS := W.word k hk (hkS.trans hSR)
  admissible k hk hkS := W.admissible k hk (hkS.trans hSR)
  terminal k hk hkS := W.terminal k hk (hkS.trans hSR)

/-- Taking an initial carry interval preserves an endpoint cylinder. -/
theorem hasSuffixCylinderAt_take
    {M N R E : ℕ} (W : SelectedHalfWindow N R) (hMN : M ≤ N)
    (hcyl : HasSuffixCylinderAt W hMN E)
    (S : ℕ) (hSR : S ≤ R) :
    HasSuffixCylinderAt
      (Erdos249257.SuffixCylinderTwoSheet.SelectedHalfWindow.take
        W S hSR) hMN E := by
  rcases hcyl with ⟨pfx, hcyl⟩
  refine ⟨pfx, ?_⟩
  intro k hk hkS
  simpa [Erdos249257.SuffixCylinderTwoSheet.SelectedHalfWindow.take]
    using hcyl k hk (hkS.trans hSR)

/-- When a crossing seam's missing carry lies above the entire next strip,
the lower sheet is an initial parent window.  Restricting to that sheet,
promoting its common true bit, and applying the ordinary explicit step
produces a new full suffix-cylinder stage. -/
noncomputable def CylinderStage.feedbackAdvanceCrossingAbove
    {K N : ℕ} (S : CylinderStage K N)
    (hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hcrossLow : 2 ^ (N - (K + 1)) < S.endpoint)
    (hcrossHigh :
      S.endpoint < 2 ^ (N - (K + 1)) + halfStripBound N)
    (c : ℕ)
    (hprofile : ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound N),
      supportCoeff (wordSupport (S.window.word k hk hkR)) (N + 1) =
        if k ≤ S.endpoint - 2 ^ (N - (K + 1)) then c + 1 else c)
    (hholeAbove :
      halfStripBound (N + 1) <
        2 * (S.endpoint - 2 ^ (N - (K + 1))) - c) :
    CylinderStage (K + 1) (N + 1) := by
  let δ := S.endpoint - 2 ^ (N - (K + 1))
  have hδpos : 1 ≤ δ := by
    dsimp [δ]
    omega
  have hδR : δ ≤ halfStripBound N := by
    dsimp [δ]
    omega
  let Wₗ : SelectedHalfWindow N δ :=
    Erdos249257.SuffixCylinderTwoSheet.SelectedHalfWindow.take
      S.window δ hδR
  have hcylK : HasSuffixCylinderAt Wₗ S.hKN S.endpoint :=
    hasSuffixCylinderAt_take S.window S.hKN S.cylinder δ hδR
  have hcylPromoted :
      HasSuffixCylinderAt Wₗ hK1N δ ∧ δ ≤ δ := by
    have hmargin :
        2 ^ (N - (K + 1)) + δ ≤ S.endpoint := by
      dsimp [δ]
      omega
    have hpromote :=
      promoteSuffixCylinderAt_succ_of_headThreshold_add_width_le_endpoint
        Wₗ hK1N hδpos
        (by simpa using hcylK) hmargin
    simpa [δ] using hpromote
  have hpCommon : ∀ k : ℕ, 1 ≤ k → k ≤ δ →
      selectedRowCoeff Wₗ k = (c + 1 : ℕ) := by
    intro k hk hkδ
    rw [selectedRowCoeff, dif_pos ⟨hk, hkδ⟩]
    have hp := hprofile k hk (hkδ.trans hδR)
    rw [if_pos hkδ] at hp
    have hp' :
        supportCoeff (wordSupport (Wₗ.word k hk hkδ)) (N + 1) = c + 1 := by
      simpa [Wₗ,
        Erdos249257.SuffixCylinderTwoSheet.SelectedHalfWindow.take]
        using hp
    exact_mod_cast hp'
  have hbuffer : halfStripBound (N + 1) + (c + 1) ≤ 2 * δ := by
    dsimp [δ] at hholeAbove ⊢
    omega
  let W' : SelectedHalfWindow (N + 1) (halfStripBound (N + 1)) :=
    Wₗ.stepExplicit hN le_rfl hpCommon hbuffer
  have hcyl' : HasSuffixCylinderAt W'
      (hK1N.trans (Nat.le_succ N)) (2 * δ - (c + 1)) ∧
      halfStripBound (N + 1) ≤ 2 * δ - (c + 1) :=
    SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit
      hN Wₗ hK1N le_rfl hpCommon hbuffer
      hcylPromoted.1 hcylPromoted.2
  exact ⟨hK1N.trans (Nat.le_succ N), W', 2 * δ - (c + 1),
    hcyl'.1, hcyl'.2⟩

#print axioms hasSuffixCylinderAt_take
#print axioms CylinderStage.feedbackAdvanceCrossingAbove

end Erdos249257.SuffixCylinderTwoSheet
