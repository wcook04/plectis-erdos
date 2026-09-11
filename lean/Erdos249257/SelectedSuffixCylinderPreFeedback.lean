import Erdos249257.SelectedSuffixCylinder

/-!
# Exact selected-window run to the first feedback row

The depth-18 executable base has a common depth-13 prefix and an
endpoint-indexed suffix cylinder.  Before row 28, every proper divisor read by
the next coefficient lies at or below that common prefix.  This module turns
that observation into an actual data-producing run of full selected windows
through depth 27, while preserving the suffix-cylinder invariant at every
step.

The result is the exact object-level input needed at the first genuine
half-divisor feedback row.  It replaces scratch scans or two-carry slices by a
full protected window on every carry in `1, ..., halfStripBound 27`.
-/

namespace Erdos249257.SelectedSuffixCylinderPreFeedback

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.HalfCarrySelectedWindowBase
open Erdos249257.SelectedSuffixCylinder

/-- A full selected window together with the common depth-13 suffix-cylinder
data that drives the pre-feedback induction. -/
structure Stage (N : ℕ) where
  h13 : 13 ≤ N
  window : SelectedHalfWindow N (halfStripBound N)
  endpoint : ℕ
  cylinder : HasSuffixCylinderAt window h13 endpoint
  covers : halfStripBound N ≤ endpoint

/-- One exact pre-feedback step.  The half-depth hypothesis makes the common
depth-13 restriction sufficient for next-row divisor agreement.  The
canonical selected successor then preserves the suffix cylinder and updates
its endpoint by `E' = 2E - C`. -/
noncomputable def Stage.step
    {N : ℕ} (S : Stage N) (hhalf : (N + 1) / 2 ≤ 13) :
    Stage (N + 1) := by
  let W := S.window
  have hN : 1 ≤ N :=
    (by norm_num : 1 ≤ 13).trans S.h13
  have hR : 1 ≤ halfStripBound N := by
    unfold halfStripBound
    omega
  have hcommon : W.CommonRestrictionAt S.h13 := by
    rcases S.cylinder with ⟨pfx, hpfx⟩
    exact ⟨pfx, fun k hk hkR ↦ (hpfx k hk hkR).1⟩
  have hagree : W.NextRowDivisorAgreement :=
    W.nextRowDivisorAgreement_of_commonRestriction S.h13 hhalf hcommon
  let a₁ := W.word 1 (by omega) hR
  let C : ℕ := supportCoeff (wordSupport a₁) (N + 1)
  have hp_common : ∀ k : ℕ, 1 ≤ k → k ≤ halfStripBound N →
      selectedRowCoeff W k = C := by
    intro k hk hkR
    calc
      selectedRowCoeff W k = selectedRowCoeff W 1 :=
        W.selectedRowCoeff_eq hagree hk hkR (by omega) hR
      _ = C := by
        rw [selectedRowCoeff, dif_pos ⟨show 1 ≤ (1 : ℕ) by omega, hR⟩]
  have hbuffer : halfStripBound (N + 1) + C ≤
      2 * halfStripBound N := by
    have hC : C ≤ 2 * Nat.sqrt (N + 1) := by
      exact supportCoeff_le_two_mul_sqrt (wordSupport a₁) (N + 1)
    simpa using halfStripBound_add_coeff_le_two_mul_pred
      (n := N + 1) (c := C) (by omega) hC
  let W' : SelectedHalfWindow (N + 1) (halfStripBound (N + 1)) :=
    W.stepExplicit hN le_rfl hp_common hbuffer
  have hcyl' : HasSuffixCylinderAt W'
      (S.h13.trans (Nat.le_succ N)) (2 * S.endpoint - C) ∧
      halfStripBound (N + 1) ≤ 2 * S.endpoint - C := by
    exact
      Erdos249257.SelectedSuffixCylinder.SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit
        hN W S.h13 le_rfl hp_common hbuffer S.cylinder S.covers
  exact ⟨S.h13.trans (Nat.le_succ N), W', 2 * S.endpoint - C,
    hcyl'.1, hcyl'.2⟩

/-- The executable depth-18 base, now packaged with its endpoint cover. -/
noncomputable def stage18 : Stage 18 :=
  ⟨by omega, depth18SelectedHalfWindow, 17,
    depth18SelectedHalfWindow_hasSuffixCylinderAt_thirteen,
    depth18SelectedHalfWindow_endpoint_covers_strip⟩

noncomputable def stage19 : Stage 19 := by
  simpa using stage18.step (by norm_num)

noncomputable def stage20 : Stage 20 := by
  simpa using stage19.step (by norm_num)

noncomputable def stage21 : Stage 21 := by
  simpa using stage20.step (by norm_num)

noncomputable def stage22 : Stage 22 := by
  simpa using stage21.step (by norm_num)

noncomputable def stage23 : Stage 23 := by
  simpa using stage22.step (by norm_num)

noncomputable def stage24 : Stage 24 := by
  simpa using stage23.step (by norm_num)

noncomputable def stage25 : Stage 25 := by
  simpa using stage24.step (by norm_num)

noncomputable def stage26 : Stage 26 := by
  simpa using stage25.step (by norm_num)

/-- The last step before the half-depth cutoff moves from 13 to 14. -/
noncomputable def stage27 : Stage 27 := by
  simpa using stage26.step (by norm_num)

/-- Uniform finite-range form of the pre-feedback construction.  This is the
consumer-facing statement: every depth from the certified base through the
last row before feedback carries a full selected window with the same
depth-13 cylinder invariant. -/
theorem nonempty_stage_of_eighteen_le_of_le_twentySeven
    {N : ℕ} (h18 : 18 ≤ N) (h27 : N ≤ 27) :
    Nonempty (Stage N) := by
  interval_cases N <;>
    first
    | exact ⟨stage18⟩
    | exact ⟨stage19⟩
    | exact ⟨stage20⟩
    | exact ⟨stage21⟩
    | exact ⟨stage22⟩
    | exact ⟨stage23⟩
    | exact ⟨stage24⟩
    | exact ⟨stage25⟩
    | exact ⟨stage26⟩
    | exact ⟨stage27⟩

/-- Full protected selected window at the first feedback depth. -/
noncomputable def depth27SelectedHalfWindow :
    SelectedHalfWindow 27 (halfStripBound 27) :=
  stage27.window

/-- Every carry in the depth-27 protected strip shares the depth-13 prefix
and has an endpoint-indexed suffix. -/
theorem depth27SelectedHalfWindow_hasSuffixCylinderAt_thirteen :
    HasSuffixCylinderAt depth27SelectedHalfWindow (by omega : 13 ≤ 27)
      stage27.endpoint := by
  exact stage27.cylinder

/-- The propagated endpoint still covers the full depth-27 carry strip. -/
theorem depth27SelectedHalfWindow_endpoint_covers_strip :
    halfStripBound 27 ≤ stage27.endpoint :=
  stage27.covers

/-- In particular, the pre-feedback run provides an actual admissible word
for every terminal carry in the full depth-27 protected strip. -/
theorem depth27SelectedHalfWindow_admissible
    {k : ℕ} (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 27) :
    HalfStripAdmissible 27
      (depth27SelectedHalfWindow.word k hk hkR) :=
  depth27SelectedHalfWindow.admissible k hk hkR

#print axioms Stage.step
#print axioms depth27SelectedHalfWindow
#print axioms nonempty_stage_of_eighteen_le_of_le_twentySeven
#print axioms depth27SelectedHalfWindow_hasSuffixCylinderAt_thirteen
#print axioms depth27SelectedHalfWindow_endpoint_covers_strip
#print axioms depth27SelectedHalfWindow_admissible

end Erdos249257.SelectedSuffixCylinderPreFeedback
