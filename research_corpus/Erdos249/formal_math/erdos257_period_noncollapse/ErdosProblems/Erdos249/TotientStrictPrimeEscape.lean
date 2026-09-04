import Erdos257PeriodNoncollapse.PivotAntiReconstruction

/-!
# Erdős #249: strict prime-orbit escape

Problem-owned consumer for the legacy first-harmonic certificate machinery.
The original irrationality problem remains open; this module keeps the exact
pointwise producer hypothesis visible.
-/

namespace ErdosProblems.Erdos249

open Erdos257PeriodNoncollapse.TotientTailPeriodKiller

/-- Cofinal prime escape at the sharp threshold consumed by the existing
finite-window singleton route.  Unlike the legacy `4/5` socket, this assumes
only a strict gap below `9/10`, with an adaptive truncation budget. -/
def DTWNaturalPrimeTailOrbitStrictGap : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ p : ℕ,
      max (N₀ + h + 1) (h + 5) ≤ p ∧
      p.Prime ∧
      (tailOrbitFirstExp h (p - h - 1)).re < (9 / 10 : ℝ)

/-- A strict `9/10` gap in the exact infinite phase leaves a positive adaptive
truncation budget and supplies the legacy finite `9/10` point escape. -/
theorem naturalPivotPointEscape_of_naturalPrimeTailOrbitStrictGap
    (hgap : DTWNaturalPrimeTailOrbitStrictGap) :
    DTWNaturalPivotPointEscape := by
  intro h hh N₀
  obtain ⟨p, hpN, hp, htail⟩ := hgap h hh N₀
  let N := p - h - 1
  have hN₀ : N₀ ≤ N := by
    dsimp [N]
    omega
  have hN4 : 4 ≤ N := by
    dsimp [N]
    omega
  have htailN :
      (tailOrbitFirstExp h N).re < (9 / 10 : ℝ) := by
    simpa [N] using htail
  let ε : ℝ := (9 / 10 : ℝ) - (tailOrbitFirstExp h N).re
  have hε : 0 < ε := by
    dsimp [ε]
    exact sub_pos.mpr htailN
  obtain ⟨L, hL, hroom, herror⟩ :=
    exists_natural_window_depth_with_error h N (h + 1) ε hε
  have hhL : h < L := by omega
  refine ⟨N, L, N, max_le hN₀ hN4, hhL, hroom, ?_, ?_⟩
  · apply (mem_pivotFiber_one_overlap_iff hN4 (Nat.le_of_lt hhL)).2
    refine ⟨le_rfl, by omega, ?_⟩
    have heq : N + h + 1 = p := by
      dsimp [N]
      omega
    rwa [heq]
  · calc
      windowFirstCos h N L
          ≤ (tailOrbitFirstExp h N).re + ε :=
        windowFirstCos_le_add_of_tailOrbitGap le_rfl herror
      _ = (9 / 10 : ℝ) := by
        dsimp [ε]
        ring

/-- The strict prime-orbit producer closes Erdős #249 through the existing
singleton-certificate endpoint.  The producer itself remains unproved. -/
theorem irrational_totient_series_of_naturalPrimeTailOrbitStrictGap
    (hgap : DTWNaturalPrimeTailOrbitStrictGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_naturalPivotPointEscape
    (naturalPivotPointEscape_of_naturalPrimeTailOrbitStrictGap hgap)

end ErdosProblems.Erdos249
