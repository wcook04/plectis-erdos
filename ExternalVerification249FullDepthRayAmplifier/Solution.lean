import Mathlib
import ErdosProblems.Erdos249.FullDepthRayAmplifier

namespace Erdos249257.ExternalVerification249FullDepthRayAmplifier

open scoped BigOperators

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧ windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
def PeriodMultipleKillSupply : Prop := ∀ d : ℕ, 0 < d → ∀ c : ℕ, ∃ t N L : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N L
def ApFullDepthEscape : Prop := ∀ d : ℕ, 0 < d → ∀ N : ℕ, ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)
def fullDepthKillMultipliers (d N : ℕ) : Set ℕ := {t | certifiedKill (t * d) N (t * d)}
def CofinalFullDepthKillSupply : Prop := ∀ d : ℕ, 0 < d → ∀ c : ℕ, ∃ t N : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N (t * d)

theorem eventually_twoSyndetic_fullDepthKillMultipliers_of_seed
    {d N L : ℕ} (hd : 0 < d) (hseed : certifiedKill d N L) :
    ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t →
      ∃ m : ℕ, m ∈ fullDepthKillMultipliers d N ∧ t ≤ m ∧ m ≤ t + 1 := by
  simpa [certifiedKill, windowDiscrepancy, fullDepthKillMultipliers,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy,
    ErdosProblems.Erdos249.FullDepthRayAmplifier.fullDepthKillMultipliers] using
    ErdosProblems.Erdos249.FullDepthRayAmplifier.eventually_twoSyndetic_fullDepthKillMultipliers_of_seed hd hseed

theorem exists_fullDepthKill_on_ray_iff_shift_notMem_int
    {d N : ℕ} (hd : 0 < d) :
    (∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
      totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  simpa [certifiedKill, windowDiscrepancy, totientTail,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail] using
    ErdosProblems.Erdos249.FullDepthRayAmplifier.exists_fullDepthKill_on_ray_iff_shift_notMem_int hd

theorem apFullDepthEscape_iff_irrational :
    ApFullDepthEscape ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  simpa [ApFullDepthEscape, certifiedKill, windowDiscrepancy,
    ErdosProblems.Erdos249.PeriodMultipleEscape.ApFullDepthEscape,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy] using
    ErdosProblems.Erdos249.FullDepthRayAmplifier.apFullDepthEscape_iff_irrational

theorem cofinalFullDepthKillSupply_iff_periodMultipleKillSupply :
    CofinalFullDepthKillSupply ↔ PeriodMultipleKillSupply := by
  simpa [CofinalFullDepthKillSupply, PeriodMultipleKillSupply, certifiedKill,
    windowDiscrepancy,
    ErdosProblems.Erdos249.FullDepthRayAmplifier.CofinalFullDepthKillSupply,
    ErdosProblems.Erdos249.PeriodMultipleEscape.PeriodMultipleKillSupply,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy] using
    ErdosProblems.Erdos249.FullDepthRayAmplifier.cofinalFullDepthKillSupply_iff_periodMultipleKillSupply

theorem cofinalFullDepthKillSupply_iff_irrational :
    CofinalFullDepthKillSupply ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  simpa [CofinalFullDepthKillSupply, certifiedKill, windowDiscrepancy,
    ErdosProblems.Erdos249.FullDepthRayAmplifier.CofinalFullDepthKillSupply,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.certifiedKill,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.windowDiscrepancy] using
    ErdosProblems.Erdos249.FullDepthRayAmplifier.cofinalFullDepthKillSupply_iff_irrational

end Erdos249257.ExternalVerification249FullDepthRayAmplifier
