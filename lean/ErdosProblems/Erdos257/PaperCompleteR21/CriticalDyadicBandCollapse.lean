import Erdos249257.HalfUpperResetCriticalBand

/-!
Paper-form restatement of `prop:critical-band-index` (line 7767) of the long
Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`.

Clauses: the `d+1`-fold band-avoidance family is literally `∀ j ≤ d`; under
`E ≤ 2^{d+1}` it collapses to one critical nearest-boundary index; the range
assumption is what produces that index; without it every band escapes
automatically once `E > 2^{d+1}` while no critical index exists, and `(d, E) =
(0, 3)` is the smallest such pair; and the concrete seam specialisation is
logically equivalent to the all-band hypothesis of `defn:band-escape`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.HalfUpperResetCriticalBand

/-- Long `prop:critical-band-index`, every asserted clause. -/
theorem paper_critical_band_index_collapse :
    (∀ d E : ℕ, DyadicBandEscape d E ↔
        ∀ j : ℕ, j ≤ d →
          2 ^ (d - j + 1) < E ∨ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)) ∧
      (∀ d E : ℕ, E ≤ 2 ^ (d + 1) →
        (DyadicBandEscape d E ↔ ∃ j : ℕ, CriticalDyadicBandIndex d E j ∧
          E + 2 * (d + j) ≤ 2 ^ (d - j + 1))) ∧
      (∀ d E : ℕ, E ≤ 2 ^ (d + 1) → ∃ j : ℕ, CriticalDyadicBandIndex d E j) ∧
      (∀ d E : ℕ, 2 ^ (d + 1) < E → DyadicBandEscape d E) ∧
      (∀ d E : ℕ, 2 ^ (d + 1) < E → ¬ ∃ j : ℕ, CriticalDyadicBandIndex d E j) ∧
      (2 ^ (0 + 1) < 3 ∧ ∀ d E : ℕ, 2 ^ (d + 1) < E → 0 ≤ d ∧ 3 ≤ E) ∧
      (SeamUpperResetCriticalBandEscape ↔ SeamUpperResetDyadicBandEscape) := by
  refine ⟨fun _ _ => Iff.rfl,
    fun _ _ hE => dyadicBandEscape_iff_exists_critical hE,
    fun _ _ hE => exists_criticalDyadicBandIndex hE, ?_, ?_, ?_,
    seamUpperResetCriticalBandEscape_iff⟩
  · intro d E hE j hj
    left
    have hmono : (2 : ℕ) ^ (d - j + 1) ≤ 2 ^ (d + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rintro d E hE ⟨j, hjd, hEbelow, -⟩
    have hmono : (2 : ℕ) ^ (d - j + 1) ≤ 2 ^ (d + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · refine ⟨by norm_num, fun d E hE => ⟨Nat.zero_le d, ?_⟩⟩
    have hmono : (2 : ℕ) ^ 1 ≤ 2 ^ (d + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hone : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega

#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_band_index_collapse

end ErdosProblems.Erdos257.PaperCompleteR21
