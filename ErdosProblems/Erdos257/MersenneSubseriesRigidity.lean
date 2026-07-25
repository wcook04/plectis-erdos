import Erdos249257.GreedyAchievementSet

/-!
# Erdős #257: hereditary Mersenne subseries rigidity

Problem-owned consequences of the strict Mersenne tail inequality.  These
results concern achievement-set geometry and do not settle the universal
irrationality problem.
-/

namespace ErdosProblems.Erdos257

open Set
open Erdos249257

/-- Mersenne tails restricted to an arbitrary set of future offsets. -/
noncomputable def selectedMersenneTail (J : Set ℕ) (n : ℕ) : ℝ :=
  ∑' k : ℕ,
    J.indicator (fun k => mersenneWeight (n + k + 1)) k

theorem summable_selectedMersenneTail (J : Set ℕ) (n : ℕ) :
    Summable (J.indicator (fun k => mersenneWeight (n + k + 1))) :=
  (summable_mersenneTail n).indicator J

/-- Strict superincreasingness is hereditary under deleting any collection of
future Mersenne weights. -/
theorem selectedMersenneTail_lt_weight
    (J : Set ℕ) {n : ℕ} (hn : 0 < n) :
    selectedMersenneTail J n < mersenneWeight n := by
  have hle : selectedMersenneTail J n ≤ mersenneTail n := by
    unfold selectedMersenneTail mersenneTail
    exact (summable_selectedMersenneTail J n).tsum_le_tsum
      (fun k => by
        by_cases hk : k ∈ J
        · rw [Set.indicator_of_mem hk]
        · rw [Set.indicator_of_notMem hk]
          exact (mersenneWeight_pos (by omega : 0 < n + k + 1)).le)
      (summable_mersenneTail n)
  exact hle.trans_lt (mersenneTail_lt_weight hn)

/-- Binary digit strings supported on `J`. -/
def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}

/-- The ordinary Mersenne digit map restricted to a chosen support. -/
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1

/-- Every Mersenne subseries retains unique binary coding. -/
theorem supportedMersenneDigitValue_injective (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J) := by
  intro b c h
  apply Subtype.ext
  exact positiveMersenneDigitValue_injective h

end ErdosProblems.Erdos257
