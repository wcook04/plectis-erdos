/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.ChannelIntegralCongruence

/-!
# Source transport for the Erdős #68 channel-radius obstruction

The declarations below restate the Mathlib-only challenge vocabulary and
transport the exact source theorems without strengthening their hypotheses.
-/

namespace Erdos249257.ExternalVerification68ChannelRadius

def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)

theorem square_subsequence_radius_three_halves_lower
    {t M R : ℕ} (ht : 2 ^ 32 ≤ t)
    (hMpos : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1) := by
  apply Erdos68.square_subsequence_radius_three_halves_lower ht hMpos
  · simpa [channelLCM, Erdos68.channelLCM] using hdiv
  · exact hsmall

theorem no_eventual_square_subsequence_three_halves_upper
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 2 ^ 32 ≤ t → 0 < M t)
    (hdiv : ∀ t, 2 ^ 32 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 2 ^ 32 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T, ∀ t, T ≤ t → 2 * (R t + 1) ≤ 3 * t ^ 3 := by
  apply Erdos68.no_eventual_square_subsequence_three_halves_upper M R hMpos
  · intro t ht
    simpa [channelLCM, Erdos68.channelLCM] using hdiv t ht
  · exact hsmall

theorem not_isLittleO_square_subsequence_radius
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 4096 ≤ t → 0 < M t)
    (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 4096 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => ((R t + 1 : ℕ) : ℝ)) =o[Filter.atTop]
        (fun t : ℕ => (t : ℝ) ^ 3) := by
  apply Erdos68.not_isLittleO_square_subsequence_radius M R hMpos
  · intro t ht
    simpa [channelLCM, Erdos68.channelLCM] using hdiv t ht
  · exact hsmall

theorem square_subsequence_radius_cubic_lower
    {t M R : ℕ} (ht : 4096 ≤ t)
    (hMpos : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    t ^ 3 < 8 * (R + 1) := by
  apply Erdos68.square_subsequence_radius_cubic_lower ht hMpos
  · simpa [channelLCM, Erdos68.channelLCM] using hdiv
  · exact hsmall

theorem no_eventual_square_subsequence_cubic_upper
    (M R : ℕ → ℕ)
    (hMpos : ∀ t, 4096 ≤ t → 0 < M t)
    (hdiv : ∀ t, 4096 ≤ t → channelLCM (2 * t ^ 2) ∣ M t)
    (hsmall : ∀ t, 4096 ≤ t →
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T, ∀ t, T ≤ t → 8 * (R t + 1) ≤ t ^ 3 := by
  apply Erdos68.no_eventual_square_subsequence_cubic_upper M R hMpos
  · intro t ht
    simpa [channelLCM, Erdos68.channelLCM] using hdiv t ht
  · exact hsmall

theorem sharp_radius_satisfies_square_log_constraint
    {t R : ℕ} (ht : 4 ≤ t) (hsharp : 9 * (R + 1) = 16 * t ^ 3) :
    (2 * t : ℝ) *
          (((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) *
              Real.log ((2 * t ^ 2 + 1 - 2 * t : ℕ) : ℝ) -
            (2 * t ^ 2 + 1 - 2 * t : ℕ) - Real.log 2) <
        ((R + 1 : ℕ) : ℝ) * Real.log (R + 1 : ℝ) +
          (((2 * t + 1).choose 3 : ℕ) : ℝ) *
            Real.log ((2 * t ^ 2 : ℕ) : ℝ) :=
  Erdos68.sharp_radius_satisfies_square_log_constraint ht hsharp

end Erdos249257.ExternalVerification68ChannelRadius
