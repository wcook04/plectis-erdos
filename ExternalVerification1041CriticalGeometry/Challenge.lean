/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1041 critical-geometry package

The package combines two source-current all-degree critical metric summits and
two exact straight-line obstructions.  The cubic safe-spoke theorem is compared
in `ExternalVerification1041SolvedFamilies`, where it supports the complete
translated cubic family, and is not repeated here.  The first
obstruction is the arithmetic endpoint of the unique-nearest-spoke quintic
certificate.  The second gives an explicit cubic for which every root-pair
midpoint escapes the unit lemniscate.  None of these statements claims the
unrestricted root-to-root path theorem.
-/

namespace Erdos249257.ExternalVerification1041CriticalGeometry

open Finset

/-- At a non-root critical point, two distinct root occurrences have total
distance at most twice the geometric mean of all root distances. -/
theorem criticalGeometricMean_twoRootProximity
    {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℂ) (c : ℂ)
    (hne : ∀ k, c - z k ≠ 0)
    (hcrit : ∑ k, (c - z k)⁻¹ = 0)
    {r : ℝ} (hr : 0 < r) (hrn : r ^ n = ∏ k, ‖c - z k‖) :
    ∃ i j : Fin n, i ≠ j ∧ ‖c - z i‖ + ‖c - z j‖ ≤ 2 * r := by
  sorry

/-- The scalar core of the global unit-disk theorem: the two nearest-root
distances `δ ≤ e` at a critical point have sum at most two once the exact
disk inverse-square estimate, reciprocal balance, and disk diameter bounds
have been supplied.  The polynomial-level derivation of these hypotheses is
an ordinary analytic/geometric assembly, not part of this declaration. -/
theorem criticalDiskInverseBalance_twoRootProximity
    {N t δ e : ℝ}
    (hN : 2 ≤ N) (ht1 : t < 1)
    (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    (hemax : e ≤ 1 + t) (hbal : e ≤ (N - 1) * δ)
    (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) :
    δ + e ≤ 2 := by
  sorry

/-- A strict disk-diameter margin upgrades the same global inverse-balance
budget from `δ + e ≤ 2` to `δ + e < 2`. -/
theorem criticalDiskInverseBalance_twoRootProximity_strict
    {N t δ e : ℝ}
    (hN : 2 ≤ N) (ht1 : t < 1)
    (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    (hemax : e < 1 + t) (hbal : e ≤ (N - 1) * δ)
    (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) :
    δ + e < 2 := by
  sorry

/-- Exact arithmetic escape certificate at one tenth of the unique nearest
spoke in the source quintic construction.  The reciprocal-balance and
unique-nearest-root parts of that construction are separate source theorems. -/
theorem nearestSpoke_unique_nearest_spoke_escapes :
    (1 : ℝ) <
      (900099 / 902000 : ℝ) * (1 - 1 / 10) *
        (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 + (999 / 1000) ^ 2) *
        (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 +
          (1 / 10) * (999 / 1000) ^ 2 + (999 / 1000) ^ 2) := by
  sorry

/- The source keeps these four configuration definitions private.  They are
reproduced literally here so that the all-pairs obstruction has a public,
self-contained Challenge interface. -/

noncomputable def allStraightRadius : ℂ := (99 : ℂ) / 100

noncomputable def allStraightOmega : ℂ :=
  (-1 : ℂ) / 2 + ((Real.sqrt 3 : ℂ) / 2) * Complex.I

noncomputable def allStraightRoot : Fin 3 → ℂ
  | 0 => allStraightRadius
  | 1 => allStraightRadius * allStraightOmega
  | 2 => allStraightRadius * allStraightOmega ^ 2

noncomputable def allStraightCubic (z : ℂ) : ℂ :=
  z ^ 3 - allStraightRadius ^ 3

/-- For the explicit monic cubic with radius `99/100`, the midpoint of every
pair of distinct roots lies outside the strict unit lemniscate. -/
theorem allStraightCubic_every_pair_midpoint_escapes :
    ∀ i j : Fin 3, i ≠ j →
      1 < ‖allStraightCubic ((allStraightRoot i + allStraightRoot j) / 2)‖ := by
  sorry

end Erdos249257.ExternalVerification1041CriticalGeometry
