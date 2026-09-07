import ErdosProblems.Erdos1041.SexticAnisotropicCubicCone
import Mathlib.Tactic

/-!
# Erdős #1041: a rational normalized-cubic compactness bound

The complement of the anisotropic cubic cone has a second-mode balance radius
`rho` bounded below by `25s/128`.  Radial energy bounds the cubic coefficient by
`(7/2)s^3`, hence the normalized cubic coordinate by the integer constant 470.
-/

namespace ErdosProblems.Erdos1041.SexticNormalizedCubicCompactness

/-- The second-mode lower threshold forces `rho ≥ s/8`. -/
theorem balanceRadius_ge_eighth
    {s e2 rho : ℝ}
    (hs : 0 ≤ s) (hrho : 0 ≤ rho)
    (he2 : 3 * s ^ 4 / 2048 ≤ e2)
    (hrho4 : rho ^ 4 = e2) :
    s / 8 ≤ rho := by
  by_contra h
  have hrlt : rho < s / 8 := lt_of_not_ge h
  have hp : rho ^ 4 < (s / 8) ^ 4 :=
    pow_lt_pow_left₀ hrlt hrho (by norm_num)
  rw [hrho4] at hp
  have hscale : (s / 8) ^ 4 = s ^ 4 / 4096 := by ring
  rw [hscale] at hp
  nlinarith [pow_nonneg hs 4]

/-- A nearly sharp rational lower bound for the balance radius. -/
theorem balanceRadius_ge_twentyFiveOver128
    {s e2 rho : ℝ}
    (hs : 0 ≤ s) (hrho : 0 ≤ rho)
    (he2 : 3 * s ^ 4 / 2048 ≤ e2)
    (hrho4 : rho ^ 4 = e2) :
    25 * s / 128 ≤ rho := by
  by_contra h
  have hrlt : rho < 25 * s / 128 := lt_of_not_ge h
  have hp : rho ^ 4 < (25 * s / 128) ^ 4 :=
    pow_lt_pow_left₀ hrlt hrho (by norm_num)
  rw [hrho4] at hp
  have hscale : (25 * s / 128) ^ 4 =
      390625 * s ^ 4 / 268435456 := by ring
  rw [hscale] at hp
  nlinarith [pow_nonneg hs 4]

/-- The radial-energy inequality `c² ≤ 12s⁶` gives `c ≤ 4s³`. -/
theorem cubicCoeff_le_four_cube
    {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (henergy : c ^ 2 ≤ 12 * s ^ 6) :
    c ≤ 4 * s ^ 3 := by
  have hsq : c ^ 2 ≤ (4 * s ^ 3) ^ 2 := by
    nlinarith [pow_nonneg hs 6]
  exact (sq_le_sq₀ hc (by positivity)).mp hsq

/-- A tighter rational majorant for the square-root energy constant. -/
theorem cubicCoeff_le_sevenHalves_cube
    {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (henergy : c ^ 2 ≤ 12 * s ^ 6) :
    c ≤ (7 / 2 : ℝ) * s ^ 3 := by
  have hsq : c ^ 2 ≤ ((7 / 2 : ℝ) * s ^ 3) ^ 2 := by
    nlinarith [pow_nonneg hs 6]
  exact (sq_le_sq₀ hc (by positivity)).mp hsq

/-- Fully rational compactness bound for the normalized cubic coordinate. -/
theorem normalizedCubic_le_twoThousandFortyEight
    {s e2 rho c : ℝ}
    (hs : 0 < s) (hrho : 0 ≤ rho) (hc : 0 ≤ c)
    (he2 : 3 * s ^ 4 / 2048 ≤ e2)
    (hrho4 : rho ^ 4 = e2)
    (henergy : c ^ 2 ≤ 12 * s ^ 6) :
    c ≤ 2048 * rho ^ 3 := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hrhoLower := balanceRadius_ge_eighth hs0 hrho he2 hrho4
  have hcubic := cubicCoeff_le_four_cube hs0 hc henergy
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ s / 8) hrhoLower 3
  have hsCube : s ^ 3 ≤ 512 * rho ^ 3 := by
    norm_num at hpow ⊢
    nlinarith
  nlinarith

/-- Ratio form used by compact coefficient atlases. -/
theorem normalizedCubic_ratio_le
    {s e2 rho c : ℝ}
    (hs : 0 < s) (hrho : 0 ≤ rho) (hc : 0 ≤ c)
    (he2 : 3 * s ^ 4 / 2048 ≤ e2)
    (hrho4 : rho ^ 4 = e2)
    (henergy : c ^ 2 ≤ 12 * s ^ 6) :
    c / rho ^ 3 ≤ 2048 := by
  have hrhoLower := balanceRadius_ge_eighth (le_of_lt hs) hrho he2 hrho4
  have hrhoPos : 0 < rho := lt_of_lt_of_le (by positivity : 0 < s / 8) hrhoLower
  rw [div_le_iff₀ (pow_pos hrhoPos 3)]
  nlinarith [normalizedCubic_le_twoThousandFortyEight
    hs hrho hc he2 hrho4 henergy]

/-- A near-optimal integer compactness ceiling, used by the finite atlas. -/
theorem normalizedCubic_le_fourHundredSeventy
    {s e2 rho c : ℝ}
    (hs : 0 < s) (hrho : 0 ≤ rho) (hc : 0 ≤ c)
    (he2 : 3 * s ^ 4 / 2048 ≤ e2)
    (hrho4 : rho ^ 4 = e2)
    (henergy : c ^ 2 ≤ 12 * s ^ 6) :
    c ≤ 470 * rho ^ 3 := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hrhoLower := balanceRadius_ge_twentyFiveOver128 hs0 hrho he2 hrho4
  have hcubic := cubicCoeff_le_sevenHalves_cube hs0 hc henergy
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 25 * s / 128) hrhoLower 3
  have hsCube : 15625 * s ^ 3 ≤ 2097152 * rho ^ 3 := by
    norm_num at hpow ⊢
    nlinarith
  nlinarith [pow_nonneg hrho 3]

/-- Ratio form of the 470 compactness ceiling. -/
theorem normalizedCubic_ratio_le_fourHundredSeventy
    {s e2 rho c : ℝ}
    (hs : 0 < s) (hrho : 0 ≤ rho) (hc : 0 ≤ c)
    (he2 : 3 * s ^ 4 / 2048 ≤ e2)
    (hrho4 : rho ^ 4 = e2)
    (henergy : c ^ 2 ≤ 12 * s ^ 6) :
    c / rho ^ 3 ≤ 470 := by
  have hrhoLower := balanceRadius_ge_twentyFiveOver128
    (le_of_lt hs) hrho he2 hrho4
  have hrhoPos : 0 < rho :=
    lt_of_lt_of_le (by positivity : 0 < 25 * s / 128) hrhoLower
  rw [div_le_iff₀ (pow_pos hrhoPos 3)]
  exact normalizedCubic_le_fourHundredSeventy hs hrho hc he2 hrho4 henergy

end ErdosProblems.Erdos1041.SexticNormalizedCubicCompactness
