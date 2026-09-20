import Erdos249257.HalfCylinderSeamLimit

/-!
Work toward the long Erdős #257 environment `thm:seam-limit` ("The quotient
remainders converge to the greedy deficit",
`paper/reasoning-parts/erdos257/a257_front.tex`, line 2499).

The environment asserts `X_{D_s}(2) → X_G(2)`, `rem(s)/4^s → δ := 1/2 - X_G(2) ≥ 0`,
and the equivalence of three conditions: `1/2 ∈ 𝒜`; the full sequence
`rem(s)/4^s` tends to zero; some cofinal subsequence does.

This file lands everything the environment asserts *downstream* of one missing
input, and states that input explicitly.  The missing input is the
unconditional convergence of the finite seam values,
`Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfValue)`, which the paper's
proof obtains from the finite-prefix stability of `prop:one-orbit`
(`D_s ∩ {2,…,K} = G ∩ {2,…,K}` for all large `s`, for each fixed `K`).  No
declaration in the tree asserts that stability; it is the whole remaining
obligation of the row.

Landed unconditionally here:

* `seamGreedyNormalizedRemainder_eq` — the paper's exact quotient identity
  `X_{D_s}(2) = 1/2 - 2^{-s} - rem(s)/4^s + Φ_s/4^s`, in the solved-for form;
* `seamGreedyFloorError_nonneg_lt_width` — the paper's `0 ≤ Φ_s < s - 2`;
* `tendsto_seamGreedyFloorError_div_atTop` — `Φ_s/4^s → 0`;
* `half_mem_iff_seamGreedyDeficit_eq_zero` — `1/2 ∈ 𝒜` is exactly `δ = 0`.

Landed conditionally on the missing input: `paper_seam_limit`, the whole
environment.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open Filter

/-- `X_G(2)`: the value of the real greedy support for the half target. -/
noncomputable def greedyHalfValue : ℝ :=
  positiveMersenneSupportValue (greedyMersenneSupport (1 / 2 : ℝ))

/-- The paper's `δ = 1/2 - X_G(2)`. -/
noncomputable def seamGreedyDeficit : ℝ := 1 / 2 - greedyHalfValue

/-! ## Membership is exactly a vanishing deficit -/

theorem half_mem_iff_greedyHalfValue_eq :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ greedyHalfValue = 1 / 2 := by
  constructor
  · rintro ⟨A, hA0, hv⟩
    have h : greedyMersenneSupport (1 / 2 : ℝ) = A := by
      rw [hv, greedySupport_supportValue_eq A hA0]
    rw [greedyHalfValue, h, ← hv]
  · intro h
    unfold greedyHalfValue at h
    exact ⟨greedyMersenneSupport (1 / 2 : ℝ), zero_not_mem_greedyMersenneSupport _, h.symm⟩

theorem half_mem_iff_seamGreedyDeficit_eq_zero :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ seamGreedyDeficit = 0 := by
  rw [half_mem_iff_greedyHalfValue_eq, seamGreedyDeficit]
  constructor <;> intro h <;> linarith

/-! ## The exact quotient identity and the floor-error window -/

/-- The paper's `0 ≤ Φ_s < s - 2`. -/
theorem seamGreedyFloorError_nonneg_lt_width {s : ℕ} (hs : 3 ≤ s) :
    0 ≤ seamGreedyFloorError s ∧ seamGreedyFloorError s < ((s - 2 : ℕ) : ℚ) :=
  ⟨seamWordFloorError_nonneg (seamGreedyWord s),
    seamWordFloorError_lt_width hs (seamGreedyWord s)⟩

private theorem half_pow_eq_div (s : ℕ) :
    (1 / 2 : ℝ) ^ s = (2 : ℝ) ^ s / (4 : ℝ) ^ s := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, div_pow, one_pow]
  have h2 : ((2 : ℝ) ^ s) ≠ 0 := by positivity
  field_simp

/-- The paper's exact quotient identity
`X_{D_s}(2) = 1/2 - 2^{-s} - rem(s)/4^s + Φ_s/4^s`, solved for the normalised
quotient remainder. -/
theorem seamGreedyNormalizedRemainder_eq (s : ℕ) (hs : 5 ≤ s) :
    seamGreedyNormalizedRemainder s
      = 1 / 2 - (1 / 2 : ℝ) ^ s - seamGreedyFiniteValue s
        + ((seamGreedyFloorError s : ℚ) : ℝ) / (4 : ℝ) ^ s := by
  have hcast : ((seamWordRationalRemainder (seamGreedyWord s) : ℚ) : ℝ)
      = 1 / 2 - seamGreedyFiniteValue s := by
    rw [seamWordRationalRemainder, seamGreedyFiniteValue_eq_cast_rationalSum]
    push_cast
    rfl
  have hrem := seamWordRationalRemainder_eq_pow_add_floorZ_div (by omega : 1 ≤ s)
    (seamGreedyWord s)
  change seamWordRationalRemainder (seamGreedyWord s)
    = ((2 : ℚ) ^ s + seamGreedyFloorZ s) / (4 : ℚ) ^ s at hrem
  rw [seamGreedyFloorZ_eq_remainder_sub_error s hs] at hrem
  have hkey : (1 : ℝ) / 2 - seamGreedyFiniteValue s
      = ((2 : ℝ) ^ s + (seamIntegerGreedyRemainder s : ℝ)
          - ((seamGreedyFloorError s : ℚ) : ℝ)) / (4 : ℝ) ^ s := by
    rw [← hcast, hrem]
    push_cast
    ring
  unfold seamGreedyNormalizedRemainder
  linear_combination -hkey + half_pow_eq_div s

/-- The floor-error correction is negligible on the quotient scale. -/
theorem tendsto_seamGreedyFloorError_div_atTop :
    Tendsto (fun s : ℕ => ((seamGreedyFloorError s : ℚ) : ℝ) / (4 : ℝ) ^ s)
      atTop (nhds 0) := by
  have hpow : Tendsto (fun s : ℕ => (1 / 2 : ℝ) ^ s) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero' ?_ ?_ hpow
  · filter_upwards [eventually_ge_atTop 3] with s hs
    have h0 : (0 : ℝ) ≤ ((seamGreedyFloorError s : ℚ) : ℝ) := by
      exact_mod_cast (seamGreedyFloorError_nonneg_lt_width hs).1
    positivity
  · filter_upwards [eventually_ge_atTop 3] with s hs
    have hWR : ((seamGreedyFloorError s : ℚ) : ℝ) < ((s - 2 : ℕ) : ℝ) := by
      exact_mod_cast (seamGreedyFloorError_nonneg_lt_width hs).2
    have hnat : (s - 2 : ℕ) < 2 ^ s := lt_of_le_of_lt (Nat.sub_le s 2) Nat.lt_two_pow_self
    have hnatR : ((s - 2 : ℕ) : ℝ) < (2 : ℝ) ^ s := by exact_mod_cast hnat
    have h4pos : (0 : ℝ) < (4 : ℝ) ^ s := by positivity
    rw [half_pow_eq_div s]
    exact (div_le_div_iff_of_pos_right h4pos).2 (le_of_lt (hWR.trans hnatR))

/-! ## The environment, reduced to one missing input -/

/-- Given the convergence of the finite seam values to the greedy value, the
normalised quotient remainders converge to the greedy deficit. -/
theorem tendsto_seamGreedyNormalizedRemainder_of_tendsto
    (htend : Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfValue)) :
    Tendsto seamGreedyNormalizedRemainder atTop (nhds seamGreedyDeficit) := by
  have hpow : Tendsto (fun s : ℕ => (1 / 2 : ℝ) ^ s) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hcomb : Tendsto
      (fun s : ℕ => 1 / 2 - (1 / 2 : ℝ) ^ s - seamGreedyFiniteValue s
        + ((seamGreedyFloorError s : ℚ) : ℝ) / (4 : ℝ) ^ s)
      atTop (nhds (1 / 2 - 0 - greedyHalfValue + 0)) :=
    ((tendsto_const_nhds.sub hpow).sub htend).add tendsto_seamGreedyFloorError_div_atTop
  have heq : (fun s : ℕ => 1 / 2 - (1 / 2 : ℝ) ^ s - seamGreedyFiniteValue s
        + ((seamGreedyFloorError s : ℚ) : ℝ) / (4 : ℝ) ^ s)
      =ᶠ[atTop] seamGreedyNormalizedRemainder := by
    filter_upwards [eventually_ge_atTop 5] with s hs
    exact (seamGreedyNormalizedRemainder_eq s hs).symm
  have hfinal := Filter.Tendsto.congr' heq hcomb
  simpa [seamGreedyDeficit] using hfinal

/-- Long `thm:seam-limit`, conditional on the one missing input: the
unconditional convergence `X_{D_s}(2) → X_G(2)`.  Everything else the
environment asserts is derived here. -/
theorem paper_seam_limit
    (htend : Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfValue)) :
    Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfValue) ∧
      Tendsto seamGreedyNormalizedRemainder atTop (nhds seamGreedyDeficit) ∧
      0 ≤ seamGreedyDeficit ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
        Tendsto seamGreedyNormalizedRemainder atTop (nhds 0)) ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
        ∃ rows : ℕ → ℕ, SeamGreedyRemainderSubquadraticAlong rows) := by
  have hlim := tendsto_seamGreedyNormalizedRemainder_of_tendsto htend
  have hnn : ∀ s : ℕ, 0 ≤ seamGreedyNormalizedRemainder s := by
    intro s
    unfold seamGreedyNormalizedRemainder
    positivity
  have hdelta : 0 ≤ seamGreedyDeficit := ge_of_tendsto' hlim hnn
  refine ⟨htend, hlim, hdelta, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hmem
    have hz : seamGreedyDeficit = 0 := half_mem_iff_seamGreedyDeficit_eq_zero.1 hmem
    rwa [hz] at hlim
  · intro h0
    exact half_mem_iff_seamGreedyDeficit_eq_zero.2 (tendsto_nhds_unique hlim h0)
  · intro hmem
    have hz : seamGreedyDeficit = 0 := half_mem_iff_seamGreedyDeficit_eq_zero.1 hmem
    rw [hz] at hlim
    exact ⟨id, tendsto_id, hlim⟩
  · rintro ⟨rows, hrows⟩
    exact half_mem_mersenneAchievementSet_of_subquadraticAlong rows hrows

#print axioms half_mem_iff_greedyHalfValue_eq
#print axioms half_mem_iff_seamGreedyDeficit_eq_zero
#print axioms seamGreedyFloorError_nonneg_lt_width
#print axioms seamGreedyNormalizedRemainder_eq
#print axioms tendsto_seamGreedyFloorError_div_atTop
#print axioms tendsto_seamGreedyNormalizedRemainder_of_tendsto
#print axioms paper_seam_limit

end ErdosProblems.Erdos257.PaperCompleteR21
