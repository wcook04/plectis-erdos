import Erdos249257.HalfCylinderFloorErrorReset

/-!
# Closed-set seam-limit route for the half target

The actual rational greedy orbit is not needed if the integer seam words
themselves approach the half target.  This module makes that alternate route
exact.  It proves that the empirical exponential remainder bound

`seamIntegerGreedyRemainder s < 2^(s+1)`

forces the finite seam support values to converge to `1/2`; closedness of the
Mersenne achievement set then gives exact membership.  The bound is exposed
as an honest socket and is not asserted here.
-/

namespace Erdos249257

open Set Filter
open HalfCylinderIntegerGreedy

/-! ## Finite seam values -/

/-- The real achievement-set point coded by the integer-greedy seam word. -/
noncomputable def seamGreedyFiniteValue (s : ℕ) : ℝ :=
  positiveMersenneSupportValue
    (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)

theorem zero_not_mem_seamWordSupport
    {s : ℕ} (b : SeamRowWord s) :
    0 ∉ seamWordSupport b := by
  intro hzero
  have hbelow := seamWordSupport_below hzero
  omega

theorem seamGreedyFiniteValue_mem_achievementSet (s : ℕ) :
    seamGreedyFiniteValue s ∈ mersenneAchievementSet := by
  refine ⟨(↑(seamWordSupport (seamGreedyWord s)) : Set ℕ), ?_, rfl⟩
  simpa using zero_not_mem_seamWordSupport (seamGreedyWord s)

theorem seamGreedyFiniteValue_eq_cast_rationalSum (s : ℕ) :
    seamGreedyFiniteValue s =
      ((seamWordRationalSum (seamGreedyWord s) : ℚ) : ℝ) := by
  unfold seamGreedyFiniteValue seamWordRationalSum
  exact positiveMersenneSupportValue_eq_cast_finiteErdosSum _

/-! ## The minimal cofinal subquadratic route -/

/-- Integer seam remainder normalized by the row-square scale. -/
noncomputable def seamGreedyNormalizedRemainder (s : ℕ) : ℝ :=
  (seamIntegerGreedyRemainder s : ℝ) / (4 : ℝ) ^ s

/-- A cofinal row sequence along which the normalized seam remainder
vanishes.  This is strictly weaker than a uniform exponential bound. -/
def SeamGreedyRemainderSubquadraticAlong (rows : ℕ → ℕ) : Prop :=
  Tendsto rows atTop atTop ∧
    Tendsto (fun j => seamGreedyNormalizedRemainder (rows j))
      atTop (nhds 0)

/-- The finite seam error is bounded by its dyadic target correction plus
the normalized integer remainder. -/
theorem seamGreedyRationalRemainder_general_bounds
    (s : ℕ) (hs : 5 ≤ s) :
    0 ≤ seamWordRationalRemainder (seamGreedyWord s) ∧
      seamWordRationalRemainder (seamGreedyWord s) ≤
        (1 / 2 : ℚ) ^ s +
          (seamIntegerGreedyRemainder s : ℚ) / (4 : ℚ) ^ s := by
  let a : ℚ := (2 : ℚ) ^ s
  have ha : 0 < a := by positivity
  have hfour : (4 : ℚ) ^ s = a ^ 2 := by
    simpa [a] using four_pow_eq_two_pow_sq s
  have hPhi0 : 0 ≤ seamGreedyFloorError s :=
    seamWordFloorError_nonneg (seamGreedyWord s)
  have hPhiWidth :=
    seamWordFloorError_lt_width (by omega : 3 ≤ s) (seamGreedyWord s)
  have hwidthPowNat : s - 2 < 2 ^ s :=
    lt_of_le_of_lt (Nat.sub_le s 2) Nat.lt_two_pow_self
  have hwidthPow : ((s - 2 : ℕ) : ℚ) < a := by
    dsimp [a]
    exact_mod_cast hwidthPowNat
  have hPhiA : seamGreedyFloorError s < a :=
    hPhiWidth.trans hwidthPow
  have hR0 : (0 : ℚ) ≤ seamIntegerGreedyRemainder s := by positivity
  have hZ := seamGreedyFloorZ_eq_remainder_sub_error s hs
  have hrem := seamWordRationalRemainder_eq_pow_add_floorZ_div
    (by omega : 1 ≤ s) (seamGreedyWord s)
  change seamWordRationalRemainder (seamGreedyWord s) =
    ((2 : ℚ) ^ s + seamGreedyFloorZ s) / (4 : ℚ) ^ s at hrem
  rw [hZ] at hrem
  rw [hrem]
  constructor
  · have hnum :
        0 ≤ (2 : ℚ) ^ s +
          ((seamIntegerGreedyRemainder s : ℚ) -
            seamGreedyFloorError s) := by
      change 0 ≤ a +
        ((seamIntegerGreedyRemainder s : ℚ) - seamGreedyFloorError s)
      linarith
    exact div_nonneg hnum (by positivity)
  · calc
      ((2 : ℚ) ^ s +
            ((seamIntegerGreedyRemainder s : ℚ) -
              seamGreedyFloorError s)) / (4 : ℚ) ^ s
          ≤ ((2 : ℚ) ^ s +
              (seamIntegerGreedyRemainder s : ℚ)) / (4 : ℚ) ^ s := by
            apply (div_le_div_iff_of_pos_right (by positivity)).2
            linarith
      _ = (1 / 2 : ℚ) ^ s +
            (seamIntegerGreedyRemainder s : ℚ) / (4 : ℚ) ^ s := by
          have hinv : (1 / 2 : ℚ) ^ s = 1 / a := by simp [a]
          rw [hinv, hfour]
          have ha0 : a ≠ 0 := ne_of_gt ha
          field_simp [ha0]
          ring

theorem seamGreedyFiniteValue_general_error_bounds
    (s : ℕ) (hs : 5 ≤ s) :
    0 ≤ (1 / 2 : ℝ) - seamGreedyFiniteValue s ∧
      (1 / 2 : ℝ) - seamGreedyFiniteValue s ≤
        (1 / 2 : ℝ) ^ s + seamGreedyNormalizedRemainder s := by
  have hbounds := seamGreedyRationalRemainder_general_bounds s hs
  have hcast :
      ((seamWordRationalRemainder (seamGreedyWord s) : ℚ) : ℝ) =
        (1 / 2 : ℝ) - seamGreedyFiniteValue s := by
    rw [seamWordRationalRemainder,
      seamGreedyFiniteValue_eq_cast_rationalSum]
    push_cast
    rfl
  constructor
  · rw [← hcast]
    exact_mod_cast hbounds.1
  · rw [← hcast]
    have hupperCast :
        ((seamWordRationalRemainder (seamGreedyWord s) : ℚ) : ℝ) ≤
          (((1 / 2 : ℚ) ^ s +
            (seamIntegerGreedyRemainder s : ℚ) / (4 : ℚ) ^ s : ℚ) : ℝ) := by
      exact_mod_cast hbounds.2
    simpa [seamGreedyNormalizedRemainder] using hupperCast

/-- Any cofinal subquadratic seam-remainder subsequence makes the finite seam
supports converge to the half target. -/
theorem tendsto_seamGreedyFiniteValue_half_of_subquadraticAlong
    (rows : ℕ → ℕ)
    (hrows : SeamGreedyRemainderSubquadraticAlong rows) :
    Tendsto (fun j => seamGreedyFiniteValue (rows j))
      atTop (nhds (1 / 2 : ℝ)) := by
  rcases hrows with ⟨hcofinal, hnormalized⟩
  have hpowBase : Tendsto (fun s : ℕ => (1 / 2 : ℝ) ^ s)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
  have hpow : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ (rows j))
      atTop (nhds 0) := hpowBase.comp hcofinal
  have hupper : Tendsto
      (fun j : ℕ =>
        (1 / 2 : ℝ) ^ (rows j) +
          seamGreedyNormalizedRemainder (rows j))
      atTop (nhds 0) := by
    simpa using hpow.add hnormalized
  have hlarge : ∀ᶠ j in atTop, 5 ≤ rows j :=
    hcofinal (eventually_ge_atTop 5)
  have hdiff : Tendsto
      (fun j : ℕ => (1 / 2 : ℝ) - seamGreedyFiniteValue (rows j))
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [hlarge] with j hj
      exact (seamGreedyFiniteValue_general_error_bounds (rows j) hj).1
    · filter_upwards [hlarge] with j hj
      exact (seamGreedyFiniteValue_general_error_bounds (rows j) hj).2
    · exact hupper
  have hconst : Tendsto (fun _j : ℕ => (1 / 2 : ℝ))
      atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have hsub := hconst.sub hdiff
  convert hsub using 1 <;> simp

/-- Closedness converts any cofinal subquadratic seam subsequence into an
exact representation of `1/2`. -/
theorem half_mem_mersenneAchievementSet_of_subquadraticAlong
    (rows : ℕ → ℕ)
    (hrows : SeamGreedyRemainderSubquadraticAlong rows) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact isClosed_mersenneAchievementSet.mem_of_tendsto
    (tendsto_seamGreedyFiniteValue_half_of_subquadraticAlong rows hrows)
    (Filter.Eventually.of_forall fun j =>
      seamGreedyFiniteValue_mem_achievementSet (rows j))

/-! ## The exact upper-bound socket -/

/-- Exponential upper bound observed by exact replay from row six onward.
Its universal proof is the remaining arithmetic producer on this route. -/
def SeamGreedyRemainderGapBound : Prop :=
  ∀ s : ℕ, 6 ≤ s →
    seamIntegerGreedyRemainder s < 2 ^ (s + 1)

/-- Under the gap bound, the exact rational residual is positive and at most
`3 * 2^(-s)`.  This uses only `Phi < s-2` and the exact floor-`Z` identity. -/
theorem seamGreedyRationalRemainder_bounds
    (s : ℕ) (hs : 5 ≤ s)
    (hR : seamIntegerGreedyRemainder s < 2 ^ (s + 1)) :
    0 ≤ seamWordRationalRemainder (seamGreedyWord s) ∧
      seamWordRationalRemainder (seamGreedyWord s) ≤
        3 * (1 / 2 : ℚ) ^ s := by
  let a : ℚ := (2 : ℚ) ^ s
  have ha : 0 < a := by positivity
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hfour : (4 : ℚ) ^ s = a ^ 2 := by
    simpa [a] using four_pow_eq_two_pow_sq s
  have hPhi0 : 0 ≤ seamGreedyFloorError s :=
    seamWordFloorError_nonneg (seamGreedyWord s)
  have hPhiWidth :=
    seamWordFloorError_lt_width (by omega : 3 ≤ s) (seamGreedyWord s)
  have hwidthPowNat : s - 2 < 2 ^ s :=
    lt_of_le_of_lt (Nat.sub_le s 2) Nat.lt_two_pow_self
  have hwidthPow : ((s - 2 : ℕ) : ℚ) < a := by
    dsimp [a]
    exact_mod_cast hwidthPowNat
  have hPhiA : seamGreedyFloorError s < a :=
    hPhiWidth.trans hwidthPow
  have hRQ : (seamIntegerGreedyRemainder s : ℚ) < 2 * a := by
    have hcast :
        (seamIntegerGreedyRemainder s : ℚ) < (2 ^ (s + 1) : ℕ) := by
      exact_mod_cast hR
    simpa [a, pow_succ, mul_comm] using hcast
  have hR0 : (0 : ℚ) ≤ seamIntegerGreedyRemainder s := by positivity
  have hZ := seamGreedyFloorZ_eq_remainder_sub_error s hs
  have hZlow : -a < seamGreedyFloorZ s := by
    rw [hZ]
    linarith
  have hZhigh : seamGreedyFloorZ s < 2 * a := by
    rw [hZ]
    linarith
  have hrem := seamWordRationalRemainder_eq_pow_add_floorZ_div
    (by omega : 1 ≤ s) (seamGreedyWord s)
  change seamWordRationalRemainder (seamGreedyWord s) =
    ((2 : ℚ) ^ s + seamGreedyFloorZ s) / (4 : ℚ) ^ s at hrem
  rw [hfour] at hrem
  rw [hrem]
  constructor
  · exact div_nonneg (by linarith) ha2.le
  · have hnum : a + seamGreedyFloorZ s < 3 * a := by linarith
    have hdiv :
        (a + seamGreedyFloorZ s) / a ^ 2 < (3 * a) / a ^ 2 :=
      (div_lt_div_iff_of_pos_right ha2).2 hnum
    have hinv : (1 / 2 : ℚ) ^ s = 1 / a := by
      simp [a]
    have heq : (3 * a) / a ^ 2 = 3 * (1 / 2 : ℚ) ^ s := by
      rw [hinv]
      field_simp
    exact hdiv.le.trans_eq heq

theorem seamGreedyFiniteValue_error_bounds
    (s : ℕ) (hs : 5 ≤ s)
    (hR : seamIntegerGreedyRemainder s < 2 ^ (s + 1)) :
    0 ≤ (1 / 2 : ℝ) - seamGreedyFiniteValue s ∧
      (1 / 2 : ℝ) - seamGreedyFiniteValue s ≤
        3 * (1 / 2 : ℝ) ^ s := by
  have hbounds := seamGreedyRationalRemainder_bounds s hs hR
  have hcast :
      ((seamWordRationalRemainder (seamGreedyWord s) : ℚ) : ℝ) =
        (1 / 2 : ℝ) - seamGreedyFiniteValue s := by
    rw [seamWordRationalRemainder,
      seamGreedyFiniteValue_eq_cast_rationalSum]
    push_cast
    rfl
  constructor
  · rw [← hcast]
    exact_mod_cast hbounds.1
  · rw [← hcast]
    have hupperCast :
        ((seamWordRationalRemainder (seamGreedyWord s) : ℚ) : ℝ) ≤
          ((3 * (1 / 2 : ℚ) ^ s : ℚ) : ℝ) := by
      exact_mod_cast hbounds.2
    simpa using hupperCast

/-! ## Convergence and exact membership -/

theorem tendsto_seamGreedyFiniteValue_half
    (hgap : SeamGreedyRemainderGapBound) :
    Tendsto seamGreedyFiniteValue atTop (nhds (1 / 2 : ℝ)) := by
  have hpow : Tendsto (fun s : ℕ => 3 * (1 / 2 : ℝ) ^ s)
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 3
  have hdiff : Tendsto
      (fun s : ℕ => (1 / 2 : ℝ) - seamGreedyFiniteValue s)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 6] with s hs
      exact (seamGreedyFiniteValue_error_bounds s (by omega) (hgap s hs)).1
    · filter_upwards [eventually_ge_atTop 6] with s hs
      exact (seamGreedyFiniteValue_error_bounds s (by omega) (hgap s hs)).2
    · exact hpow
  have hconst : Tendsto (fun _s : ℕ => (1 / 2 : ℝ))
      atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  have hsub := hconst.sub hdiff
  convert hsub using 1 <;> simp

/-- Closedness converts the convergent sequence of finite seam supports into
an exact representation of `1/2`. -/
theorem half_mem_mersenneAchievementSet_of_seamRemainderGapBound
    (hgap : SeamGreedyRemainderGapBound) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact isClosed_mersenneAchievementSet.mem_of_tendsto
    (tendsto_seamGreedyFiniteValue_half hgap)
    (Filter.Eventually.of_forall seamGreedyFiniteValue_mem_achievementSet)

#print axioms seamGreedyRationalRemainder_bounds
#print axioms seamGreedyRationalRemainder_general_bounds
#print axioms tendsto_seamGreedyFiniteValue_half_of_subquadraticAlong
#print axioms half_mem_mersenneAchievementSet_of_subquadraticAlong
#print axioms tendsto_seamGreedyFiniteValue_half
#print axioms half_mem_mersenneAchievementSet_of_seamRemainderGapBound

end Erdos249257
