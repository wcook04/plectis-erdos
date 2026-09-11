import Erdos249257.HalfCarryReachability

/-!
# Cofinal square-root-strip returns close the greedy half target

The existing greedy consumer asks for a uniform square-root bound on the
Möbius-centred half carry.  The uncentred carry has an extra monotonicity
which makes that stronger than necessary: after division by `2^N`, every
support coefficient subtracts a nonnegative amount.  Consequently,
cofinally many returns to the square-root strip already force the whole
scaled carry to tend to zero.

This file is a read-only scratch candidate.  It does not claim the required
cofinal returns; it isolates them as a strictly weaker producer socket.
-/

namespace Erdos249257.HalfCarryReachability

open Filter Set

/-- The uncentred integer half carry, scaled by its binary place value, is
antitone for every support. -/
theorem scaled_integerHalfCarry_antitone (A : Set ℕ) :
    Antitone (fun N : ℕ ↦
      (integerHalfCarry A N : ℝ) / (2 : ℝ) ^ N) := by
  apply antitone_nat_of_succ_le
  intro N
  rw [integerHalfCarry_succ, pow_succ]
  push_cast
  calc
    (2 * (integerHalfCarry A N : ℝ) -
          (supportCoeff A (N + 2) : ℝ)) /
        ((2 : ℝ) ^ N * 2) =
      (integerHalfCarry A N : ℝ) / (2 : ℝ) ^ N -
        (supportCoeff A (N + 2) : ℝ) /
          ((2 : ℝ) ^ N * 2) := by ring
    _ ≤ (integerHalfCarry A N : ℝ) / (2 : ℝ) ^ N :=
      sub_le_self _ (by positivity)

/-- The concrete strip envelope is subexponential even when indexed at the
successor row corresponding to `integerHalfCarry A N`. -/
theorem tendsto_halfStripBound_succ_div_pow_zero :
    Tendsto
      (fun N : ℕ ↦
        (halfStripBound (N + 1) : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
  have hN : Tendsto (fun N : ℕ ↦ (N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
  have hOne : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hUpper : Tendsto
      (fun N : ℕ ↦ (2 * (N : ℝ) + 6) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    have h := (hN.const_mul 2).add (hOne.const_mul 6)
    convert h using 1
    · funext N
      ring
    · simp
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N ↦ by positivity)
    (Filter.Eventually.of_forall fun N ↦ ?_)
    hUpper
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsqrt : Nat.sqrt (N + 1) ≤ N + 1 := Nat.sqrt_le_self _
  have hnat : halfStripBound (N + 1) ≤ 2 * N + 6 := by
    unfold halfStripBound
    omega
  exact_mod_cast hnat

/-- The actual greedy half carry returns to the square-root strip beyond
every requested index.  This is weaker than an all-level strip bound. -/
def GreedyHalfCarryCofinalStripReturn : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
    integerHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) M ≤
      (halfStripBound (M + 1) : ℤ)

/-- Cofinal strip returns force the entire scaled uncentred greedy carry to
zero.  Antitonicity is the fan-in: after one late return, every still later
scaled state is no larger. -/
theorem greedy_integerHalfCarry_scaled_tendsto_zero_of_cofinalStripReturn
    (hreturn : GreedyHalfCarryCofinalStripReturn) :
    Tendsto
      (fun N : ℕ ↦
        (integerHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) /
          (2 : ℝ) ^ N)
      atTop (nhds 0) := by
  let G := greedyMersenneSupport (1 / 2 : ℝ)
  let f : ℕ → ℝ := fun N ↦
    (integerHalfCarry G N : ℝ) / (2 : ℝ) ^ N
  let b : ℕ → ℝ := fun N ↦
    (halfStripBound (N + 1) : ℝ) / (2 : ℝ) ^ N
  have hanti : Antitone f := by
    simpa [f, G] using scaled_integerHalfCarry_antitone G
  have hb : Tendsto b atTop (nhds 0) := by
    simpa [b] using tendsto_halfStripBound_succ_div_pow_zero
  have hnonneg : ∀ N : ℕ, 0 ≤ f N := by
    intro N
    have hcenter := greedy_mobiusCenteredHalfCarry_nonneg N
    have hcarry : (0 : ℤ) ≤ integerHalfCarry G N := by
      dsimp [G]
      unfold mobiusCenteredHalfCarry at hcenter
      omega
    exact div_nonneg (by exact_mod_cast hcarry) (by positivity)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hb ε hε
  obtain ⟨M, hN₀M, hM⟩ := hreturn N₀
  change integerHalfCarry G M ≤ (halfStripBound (M + 1) : ℤ) at hM
  have hMf : f M ≤ b M := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hM
  have hbM : b M < ε := by
    have hdist := hN₀ M hN₀M
    have hbnonneg : 0 ≤ b M := by positivity
    simpa [Real.dist_eq, abs_of_nonneg hbnonneg] using hdist
  refine ⟨M, ?_⟩
  intro N hMN
  have hfN : f N < ε := lt_of_le_of_lt
    ((hanti hMN).trans hMf) hbM
  have hfnonneg := hnonneg N
  change dist (f N) 0 < ε
  simpa [Real.dist_eq, abs_of_nonneg hfnonneg] using hfN

/-- Cofinal returns to the square-root strip already give an infinite
canonical greedy support with exact Mersenne support-series value `1/2`. -/
theorem greedy_half_infinite_of_cofinalStripReturn
    (hreturn : GreedyHalfCarryCofinalStripReturn) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  have hcarry :=
    greedy_integerHalfCarry_scaled_tendsto_zero_of_cofinalStripReturn hreturn
  have hgeom : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hcentered : Tendsto
      (fun N : ℕ ↦
        (mobiusCenteredHalfCarry
          (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) /
            (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    have h := hcarry.sub hgeom
    convert h using 1
    · funext N
      unfold mobiusCenteredHalfCarry
      push_cast
      ring
    · simp
  exact greedy_half_infinite_of_mobiusCenteredHalfCarry_tempered hcentered

/-- Achievement-set form of the same closure lemma. -/
theorem half_mem_mersenneAchievementSet_of_cofinalStripReturn
    (hreturn : GreedyHalfCarryCofinalStripReturn) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  have h := greedy_half_infinite_of_cofinalStripReturn hreturn
  refine ⟨greedyMersenneSupport (1 / 2 : ℝ),
    zero_not_mem_greedyMersenneSupport _, ?_⟩
  rw [positiveMersenneSupportValue_eq_erdosSupportSeries]
  exact h.2.symm

end Erdos249257.HalfCarryReachability
