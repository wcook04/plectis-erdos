import Erdos249257.TerminalOnlyCofinal

/-!
# Terminal-only approximation with a scaled-vanishing carry

The square-root strip in `TerminalOnlyCofinal` is one convenient way to make
the terminal carry negligible after division by its binary place value.  It
is not the analytic threshold used by the achievement-set consumer.

This module isolates the weaker invariant.  A sequence of normalized finite
words may use arbitrary terminal carries, provided their absolute values
divided by `2^M` tend to zero.  No coherence and no earlier-row carry control
is required.  The existing cofinal square-root-strip producer maps into this
interface, so the new socket is a genuine weakening rather than a parallel
restatement.
-/

namespace Erdos249257.HalfCarryReachability

open Filter Set

/-- A terminal word is close to `1/2` by the sum of two normalized errors:
its absolute terminal carry and the universal support-coefficient tail. -/
theorem dist_half_erdosSupportSeries_wordSupport_le_carry_add_tail
    {M : ℕ} (hM : 1 ≤ M) {a : HalfWord M}
    (hone : ∀ h : 1 < M + 1, a ⟨1, h⟩ = false) :
    dist (erdosSupportSeries 2 (wordSupport a)) (1 / 2 : ℝ) ≤
      (|(integerHalfCarry (wordSupport a) (M - 1) : ℝ)| +
          (2 * Real.sqrt (M : ℝ) + 4)) /
        (2 : ℝ) ^ M := by
  let A : Set ℕ := wordSupport a
  let K : ℝ := (integerHalfCarry A (M - 1) : ℝ)
  let T : ℝ := binaryCoeffTail (supportCoeff A) M
  let B : ℝ := 2 * Real.sqrt (M : ℝ) + 4
  have honeA : 1 ∉ A :=
    one_not_mem_wordSupport_of_terminalOnlyWitness hone
  have hid0 := integerHalfCarry_eq_scaled_residual_add_tail
    A honeA (M - 1)
  have hindex : M - 1 + 1 = M := Nat.sub_add_cancel hM
  have hid : K = (2 : ℝ) ^ M *
        ((1 : ℝ) / 2 - erdosSupportSeries 2 A) + T := by
    simpa only [K, T, hindex] using hid0
  have hT0 : 0 ≤ T :=
    binaryCoeffTail_nonneg (supportCoeff A) M
  have hTB : T ≤ B :=
    binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A M
  have hpow : 0 < (2 : ℝ) ^ M := by positivity
  have herrorIdentity :
      erdosSupportSeries 2 A - (1 : ℝ) / 2 =
        (T - K) / (2 : ℝ) ^ M := by
    apply (eq_div_iff hpow.ne').2
    nlinarith [hid]
  have hTK : |T - K| ≤ |K| + B := by
    calc
      |T - K| ≤ |T| + |K| := abs_sub T K
      _ = T + |K| := by rw [abs_of_nonneg hT0]
      _ ≤ |K| + B := by linarith
  rw [Real.dist_eq, herrorIdentity, abs_div, abs_of_pos hpow]
  exact div_le_div_of_nonneg_right hTK hpow.le

/-- The universal coefficient-tail envelope is negligible on the binary
scale. -/
theorem tendsto_two_sqrt_add_four_div_pow_zero :
    Tendsto
      (fun M : ℕ ↦
        (2 * Real.sqrt (M : ℝ) + 4) / (2 : ℝ) ^ M)
      atTop (nhds 0) := by
  have hM : Tendsto (fun M : ℕ ↦ (M : ℝ) / (2 : ℝ) ^ M)
      atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
  have hOne : Tendsto (fun M : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ M)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hUpper : Tendsto
      (fun M : ℕ ↦ (2 * (M : ℝ) + 6) / (2 : ℝ) ^ M)
      atTop (nhds 0) := by
    have h := (hM.const_mul 2).add (hOne.const_mul 6)
    convert h using 1
    · funext M
      ring
    · simp
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun M ↦ by positivity)
    (Filter.Eventually.of_forall fun M ↦ ?_)
    hUpper
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsqrt : Real.sqrt (M : ℝ) ≤ (M : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
      nlinarith
  nlinarith

/-- The concrete square-root strip is itself negligible on the binary
scale. -/
theorem tendsto_halfStripBound_div_pow_zero :
    Tendsto
      (fun M : ℕ ↦ (halfStripBound M : ℝ) / (2 : ℝ) ^ M)
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun M ↦ by positivity)
    (Filter.Eventually.of_forall fun M ↦ ?_)
    tendsto_two_sqrt_add_four_div_pow_zero
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsqrtFloor : (Nat.sqrt M : ℝ) ≤ Real.sqrt (M : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  unfold halfStripBound
  push_cast
  gcongr

/-- The weakest sequential terminal-only producer used here.  Depths tend to
infinity, normalization makes every finite value an achievement-set member,
and only the *scaled terminal carry* is required to vanish. -/
structure HalfTerminalOnlyScaledVanishingSequence where
  depth : ℕ → ℕ
  word : ∀ n : ℕ, HalfWord (depth n)
  depth_pos : ∀ n : ℕ, 1 ≤ depth n
  depth_tendsto : Tendsto depth atTop atTop
  zero : ∀ n : ℕ,
    word n ⟨0, Nat.zero_lt_succ (depth n)⟩ = false
  one : ∀ (n : ℕ) (h : 1 < depth n + 1), word n ⟨1, h⟩ = false
  carry_scaled_tendsto :
    Tendsto
      (fun n : ℕ ↦
        |(integerHalfCarry (wordSupport (word n)) (depth n - 1) : ℝ)| /
          (2 : ℝ) ^ (depth n))
      atTop (nhds 0)

/-- Every cofinal square-root-strip family canonically supplies the weaker
scaled-vanishing sequence. -/
noncomputable def
    HalfTerminalOnlyScaledVanishingSequence.ofCofinalTerminalOnlyStrip
    (hcofinal : HalfCarryCofinalTerminalOnlyStrip) :
    HalfTerminalOnlyScaledVanishingSequence := by
  unfold HalfCarryCofinalTerminalOnlyStrip at hcofinal
  choose M hMN hW using hcofinal
  simp only [HalfTerminalOnlyStripWitness] at hW
  choose a hzero hone hcarry using hW
  have hM1 : ∀ N : ℕ, 1 ≤ M N := by
    intro N
    exact (le_max_right N 1).trans (hMN N)
  have hMtop : Tendsto M atTop atTop :=
    tendsto_atTop_mono
      (fun N ↦ (le_max_left N 1).trans (hMN N)) tendsto_id
  refine
    { depth := M
      word := a
      depth_pos := hM1
      depth_tendsto := hMtop
      zero := hzero
      one := hone
      carry_scaled_tendsto := ?_ }
  have hstrip := tendsto_halfStripBound_div_pow_zero.comp hMtop
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N ↦ by positivity)
    (Filter.Eventually.of_forall fun N ↦ ?_)
    hstrip
  apply div_le_div_of_nonneg_right (hcarry N) (by positivity)

/-- **Scaled-terminal consumer.**  Vanishing of the normalized terminal carry
already puts `1/2` in the Mersenne achievement set. -/
theorem half_mem_mersenneAchievementSet_of_terminalScaledVanishing
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  let y : ℕ → ℝ := fun n ↦
    erdosSupportSeries 2 (wordSupport (S.word n))
  have htail : Tendsto
      (fun n : ℕ ↦
        (2 * Real.sqrt (S.depth n : ℝ) + 4) /
          (2 : ℝ) ^ (S.depth n))
      atTop (nhds 0) :=
    tendsto_two_sqrt_add_four_div_pow_zero.comp S.depth_tendsto
  have hupper : Tendsto
      (fun n : ℕ ↦
        |(integerHalfCarry (wordSupport (S.word n))
              (S.depth n - 1) : ℝ)| /
            (2 : ℝ) ^ (S.depth n) +
          (2 * Real.sqrt (S.depth n : ℝ) + 4) /
            (2 : ℝ) ^ (S.depth n))
      atTop (nhds 0) := by
    simpa using S.carry_scaled_tendsto.add htail
  have hdist : Tendsto (fun n : ℕ ↦ dist (y n) (1 / 2 : ℝ))
      atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n ↦ dist_nonneg)
      (Filter.Eventually.of_forall fun n ↦ ?_)
      hupper
    calc
      dist (y n) (1 / 2 : ℝ) ≤
          (|(integerHalfCarry (wordSupport (S.word n))
                (S.depth n - 1) : ℝ)| +
              (2 * Real.sqrt (S.depth n : ℝ) + 4)) /
            (2 : ℝ) ^ (S.depth n) := by
        exact
          dist_half_erdosSupportSeries_wordSupport_le_carry_add_tail
            (S.depth_pos n) (S.one n)
      _ =
          |(integerHalfCarry (wordSupport (S.word n))
                (S.depth n - 1) : ℝ)| /
              (2 : ℝ) ^ (S.depth n) +
            (2 * Real.sqrt (S.depth n : ℝ) + 4) /
              (2 : ℝ) ^ (S.depth n) := by ring
  have hy : Tendsto y atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.2 hdist
  have hyMem : ∀ n : ℕ, y n ∈ mersenneAchievementSet := by
    intro n
    have hA0 : 0 ∉ wordSupport (S.word n) :=
      zero_not_mem_wordSupport_of_terminalOnlyWitness (S.zero n)
    refine ⟨wordSupport (S.word n), hA0, ?_⟩
    simp only [y]
    exact (positiveMersenneSupportValue_eq_erdosSupportSeries _).symm
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall hyMem)

/-- The scaled-terminal producer yields an infinite support summing exactly
to `1/2`. -/
theorem exists_infinite_support_half_of_terminalScaledVanishing
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  have hhalf := half_mem_mersenneAchievementSet_of_terminalScaledVanishing S
  rcases hhalf with ⟨A, hA0, hvalue⟩
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue.symm
  refine ⟨A, ?_, hseries⟩
  intro hfinite
  exact finite_boolSupport_ne_half A hfinite hA0 hseries

/-- Compatibility theorem: the old square-root-strip hypothesis is a
special case of the new scaled-terminal consumer. -/
theorem half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip_via_scaled
    (hcofinal : HalfCarryCofinalTerminalOnlyStrip) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_terminalScaledVanishing
    (.ofCofinalTerminalOnlyStrip hcofinal)

#print axioms dist_half_erdosSupportSeries_wordSupport_le_carry_add_tail
#print axioms tendsto_two_sqrt_add_four_div_pow_zero
#print axioms HalfTerminalOnlyScaledVanishingSequence.ofCofinalTerminalOnlyStrip
#print axioms half_mem_mersenneAchievementSet_of_terminalScaledVanishing
#print axioms exists_infinite_support_half_of_terminalScaledVanishing

end Erdos249257.HalfCarryReachability
