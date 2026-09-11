import Erdos249257.HalfCarryReachability

/-!
# Terminal-only cofinal approximation for Erdos 257

This scratch module isolates a weaker producer than
`HalfCarryCofinalAdmissibility`.  Witness words at different depths need not
be coherent, and no carry bound is assumed before the terminal row.  A
cofinal family of terminal carries in the square-root strip already gives
finite achievement sums converging to `1/2`; closedness of the achievement
set replaces the inverse-system/Konig argument.

This file is an immutable handoff draft.  It was intentionally not passed to
the Lean compiler while another lane owned compiler serialization.
-/

namespace Erdos249257.HalfCarryReachability

open Filter Set

/-- A normalized finite word whose *terminal* integer half-carry is in the
discrete square-root strip.  There is deliberately no all-prefix admissibility
hypothesis here. -/
def HalfTerminalOnlyStripWitness (M : ℕ) : Prop :=
  ∃ a : HalfWord M,
    a ⟨0, Nat.zero_lt_succ M⟩ = false ∧
    (∀ h : 1 < M + 1, a ⟨1, h⟩ = false) ∧
    |(integerHalfCarry (wordSupport a) (M - 1) : ℝ)| ≤
      (halfStripBound M : ℝ)

/-- Terminal-only square-root-strip witnesses exist at cofinally many
depths.  The `max N 1` guard makes the terminal index `M - 1` line up with
the scaled-residual identity at exponent `M`. -/
def HalfCarryCofinalTerminalOnlyStrip : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, max N 1 ≤ M ∧ HalfTerminalOnlyStripWitness M

/-- The zero bit of a normalized terminal-only witness is absent from its
finite support. -/
theorem zero_not_mem_wordSupport_of_terminalOnlyWitness
    {M : ℕ} {a : HalfWord M}
    (hzero : a ⟨0, Nat.zero_lt_succ M⟩ = false) :
    0 ∉ wordSupport a := by
  intro hmem
  rcases hmem with ⟨h, htrue⟩
  have hfin : (⟨0, h⟩ : Fin (M + 1)) =
      ⟨0, Nat.zero_lt_succ M⟩ := Fin.ext (by rfl)
  rw [hfin, hzero] at htrue
  simp at htrue

/-- The exponent-one bit of a normalized terminal-only witness is absent
from its finite support. -/
theorem one_not_mem_wordSupport_of_terminalOnlyWitness
    {M : ℕ} {a : HalfWord M}
    (hone : ∀ h : 1 < M + 1, a ⟨1, h⟩ = false) :
    1 ∉ wordSupport a := by
  intro hmem
  rcases hmem with ⟨h, htrue⟩
  rw [hone h] at htrue
  simp at htrue

/-- Pointwise approximation estimate.  A terminal-only strip witness at
positive depth gives a finite support value within

`(4*M + 12) / 2^M`

of `1/2`.  The constant combines the discrete terminal strip with the
existing analytic support-coefficient-tail bound. -/
theorem dist_half_erdosSupportSeries_wordSupport_le_of_terminalOnlyWitness
    {M : ℕ} (hM : 1 ≤ M) {a : HalfWord M}
    (hone : ∀ h : 1 < M + 1, a ⟨1, h⟩ = false)
    (hcarry : |(integerHalfCarry (wordSupport a) (M - 1) : ℝ)| ≤
      (halfStripBound M : ℝ)) :
    dist (erdosSupportSeries 2 (wordSupport a)) (1 / 2 : ℝ) ≤
      (4 * (M : ℝ) + 12) / (2 : ℝ) ^ M := by
  let A : Set ℕ := wordSupport a
  let K : ℝ := (integerHalfCarry A (M - 1) : ℝ)
  let T : ℝ := binaryCoeffTail (supportCoeff A) M
  let B : ℝ := 2 * Real.sqrt (M : ℝ) + 4
  have honeA : 1 ∉ A := by
    exact one_not_mem_wordSupport_of_terminalOnlyWitness hone
  have hid0 := integerHalfCarry_eq_scaled_residual_add_tail
    A honeA (M - 1)
  have hindex : M - 1 + 1 = M := Nat.sub_add_cancel hM
  have hid : K = (2 : ℝ) ^ M *
        ((1 : ℝ) / 2 - erdosSupportSeries 2 A) + T := by
    simpa only [K, T, hindex] using hid0
  have hT0 : 0 ≤ T := by
    exact binaryCoeffTail_nonneg (supportCoeff A) M
  have hTB : T ≤ B := by
    exact binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A M
  have hsqrtFloor : (Nat.sqrt M : ℝ) ≤ Real.sqrt (M : ℝ) := by
    exact Real.nat_sqrt_le_real_sqrt
  have hstripB : (halfStripBound M : ℝ) ≤ B := by
    unfold halfStripBound B
    push_cast
    gcongr
  have hKB : |K| ≤ B := by
    exact hcarry.trans hstripB
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hTK : |T - K| ≤ 2 * B := by
    rw [abs_le]
    constructor
    · have hKupper : K ≤ B := le_trans (le_abs_self K) hKB
      nlinarith
    · have hKlower : -B ≤ K := (abs_le.mp hKB).1
      nlinarith
  have hsqrtLinear : Real.sqrt (M : ℝ) ≤ (M : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
      nlinarith
  have hTKlinear : |T - K| ≤ 4 * (M : ℝ) + 12 := by
    calc
      |T - K| ≤ 2 * B := hTK
      _ ≤ 4 * (M : ℝ) + 12 := by
        dsimp [B]
        nlinarith
  have hpow : 0 < (2 : ℝ) ^ M := by positivity
  have herrorIdentity :
      erdosSupportSeries 2 A - (1 : ℝ) / 2 =
        (T - K) / (2 : ℝ) ^ M := by
    apply (eq_div_iff hpow.ne').2
    nlinarith [hid]
  rw [Real.dist_eq, herrorIdentity, abs_div, abs_of_pos hpow]
  exact div_le_div_of_nonneg_right hTKlinear hpow.le

/-- **Terminal-only cofinal consumer.**  Cofinal square-root-strip terminal
witnesses force `1/2` into the Mersenne achievement set.  Unlike
`exists_infinite_support_half_of_cofinalAdmissibility`, this theorem assumes
neither coherent witnesses nor strip control at any earlier row. -/
theorem half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip
    (hcofinal : HalfCarryCofinalTerminalOnlyStrip) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  unfold HalfCarryCofinalTerminalOnlyStrip at hcofinal
  choose M hMN hW using hcofinal
  simp only [HalfTerminalOnlyStripWitness] at hW
  choose a hzero hone hcarry using hW
  let y : ℕ → ℝ := fun N => erdosSupportSeries 2 (wordSupport (a N))
  have hM1 : ∀ N : ℕ, 1 ≤ M N := by
    intro N
    exact (le_max_right N 1).trans (hMN N)
  have hMtop : Tendsto M atTop atTop := by
    exact tendsto_atTop_mono
      (fun N => (le_max_left N 1).trans (hMN N)) tendsto_id
  have hNlim : Tendsto (fun N : ℕ => (N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
  have h1lim : Tendsto (fun N : ℕ => (1 : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hlinear : Tendsto
      (fun N : ℕ => (4 * (N : ℝ) + 12) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    have h := (hNlim.const_mul 4).add (h1lim.const_mul 12)
    convert h using 1
    · funext N
      ring
    · simp
  have hlinearM : Tendsto
      (fun N : ℕ => (4 * (M N : ℝ) + 12) / (2 : ℝ) ^ (M N))
      atTop (nhds 0) := by
    simpa using hlinear.comp hMtop
  have hdist : Tendsto (fun N : ℕ => dist (y N) (1 / 2 : ℝ))
      atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun N => dist_nonneg)
      (Filter.Eventually.of_forall fun N => ?_)
      hlinearM
    exact dist_half_erdosSupportSeries_wordSupport_le_of_terminalOnlyWitness
      (hM1 N) (hone N) (hcarry N)
  have hy : Tendsto y atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.2 hdist
  have hyMem : ∀ N : ℕ, y N ∈ mersenneAchievementSet := by
    intro N
    have hA0 : 0 ∉ wordSupport (a N) :=
      zero_not_mem_wordSupport_of_terminalOnlyWitness (hzero N)
    refine ⟨wordSupport (a N), hA0, ?_⟩
    simp only [y]
    exact (positiveMersenneSupportValue_eq_erdosSupportSeries _).symm
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall hyMem)

/-- The terminal-only cofinal producer yields an infinite normalized support
summing exactly to `1/2`.  Infinitude follows from the existing odd-
denominator obstruction for finite Boolean supports. -/
theorem exists_infinite_support_half_of_cofinalTerminalOnlyStrip
    (hcofinal : HalfCarryCofinalTerminalOnlyStrip) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  have hhalf :=
    half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip hcofinal
  rcases hhalf with ⟨A, hA0, hvalue⟩
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue.symm
  refine ⟨A, ?_, hseries⟩
  intro hfinite
  exact finite_boolSupport_ne_half A hfinite hA0 hseries

#print axioms half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip
#print axioms exists_infinite_support_half_of_cofinalTerminalOnlyStrip

end Erdos249257.HalfCarryReachability
