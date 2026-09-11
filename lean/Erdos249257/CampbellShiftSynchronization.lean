import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCutLocator

/-!
# Campbell forcing versus a last greedy skip

This companion isolates the part of Packet 5 that is already theorem-grade
without formalizing the Alford--Granville--Pomerance prime-distribution input.

For the actual greedy orbit at `1 / 2`, a putative last skipped exponent `M`
determines a finite rational Mersenne shift.  We prove the exact one-sided
fatal interval for that shift, its centered shadow form, and the resulting
dyadic window below `1 / 2`.  Separately, we prove the elementary parameter
contradiction which rules out synchronizing Campbell's `1/4`-exponent prime
progression by adjoining the shift period.

These theorems do not prove infinitely many skips.  The final section also
closes the logical status of the previously proposed shifted-zero interface:
because its window inequality is guarded by a last-skip hypothesis, it is
equivalent to the endpoint itself.  A future Campbell input must therefore
be nonvacuous (for example, a window theorem without that antecedent), not a
repackaging of `GreedyShiftWindowZero`.
-/

namespace Erdos249257

open Set

open scoped ENNReal

open scoped Classical in
/-- The skipped exponents visible through level `M`. -/
noncomputable def halfSkippedPrefix (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter
    (fun m => m ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ))

/-- The Mersenne-rational shift carried by a finite set of exponents. -/
noncomputable def finiteMersenneShift (F : Finset ℕ) : ℝ :=
  positiveMersenneSupportValue (↑F : Set ℕ)

/-- `M` is the final exponent skipped by the actual greedy half orbit. -/
def IsLastHalfGreedySkip (M : ℕ) : Prop :=
  M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) ∧
    ∀ m, M < m → m ∉ greedyMersenneSkippedSupport (1 / 2 : ℝ)

theorem isLastHalfGreedySkip_pos {M : ℕ} (hlast : IsLastHalfGreedySkip M) :
    0 < M := by
  by_contra hM
  have hzero : M = 0 := by omega
  subst M
  exact zero_not_mem_greedyMersenneSkippedSupport (1 / 2 : ℝ) hlast.1

/-- Under a last-skip hypothesis, the finite prefix is the complete skipped
support. -/
theorem coe_halfSkippedPrefix_eq_skippedSupport
    {M : ℕ} (hlast : IsLastHalfGreedySkip M) :
    (↑(halfSkippedPrefix M) : Set ℕ) =
      greedyMersenneSkippedSupport (1 / 2 : ℝ) := by
  classical
  ext m
  simp only [halfSkippedPrefix, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · exact fun hm => hm.2
  · intro hm
    refine ⟨?_, hm⟩
    by_contra hnot
    have hMm : M < m := by omega
    exact hlast.2 m hMm hm

/-- A finite Mersenne shift is visibly rational. -/
theorem finiteMersenneShift_eq_cast_finiteErdosSum (F : Finset ℕ) :
    finiteMersenneShift F = ((finiteErdosSum F 2 : ℚ) : ℝ) := by
  exact positiveMersenneSupportValue_eq_cast_finiteErdosSum F

/-- After a last skip, every term in the remaining suffix is selected. -/
theorem halfGreedySupportSuffix_eq_tail_of_lastSkip
    {M : ℕ} (hlast : IsLastHalfGreedySkip M) :
    positiveMersenneSupportSuffix
        (greedyMersenneSupport (1 / 2 : ℝ)) M = mersenneTail M := by
  unfold positiveMersenneSupportSuffix mersenneTail
  apply tsum_congr
  intro k
  have hnotSkip :
      M + k + 1 ∉ greedyMersenneSkippedSupport (1 / 2 : ℝ) :=
    hlast.2 (M + k + 1) (by omega)
  have hselected :
      M + k + 1 ∈ greedyMersenneSupport (1 / 2 : ℝ) := by
    by_contra hnotSelected
    apply hnotSkip
    exact ⟨by omega, hnotSelected⟩
  rw [Set.indicator_of_mem hselected]

/-- The full selected value is the finite selected prefix plus the complete
tail after a last skip. -/
theorem halfGreedySupportValue_eq_prefix_add_tail_of_lastSkip
    {M : ℕ} (hlast : IsLastHalfGreedySkip M) :
    positiveMersenneSupportValue
        (greedyMersenneSupport (1 / 2 : ℝ)) =
      halfGreedyMersennePrefix M + mersenneTail M := by
  rw [positiveMersenneSupportValue_eq_prefix_add_suffix]
  rw [halfGreedySupportSuffix_eq_tail_of_lastSkip hlast]
  rfl

/-- Exact fatal coordinate: the finite-shift displacement is the residual
excess above the remaining tail. -/
theorem lastHalfSkip_shiftDelta_eq_remainder_sub_tail
    {M : ℕ} (hlast : IsLastHalfGreedySkip M) :
    (1 / 2 : ℝ) + finiteMersenneShift (halfSkippedPrefix M) -
        erdosBorweinMersenneConstant =
      greedyMersenneRemainder (1 / 2 : ℝ) M - mersenneTail M := by
  have hpartition :=
    erdosBorweinMersenneConstant_eq_greedy_add_skipped (1 / 2 : ℝ)
  have hcoe := coe_halfSkippedPrefix_eq_skippedSupport hlast
  have hshift :
      positiveMersenneSupportValue
          (greedyMersenneSkippedSupport (1 / 2 : ℝ)) =
        finiteMersenneShift (halfSkippedPrefix M) := by
    unfold finiteMersenneShift
    rw [hcoe]
  have hselected :=
    halfGreedySupportValue_eq_prefix_add_tail_of_lastSkip hlast
  have hprefix := greedyMersenne_prefix_add_remainder (1 / 2 : ℝ) M
  change (1 / 2 : ℝ) = halfGreedyMersennePrefix M +
    greedyMersenneRemainder (1 / 2 : ℝ) M at hprefix
  rw [hshift, hselected] at hpartition
  linarith

/-- The last skipped branch leaves the level-`M` residual below `w_M`. -/
theorem lastHalfSkip_remainder_lt_weight
    {M : ℕ} (hlast : IsLastHalfGreedySkip M) :
    greedyMersenneRemainder (1 / 2 : ℝ) M < mersenneWeight M := by
  rcases M with _ | m
  · exact False.elim
      (zero_not_mem_greedyMersenneSkippedSupport (1 / 2 : ℝ) hlast.1)
  · have hskip :
        ¬ mersenneWeight (m + 1) ≤
          greedyMersenneRemainder (1 / 2 : ℝ) m :=
      (succ_mem_greedyMersenneSkippedSupport_iff (1 / 2 : ℝ) m).1 hlast.1
    rw [greedyMersenneRemainder_succ, if_neg hskip]
    exact lt_of_not_ge hskip

/-- After a last skip the greedy orbit selects every later exponent, so the
partial tail sums telescope inside the level-`M` residual: the complete tail
is at most the residual. -/
theorem lastHalfSkip_tail_le_remainder
    {M : ℕ} (hlast : IsLastHalfGreedySkip M) :
    mersenneTail M ≤ greedyMersenneRemainder (1 / 2 : ℝ) M := by
  have hstep : ∀ k : ℕ,
      greedyMersenneRemainder (1 / 2 : ℝ) (M + k)
        = greedyMersenneRemainder (1 / 2 : ℝ) M
          - ∑ i ∈ Finset.range k, mersenneWeight (M + i + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hnotSkip :
            M + k + 1 ∉ greedyMersenneSkippedSupport (1 / 2 : ℝ) :=
          hlast.2 (M + k + 1) (by omega)
        have hsel : mersenneWeight (M + k + 1)
            ≤ greedyMersenneRemainder (1 / 2 : ℝ) (M + k) := by
          by_contra hnot
          exact hnotSkip ((succ_mem_greedyMersenneSkippedSupport_iff
            (1 / 2 : ℝ) (M + k)).2 hnot)
        rw [show M + (k + 1) = (M + k) + 1 by ring,
          greedyMersenneRemainder_succ, if_pos hsel, ih,
          Finset.sum_range_succ]
        ring
  have hpartial : ∀ k : ℕ,
      ∑ i ∈ Finset.range k, mersenneWeight (M + i + 1)
        ≤ greedyMersenneRemainder (1 / 2 : ℝ) M := by
    intro k
    have hnn := greedyMersenneRemainder_nonneg
      (x := (1 / 2 : ℝ)) (by norm_num) (M + k)
    have h := hstep k
    linarith
  unfold mersenneTail
  exact le_of_tendsto' (summable_mersenneTail M).tendsto_sum_tsum_nat hpartial

/-- The finite-shift displacement is nonnegative for a last skip. -/
theorem lastHalfSkip_shiftDelta_nonneg
    {M : ℕ} (hlast : IsLastHalfGreedySkip M) :
    0 ≤ (1 / 2 : ℝ) + finiteMersenneShift (halfSkippedPrefix M) -
      erdosBorweinMersenneConstant := by
  have hdelta := lastHalfSkip_shiftDelta_eq_remainder_sub_tail hlast
  have hle := lastHalfSkip_tail_le_remainder hlast
  linarith

/-- Irrationality excludes equality at the rational centre of the shifted
fatal interval. -/
theorem lastHalfSkip_shiftDelta_ne_zero
    {M : ℕ} (_hlast : IsLastHalfGreedySkip M) :
    (1 / 2 : ℝ) + finiteMersenneShift (halfSkippedPrefix M) -
      erdosBorweinMersenneConstant ≠ 0 := by
  intro hzero
  apply (irrational_erdosBorweinMersenneConstant.ne_rat
    ((1 : ℚ) / 2 + finiteErdosSum (halfSkippedPrefix M) 2))
  have hshift :=
    finiteMersenneShift_eq_cast_finiteErdosSum (halfSkippedPrefix M)
  calc
    erdosBorweinMersenneConstant
        = (1 / 2 : ℝ) + finiteMersenneShift (halfSkippedPrefix M) := by
            linarith
    _ = (((1 : ℚ) / 2 + finiteErdosSum (halfSkippedPrefix M) 2 : ℚ) : ℝ) := by
          rw [hshift]
          push_cast
          norm_num

/-- Exact one-sided fatal interval around the rational shift determined by a
putative last skip. -/
theorem lastHalfSkip_shift_fatalInterval
    {M : ℕ} (hlast : IsLastHalfGreedySkip M) :
    0 < (1 / 2 : ℝ) + finiteMersenneShift (halfSkippedPrefix M) -
          erdosBorweinMersenneConstant ∧
      (1 / 2 : ℝ) + finiteMersenneShift (halfSkippedPrefix M) -
          erdosBorweinMersenneConstant < mersenneGap M := by
  have hnonneg := lastHalfSkip_shiftDelta_nonneg hlast
  have hne := lastHalfSkip_shiftDelta_ne_zero hlast
  have hpos :
      0 < (1 / 2 : ℝ) + finiteMersenneShift (halfSkippedPrefix M) -
        erdosBorweinMersenneConstant := lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hdelta := lastHalfSkip_shiftDelta_eq_remainder_sub_tail hlast
  have hrem := lastHalfSkip_remainder_lt_weight hlast
  constructor
  · exact hpos
  · unfold mersenneGap
    linarith

/-- The `M-1` shadow uses the same gap as the last skipped exponent `M`.
This theorem is the exact index reconciliation for the death-hole picture. -/
theorem lastHalfSkip_shadow_mem_gap
    {M : ℕ} (hlast : IsLastHalfGreedySkip M) :
    |halfGreedyMersenneShadow (M - 1) -
        erdosBorweinMersenneConstant| < mersenneGap M := by
  cases M with
  | zero =>
      exact False.elim
        (zero_not_mem_greedyMersenneSkippedSupport (1 / 2 : ℝ) hlast.1)
  | succ m =>
      have hinterval := lastHalfSkip_shift_fatalInterval hlast
      have hdelta := lastHalfSkip_shiftDelta_eq_remainder_sub_tail hlast
      have hskip :
          ¬ mersenneWeight (m + 1) ≤
            greedyMersenneRemainder (1 / 2 : ℝ) m :=
        (succ_mem_greedyMersenneSkippedSupport_iff (1 / 2 : ℝ) m).1 hlast.1
      have hremEq :
          greedyMersenneRemainder (1 / 2 : ℝ) (m + 1) =
            greedyMersenneRemainder (1 / 2 : ℝ) m := by
        rw [greedyMersenneRemainder_succ, if_neg hskip]
      have htail := mersenneTail_eq_weight_add m
      rw [Nat.succ_sub_one,
        halfGreedyMersenneShadow_sub_constant_eq_signedBalance,
        greedyMersenneSignedBalance_eq]
      rw [hremEq] at hdelta
      rw [abs_lt]
      unfold mersenneGap at hinterval ⊢
      constructor <;> linarith

/-- The Mersenne gap is already smaller than the depth-`2M` dyadic scale for
`M ≥ 3`. -/
theorem mersenneGap_lt_quarterPow
    {M : ℕ} (hM : 3 ≤ M) :
    mersenneGap M < ((1 : ℝ) / 4) ^ M := by
  have hgap := mersenneGap_sub_main_eq_remainder_sub_tail
    (n := M) (by omega)
  have hrem := mersenneWeightRemainder_le (n := M) (by omega)
  have htail := mersenneWeightRemainderTail_pos M
  have h8 : ((1 : ℝ) / 8) ^ M = ((1 : ℝ) / 2) ^ M * ((1 : ℝ) / 4) ^ M := by
    rw [← mul_pow]
    norm_num
  have hhalf : ((1 : ℝ) / 2) ^ M ≤ ((1 : ℝ) / 2) ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hM
  have hq : (0 : ℝ) < ((1 : ℝ) / 4) ^ M := by positivity
  have h8le : ((1 : ℝ) / 8) ^ M ≤ (1 / 8 : ℝ) * ((1 : ℝ) / 4) ^ M := by
    rw [h8]
    have hcube : ((1 : ℝ) / 2) ^ 3 = 1 / 8 := by norm_num
    nlinarith
  unfold mersenneGap at hgap ⊢
  linarith

/-- A last skip puts the shifted constant inside the depth-`2M` cylinder
immediately below `1 / 2`. -/
theorem lastHalfSkip_shifted_mem_dyadicCylinder
    {M : ℕ} (hM : 3 ≤ M) (hlast : IsLastHalfGreedySkip M) :
    (1 / 2 : ℝ) - ((1 : ℝ) / 4) ^ M <
        erdosBorweinMersenneConstant -
          finiteMersenneShift (halfSkippedPrefix M) ∧
      erdosBorweinMersenneConstant -
          finiteMersenneShift (halfSkippedPrefix M) < (1 / 2 : ℝ) := by
  have hinterval := lastHalfSkip_shift_fatalInterval hlast
  have hgap := mersenneGap_lt_quarterPow hM
  constructor <;> linarith

/-! ## Campbell parameter obstruction -/

/-- If `d` is the combined prime-progression modulus, `t` is the unavoidable
phase factor, and `P` is the prime cap forced by the fatal window, Campbell's
quarter-exponent applicability condition is impossible. -/
theorem campbellQuarterExponent_periodFreeze_noSync
    {d t P : ℕ}
    (hd : 2 ≤ d)
    (htd : t ≤ d)
    (hP : P ≤ 4 * t)
    (hAGP : d ^ 4 ≤ P) :
    False := by
  have hfour : d ^ 4 ≤ 4 * d :=
    hAGP.trans (hP.trans (Nat.mul_le_mul_left 4 htd))
  have hdpos : 0 < d := by omega
  have hcubic : d ^ 3 ≤ 4 := by
    apply Nat.le_of_mul_le_mul_right
    · simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hfour
    · exact hdpos
  have hlower : 2 ^ 3 ≤ d ^ 3 := Nat.pow_le_pow_left hd 3
  norm_num at hlower
  omega

/-- Substrate-native parameter map.  The hypotheses expose exactly where a
future analytic construction must improve: the phase-period factor `t`, the
fatal-window cap `P`, or the sublinear modulus exponent. -/
theorem campbellPhaseFreeze_parameters_impossible
    {M q0sq t d P : ℕ}
    (hq : 0 < q0sq)
    (htpos : 0 < t)
    (hd : 2 ≤ d)
    (ht : M ≤ t * q0sq)
    (htd : t ≤ d)
    (hwindow : P * q0sq ≤ 2 * M + 2)
    (hAGP : d ^ 4 ≤ P) :
    False := by
  have hP : P ≤ 4 * t := by
    have hMq : 2 * M + 2 ≤ 4 * t * q0sq := by
      have hone : 1 ≤ t * q0sq := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.ne_of_gt htpos) (Nat.ne_of_gt hq))
      have hdoubleM : 2 * M ≤ 2 * (t * q0sq) :=
        Nat.mul_le_mul_left 2 ht
      have htwo : 2 ≤ 2 * (t * q0sq) := Nat.mul_le_mul_left 2 hone
      calc
        2 * M + 2 ≤ 2 * (t * q0sq) + 2 * (t * q0sq) :=
          Nat.add_le_add hdoubleM htwo
        _ = 4 * t * q0sq := by ring
    have hscaled : P * q0sq ≤ (4 * t) * q0sq := by
      calc
        P * q0sq ≤ 2 * M + 2 := hwindow
        _ ≤ 4 * t * q0sq := hMq
    exact Nat.le_of_mul_le_mul_right hscaled hq
  exact campbellQuarterExponent_periodFreeze_noSync hd htd hP hAGP

/-- Exponent four is already skipped by the exact greedy recursion.  This
small evaluator fixes the positive-index convention used by the last-skip
endpoint below. -/
theorem four_mem_greedyMersenneSkippedSupport_half :
    4 ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num,
    succ_mem_greedyMersenneSkippedSupport_iff]
  norm_num [greedyMersenneRemainder_succ, mersenneWeight]

/-- A final skipped exponent exists exactly when the actual skipped support
is finite.  Nonemptiness is unconditional because exponent four is skipped. -/
theorem exists_isLastHalfGreedySkip_iff_skippedSupport_finite :
    (∃ M : ℕ, IsLastHalfGreedySkip M) ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Finite := by
  constructor
  · rintro ⟨M, hlast⟩
    rw [← coe_halfSkippedPrefix_eq_skippedSupport hlast]
    exact Set.toFinite _
  · intro hfinite
    classical
    let F : Finset ℕ := hfinite.toFinset
    have h4memF : 4 ∈ F := by
      simpa [F] using four_mem_greedyMersenneSkippedSupport_half
    have hFne : F.Nonempty := ⟨4, h4memF⟩
    let M : ℕ := F.max' hFne
    have hMmemF : M ∈ F := Finset.max'_mem F hFne
    have hMskip : M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) := by
      simpa [F] using hMmemF
    refine ⟨M, hMskip, fun m hMm hmSkip => ?_⟩
    have hmF : m ∈ F := by
      simpa [F] using hmSkip
    exact (not_lt_of_ge (Finset.le_max' F m hmF)) hMm

/-- The cut-locator's arbitrary-word fatal branch is now identified with the
canonical dynamical endpoint: it occurs exactly when the actual greedy orbit
has a final skipped exponent. -/
theorem existsFatalHalfGap_iff_exists_isLastHalfGreedySkip :
    ExistsFatalHalfGap ↔ ∃ M : ℕ, IsLastHalfGreedySkip M := by
  constructor
  · intro hgap
    have hnotmem : (1 / 2 : ℝ) ∉ mersenneAchievementSet :=
      existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet.mp hgap
    have hfinite :
        (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Finite := by
      by_contra hinfinite
      exact hnotmem
        (half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite.mpr
          hinfinite)
    exact exists_isLastHalfGreedySkip_iff_skippedSupport_finite.mpr hfinite
  · intro hlast
    have hfinite :
        (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Finite :=
      exists_isLastHalfGreedySkip_iff_skippedSupport_finite.mp hlast
    apply existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet.mpr
    intro hmem
    exact
      (half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite.mp
        hmem) hfinite

/-- The last-skip-guarded shifted-window interface.  Under a putative last
skip `M ≥ 3`, the complete finite shift is required to lie outside the
all-one depth-`2M` cylinder.  The equivalence theorem below shows that this
guarded formulation is an endpoint restatement, not an independent
arithmetic producer. -/
def GreedyShiftWindowZero : Prop :=
  ∀ M : ℕ, 3 ≤ M →
    IsLastHalfGreedySkip M →
    erdosBorweinMersenneConstant - finiteMersenneShift (halfSkippedPrefix M) ≤
      (1 / 2 : ℝ) - ((1 : ℝ) / 4) ^ M

/-- The shifted-zero producer rules out a final skipped exponent. -/
theorem not_isLastHalfGreedySkip_of_shiftWindowZero
    (hzero : GreedyShiftWindowZero) {M : ℕ} (hM : 3 ≤ M) :
    ¬ IsLastHalfGreedySkip M := by
  intro hlast
  have hcylinder := lastHalfSkip_shifted_mem_dyadicCylinder hM hlast
  have houtside := hzero M hM hlast
  linarith

/-- The shifted-zero producer forces infinitely many actual skips. -/
theorem greedyMersenneSkippedSupport_infinite_of_shiftWindowZero
    (hzero : GreedyShiftWindowZero) :
    (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite := by
  intro hfinite
  classical
  let F : Finset ℕ := hfinite.toFinset
  have h4memF : 4 ∈ F := by
    simpa [F] using four_mem_greedyMersenneSkippedSupport_half
  have hFne : F.Nonempty := by
    exact ⟨4, h4memF⟩
  let M : ℕ := F.max' hFne
  have hMmemF : M ∈ F := Finset.max'_mem F hFne
  have hMskip : M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) := by
    simpa [F] using hMmemF
  have hfourLe : 4 ≤ M := by
    apply Finset.le_max' F 4
    exact h4memF
  have hlast : IsLastHalfGreedySkip M := by
    refine ⟨hMskip, fun m hMm hmSkip => ?_⟩
    have hmF : m ∈ F := by
      simpa [F] using hmSkip
    have hmle : m ≤ M := Finset.le_max' F m hmF
    omega
  exact not_isLastHalfGreedySkip_of_shiftWindowZero hzero (by omega) hlast

/-- Infinitely many skipped exponents make the last-skip hypothesis in the
shifted-window producer impossible.  This closes the converse logical
direction without adding any analytic input: the genuine arithmetic content
of `GreedyShiftWindowZero` is exactly the exclusion of a final skip. -/
theorem shiftWindowZero_of_greedyMersenneSkippedSupport_infinite
    (hinfinite :
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite) :
    GreedyShiftWindowZero := by
  intro M _hM hlast
  have hfinite :
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Finite := by
    rw [← coe_halfSkippedPrefix_eq_skippedSupport hlast]
    exact Set.toFinite _
  exact (hinfinite hfinite).elim

/-- Exact endpoint classification of the Campbell-shift interface.  It is
equivalent to infinitude of the actual greedy skipped support, rather than a
strictly weaker producer waiting for a separate composition theorem. -/
theorem shiftWindowZero_iff_greedyMersenneSkippedSupport_infinite :
    GreedyShiftWindowZero ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite := by
  constructor
  · exact greedyMersenneSkippedSupport_infinite_of_shiftWindowZero
  · exact shiftWindowZero_of_greedyMersenneSkippedSupport_infinite

/-- Composition with the checked greedy endpoint yields exact half
membership once the shifted-zero producer is supplied. -/
theorem half_mem_mersenneAchievementSet_of_shiftWindowZero
    (hzero : GreedyShiftWindowZero) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite.mpr
    (greedyMersenneSkippedSupport_infinite_of_shiftWindowZero hzero)

/-- The shifted-window formulation is exactly equivalent to the concrete
half-achievement endpoint. -/
theorem shiftWindowZero_iff_half_mem_mersenneAchievementSet :
    GreedyShiftWindowZero ↔ (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  rw [half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite]
  exact shiftWindowZero_iff_greedyMersenneSkippedSupport_infinite

end Erdos249257
