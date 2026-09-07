import Erdos257PeriodNoncollapse.BooleanMobiusCarry

/-!
# Erdős #257: the achievement set is a non-escaping set

The Mersenne achievement set `𝒜` is already known here to be compact,
perfect, nowhere dense, and of Lebesgue measure exactly `1`.  This module
identifies it *dynamically*.

Scale the greedy residual by `2 ^ N`:

`scaledGreedyRemainder x N = 2 ^ N * greedyMersenneRemainder x N`.

The greedy recursion becomes an explicit non-autonomous **nearly doubling
map** (`scaledGreedyRemainder_succ`)

`y_{N+1} = if c_{N+1} ≤ 2 y_N then 2 y_N - c_{N+1} else 2 y_N`,
`c_n = 2^n / (2^n - 1) ↓ 1`,

and then

* `mersenneAchievementSet_eq_scaledGreedyTrap` :
  `𝒜 = {x ≥ 0 | ∀ N, y_N < 2}` — membership is exactly permanent trapping
  below the *universal* barrier `2`;
* `scaledGreedyRemainder_tendsto_atTop_of_not_mem` : non-membership is not
  merely unbounded behaviour, it is forced **exponential escape**;
* `mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded` : one
  bounded cofinal subsequence already certifies membership.

So a compact, perfect, nowhere dense set of Lebesgue measure one is exactly
the filled non-escaping set of an explicit asymptotically dyadic dynamical
system.  The `1/21` bounded-return criterion already in the corpus is the
`x = 1/21` instance (`one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded`).

Erdős #257 remains open; membership of `1/2` and `1/21` remains undecided.
-/

namespace Erdos257PeriodNoncollapse

open Filter Topology

/-- The greedy residual rescaled to the current dyadic scale. -/
noncomputable def scaledGreedyRemainder (x : ℝ) (N : ℕ) : ℝ :=
  (2 : ℝ) ^ N * greedyMersenneRemainder x N

/-- The rescaled Mersenne weight, i.e. the subtraction constant of the
rescaled dynamics.  It decreases strictly to `1`. -/
noncomputable def mersenneScale (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * mersenneWeight n

theorem mersenneScale_eq (n : ℕ) (hn : 0 < n) :
    mersenneScale n = (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 1) := by
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ n := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
  unfold mersenneScale mersenneWeight
  field_simp

theorem one_lt_mersenneScale {n : ℕ} (hn : 0 < n) : 1 < mersenneScale n := by
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ n := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
  rw [mersenneScale_eq n hn]
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- **The rescaled greedy recursion is an explicit nearly doubling map.** -/
theorem scaledGreedyRemainder_succ (x : ℝ) (N : ℕ) :
    scaledGreedyRemainder x (N + 1) =
      if mersenneScale (N + 1) ≤ 2 * scaledGreedyRemainder x N then
        2 * scaledGreedyRemainder x N - mersenneScale (N + 1)
      else
        2 * scaledGreedyRemainder x N := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hcond :
      mersenneScale (N + 1) ≤ 2 * scaledGreedyRemainder x N ↔
        mersenneWeight (N + 1) ≤ greedyMersenneRemainder x N := by
    unfold mersenneScale scaledGreedyRemainder
    rw [pow_succ]
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  by_cases hle : mersenneWeight (N + 1) ≤ greedyMersenneRemainder x N
  · rw [if_pos (hcond.2 hle)]
    show (2 : ℝ) ^ (N + 1) * greedyMersenneRemainder x (N + 1) = _
    rw [greedyMersenneRemainder, if_pos hle]
    unfold mersenneScale scaledGreedyRemainder
    rw [pow_succ]
    ring
  · rw [if_neg fun hbad => hle (hcond.1 hbad)]
    show (2 : ℝ) ^ (N + 1) * greedyMersenneRemainder x (N + 1) = _
    rw [greedyMersenneRemainder, if_neg hle]
    unfold scaledGreedyRemainder
    rw [pow_succ]
    ring

/-! ## The exact lower separatrix -/

/-- Rank `N + 1` is skipped exactly when the scaled residual crosses below
the moving lower separatrix `mersenneScale (N + 1) / 2`. -/
@[simp] theorem succ_mem_greedyMersenneSkippedSupport_iff_scaled_lowerBranch
    (x : ℝ) (N : ℕ) :
    N + 1 ∈ greedyMersenneSkippedSupport x ↔
      2 * scaledGreedyRemainder x N < mersenneScale (N + 1) := by
  rw [succ_mem_greedyMersenneSkippedSupport_iff]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hcond :
      mersenneScale (N + 1) ≤ 2 * scaledGreedyRemainder x N ↔
        mersenneWeight (N + 1) ≤ greedyMersenneRemainder x N := by
    unfold mersenneScale scaledGreedyRemainder
    rw [pow_succ]
    constructor <;> intro h <;> nlinarith
  simpa only [not_le] using (not_congr hcond).symm

/-- The scaled greedy orbit enters its exact lower branch beyond every
cutoff.  This is the moving-barrier form of a cofinal supply of skips. -/
def ScaledGreedyLowerBranchCofinally (x : ℝ) : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    2 * scaledGreedyRemainder x N < mersenneScale (N + 1)

/-- Infinitely many omitted exponents are exactly cofinal crossings of the
scaled lower separatrix. -/
theorem greedySkippedSupport_infinite_iff_scaledLowerBranchCofinally
    (x : ℝ) :
    (greedyMersenneSkippedSupport x).Infinite ↔
      ScaledGreedyLowerBranchCofinally x := by
  rw [greedyMersenneSkippedSupport_infinite_iff_cofinal_skips]
  constructor
  · intro hcofinal K
    obtain ⟨N, hKN, hskip⟩ := hcofinal K
    refine ⟨N, hKN, ?_⟩
    exact
      (succ_mem_greedyMersenneSkippedSupport_iff_scaled_lowerBranch x N).1
        ((succ_mem_greedyMersenneSkippedSupport_iff x N).2 hskip)
  · intro hlower K
    obtain ⟨N, hKN, hlowerN⟩ := hlower K
    refine ⟨N, hKN, ?_⟩
    exact
      (succ_mem_greedyMersenneSkippedSupport_iff x N).1
        ((succ_mem_greedyMersenneSkippedSupport_iff_scaled_lowerBranch x N).2
          hlowerN)

/-- **Rational lower-separatrix criterion.**  A nonnegative rational target
belongs to the Mersenne achievement set exactly when its scaled greedy orbit
crosses the moving lower barrier beyond every cutoff. -/
theorem rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (q : ℝ) := by
  calc
    (q : ℝ) ∈ mersenneAchievementSet ↔
        (greedyMersenneSkippedSupport (q : ℝ)).Infinite :=
      rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite q hq
    _ ↔ ScaledGreedyLowerBranchCofinally (q : ℝ) :=
      greedySkippedSupport_infinite_iff_scaledLowerBranchCofinally (q : ℝ)

/-- The universal barrier: the rescaled complete Mersenne tail never reaches
`2`, at any scale. -/
theorem two_pow_mul_mersenneTail_lt_two (n : ℕ) :
    (2 : ℝ) ^ n * mersenneTail n < 2 := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have htail := mersenneTail_lt_two_mul_weight n
  have hmul := mul_lt_mul_of_pos_left htail hpow
  refine hmul.trans_le ?_
  have hden : (0 : ℝ) < (2 : ℝ) ^ n * 2 - 1 := by nlinarith
  have hweight : mersenneWeight (n + 1) = 1 / ((2 : ℝ) ^ n * 2 - 1) := by
    unfold mersenneWeight
    rw [pow_succ]
  rw [hweight]
  rw [show (2 : ℝ) ^ n * (2 * (1 / ((2 : ℝ) ^ n * 2 - 1)))
      = ((2 : ℝ) ^ n * 2) / ((2 : ℝ) ^ n * 2 - 1) by field_simp]
  rw [div_le_iff₀ hden]
  nlinarith

/-- One bounded cofinal subsequence of the rescaled residual. -/
def ScaledGreedyRemainderCofinallyBounded (x : ℝ) : Prop :=
  ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ scaledGreedyRemainder x N ≤ B

/-- Outside the achievement set, the rescaled residual escapes to infinity
**exponentially**: the excess over the complete tail is conserved exactly and
gets doubled at every scale. -/
theorem scaledGreedyRemainder_tendsto_atTop_of_not_mem {x : ℝ} (hx : 0 ≤ x)
    (hnot : x ∉ mersenneAchievementSet) :
    Tendsto (fun N : ℕ => scaledGreedyRemainder x N) atTop atTop := by
  have hnotSurvive : ¬ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
    intro hsurvive
    exact hnot ((mem_mersenneAchievementSet_iff_greedy_survival x).2 ⟨hx, hsurvive⟩)
  push_neg at hnotSurvive
  obtain ⟨n, hn⟩ := hnotSurvive
  have hfatal : GreedyMersenneFatalAt x n := hn
  set δ : ℝ := greedyMersenneRemainder x n - mersenneTail n with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδle : ∀ N : ℕ, n ≤ N → δ ≤ greedyMersenneRemainder x N := by
    intro N hN
    have heq := greedyMersenneRemainder_sub_tail_eq_of_fatalAt_add hfatal (N - n)
    rw [show n + (N - n) = N by omega] at heq
    have htail := mersenneTail_nonneg N
    rw [hδ]
    linarith
  have hpow : Tendsto (fun N : ℕ => (2 : ℝ) ^ N) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  apply Filter.tendsto_atTop_atTop.2
  intro B
  obtain ⟨K₀, hK₀⟩ := (Filter.tendsto_atTop_atTop.1 hpow) (B / δ + 1)
  refine ⟨max n K₀, fun N hN => ?_⟩
  have hnN : n ≤ N := le_trans (le_max_left n K₀) hN
  have hK₀N : K₀ ≤ N := le_trans (le_max_right n K₀) hN
  have hpowN : B / δ < (2 : ℝ) ^ N := by
    have := hK₀ N hK₀N
    linarith
  have hstrict : B < (2 : ℝ) ^ N * δ := (div_lt_iff₀ hδ0).1 hpowN
  have hscaled : (2 : ℝ) ^ N * δ ≤ (2 : ℝ) ^ N * greedyMersenneRemainder x N :=
    mul_le_mul_of_nonneg_left (hδle N hnN) (by positivity)
  unfold scaledGreedyRemainder
  linarith

/-- **Membership is exactly one bounded cofinal return.** -/
theorem mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded {x : ℝ}
    (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔ ScaledGreedyRemainderCofinallyBounded x := by
  constructor
  · intro hmem
    obtain ⟨_, hsurvive⟩ := (mem_mersenneAchievementSet_iff_greedy_survival x).1 hmem
    refine ⟨2, fun K => ⟨K, le_rfl, ?_⟩⟩
    have hscaled :=
      mul_le_mul_of_nonneg_left (hsurvive K) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ K)
    exact le_of_lt (lt_of_le_of_lt hscaled (two_pow_mul_mersenneTail_lt_two K))
  · rintro ⟨B, hbounded⟩
    by_contra hnot
    have hesc := scaledGreedyRemainder_tendsto_atTop_of_not_mem hx hnot
    obtain ⟨K, hK⟩ := (Filter.tendsto_atTop_atTop.1 hesc) (B + 1)
    obtain ⟨N, hcut, hupper⟩ := hbounded K
    have := hK N hcut
    linarith

/-- **The achievement set is the trapping set below the universal barrier
`2`.** -/
theorem mem_mersenneAchievementSet_iff_forall_scaledRemainder_lt_two {x : ℝ}
    (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔ ∀ N : ℕ, scaledGreedyRemainder x N < 2 := by
  constructor
  · intro hmem N
    have hsurvive := ((mem_mersenneAchievementSet_iff_greedy_survival x).1 hmem).2 N
    have hscaled :=
      mul_le_mul_of_nonneg_left hsurvive (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ N)
    exact lt_of_le_of_lt hscaled (two_pow_mul_mersenneTail_lt_two N)
  · intro htrap
    exact (mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded hx).2
      ⟨2, fun K => ⟨K, le_rfl, (htrap K).le⟩⟩

/-- **A fat Cantor set is exactly a non-escaping set.**  The compact,
perfect, nowhere dense, Lebesgue-measure-one Mersenne achievement set is the
filled non-escaping set of the explicit nearly doubling dynamics of
`scaledGreedyRemainder_succ`. -/
theorem mersenneAchievementSet_eq_scaledGreedyTrap :
    mersenneAchievementSet =
      {x : ℝ | 0 ≤ x ∧ ∀ N : ℕ, scaledGreedyRemainder x N < 2} := by
  ext x
  constructor
  · intro hmem
    have hx : 0 ≤ x := ((mem_mersenneAchievementSet_iff_greedy_survival x).1 hmem).1
    exact ⟨hx, (mem_mersenneAchievementSet_iff_forall_scaledRemainder_lt_two hx).1 hmem⟩
  · rintro ⟨hx, htrap⟩
    exact (mem_mersenneAchievementSet_iff_forall_scaledRemainder_lt_two hx).2 htrap

/-- The `1/21` endpoint of the corpus is the `x = 1/21` instance of the
general criterion. -/
theorem one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyRemainderCofinallyBounded (1 / 21 : ℝ) :=
  mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded (by norm_num)

/-- The exact remaining `1/21` producer is cofinal crossing of the scaled
lower separatrix.  This theorem packages the endpoint but does not prove its
open positive side. -/
theorem one_div_twentyOne_mem_iff_scaledLowerBranchCofinally :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (1 / 21 : ℝ) := by
  simpa using
    rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
      ((1 : ℚ) / 21) (by norm_num)

end Erdos257PeriodNoncollapse
