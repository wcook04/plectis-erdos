import Erdos249257.DyadicPrefixCompression
import Erdos249257.HalfGreedyFatalGap
import Erdos249257.GreedyHoleNormalForm

/-!
# Dyadic safety of half-greedy skips

Checked reductions for the `1/2` frontier in Erdős Problem #257.  The module
separates the finite unit-residual segment and conditional skip-safety
criteria from their still-open global hypotheses.

The weaker criterion uses the full remaining Mersenne tail.  At a skipped
rank, write the residual as `p/q` and put `X = 2^(n+1)`.  The inequality
`3*p*X <= 3*q+p` implies that the residual is below the remaining tail.  This
criterion admits states excluded by the dyadic bound; it is not proved here
for every state of the actual orbit.

Analytical claim:
  rem(n) < w_(n+1)  →  rem(n) ≤ 2^(-(n+1))
i.e. every skip is dyadically safe, so E_n ≤ 0.

Unit-numerator kill (CLOSED): when p = 1, rem = 1/(2D) so 1/rem ∈ ℤ,
and (2^k - 1, 2^k) contains no integers — every unit skip is safe.

Global producer (OPEN): ⌊1/rem + 1⌋ is never a power of two on the
half-greedy orbit. Empirically true through depth ≥200; equivalent to
excluding the unsafe sliver at every rank. Take-step: R' = R·q/(q-R)
with q = 2^b-1, and the unreduced U,V for R'+1 are both odd.
-/

namespace Erdos249257

/-! ## Consumer: dyadic-safe skips close #257 half -/

/-- Every skipped half-greedy rank is dyadically safe (real coordinates). -/
def HalfGreedySkipDyadicSafe : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      halfGreedyNextDyadicExcessNumerator n ≤ 0

/-- On a dyadically safe skip, the two-channel excess bound is free. -/
theorem halfGreedySkippedExcessBound_of_skipDyadicSafe
    (hsafe : HalfGreedySkipDyadicSafe) :
    HalfGreedySkippedExcessBound := by
  intro n hskip
  have hE : halfGreedyNextDyadicExcessNumerator n ≤ 0 := hsafe n hskip
  have hD : 0 < (halfGreedyPrefixDenominator n : ℤ) := by
    exact_mod_cast Rat.den_pos (halfGreedyPrefixRat n)
  have hpow : 0 ≤ (((2 ^ (n + 1) : ℕ) : ℤ)) := by positivity
  nlinarith

/-- Dyadic safety of actual skips proves half membership. -/
theorem half_mem_mersenneAchievementSet_of_skipDyadicSafe
    (hsafe : HalfGreedySkipDyadicSafe) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_skipped_excessBound
    (halfGreedySkippedExcessBound_of_skipDyadicSafe hsafe)

/-! ## The two-thirds skipped-margin criterion -/

/-- At every skipped rank, the displayed residual `p/q` has the margin
`3*p*2^(n+1) <= 3*q+p`.  This is equivalent to the two-thirds clearance used
by `HalfGreedyFatalGap.skipSafe_actualTail_of_two_mul_le_three_mul`.

This hypothesis remains open for the actual half-greedy orbit. -/
def HalfGreedySkippedTwoThirdsMargin : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      let p := (halfGreedyResidualDisplayedNumerator n).natAbs
      let q := 2 * halfGreedyPrefixDenominator n
      3 * p * 2 ^ (n + 1) ≤ 3 * q + p

/-- The dyadic block inequality implies the two-thirds margin. -/
theorem twoThirdsMargin_of_blockDyadicSafe
    {p D k : ℕ} (hsafe : BlockDyadicSafeAt p D k) :
    3 * p * 2 ^ k ≤ 3 * (2 * D) + p := by
  unfold BlockDyadicSafeAt at hsafe
  simp only [Nat.mul_assoc]
  omega

/-- A nonpositive actual excess numerator is the corresponding natural
block-safe inequality. -/
theorem blockDyadicSafeAt_of_halfGreedyNextDyadicExcess_nonpos
    (n : ℕ) (hsafe : halfGreedyNextDyadicExcessNumerator n ≤ 0) :
    BlockDyadicSafeAt
      (halfGreedyResidualDisplayedNumerator n).natAbs
      (halfGreedyPrefixDenominator n) (n + 1) := by
  have hp0 := halfGreedyResidualDisplayedNumerator_nonneg n
  have hpcast :
      (((halfGreedyResidualDisplayedNumerator n).natAbs : ℕ) : ℤ) =
        halfGreedyResidualDisplayedNumerator n := by
    simp [Int.natAbs_of_nonneg hp0]
  have hsafeZ :
      halfGreedyResidualDisplayedNumerator n *
          (((2 ^ (n + 1) : ℕ) : ℤ)) ≤
        2 * (halfGreedyPrefixDenominator n : ℤ) := by
    unfold halfGreedyNextDyadicExcessNumerator at hsafe
    unfold nextDyadicExcessIntNumerator at hsafe
    have hbase :
        halfGreedyResidualDisplayedNumerator n *
            (((2 ^ n : ℕ) : ℤ)) ≤
          (halfGreedyPrefixDenominator n : ℤ) := by
      simpa [mul_comm] using (sub_nonpos.mp hsafe)
    have htwice := mul_le_mul_of_nonneg_right hbase (by norm_num : (0 : ℤ) ≤ 2)
    rw [pow_succ]
    push_cast
    simpa [mul_assoc, mul_comm, mul_left_comm] using htwice
  rw [← hpcast] at hsafeZ
  unfold BlockDyadicSafeAt
  exact_mod_cast hsafeZ

/-- Orbit-wide dyadic safety is a stronger sufficient condition than the
two-thirds skipped margin. -/
theorem halfGreedySkippedTwoThirdsMargin_of_skipDyadicSafe
    (hsafe : HalfGreedySkipDyadicSafe) :
    HalfGreedySkippedTwoThirdsMargin := by
  intro n hskip
  exact twoThirdsMargin_of_blockDyadicSafe
    (blockDyadicSafeAt_of_halfGreedyNextDyadicExcess_nonpos n
      (hsafe n hskip))

/-- The two-thirds margin is genuinely weaker than dyadic block safety.
The state `(p,D,k)=(7,13,2)` is skipped and satisfies the former, while
`7/26 > 1/4` makes the latter fail. -/
theorem exists_twoThirdsMargin_not_blockDyadicSafe :
    ∃ p D k : ℕ,
      0 < p ∧ ¬ BlockTakeAt p D k ∧
        3 * p * 2 ^ k ≤ 3 * (2 * D) + p ∧
          ¬ BlockDyadicSafeAt p D k := by
  refine ⟨7, 13, 2, by norm_num, ?_, by norm_num, ?_⟩
  · norm_num [BlockTakeAt]
  · norm_num [BlockDyadicSafeAt]

/-- At an actual skipped rank, the two-thirds margin places the residual
strictly below the full remaining Mersenne tail. -/
theorem halfGreedyRemainder_lt_tail_of_skippedTwoThirdsMargin
    (n : ℕ)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n)
    (hmargin :
      let p := (halfGreedyResidualDisplayedNumerator n).natAbs
      let q := 2 * halfGreedyPrefixDenominator n
      3 * p * 2 ^ (n + 1) ≤ 3 * q + p) :
    greedyMersenneRemainder (1 / 2 : ℝ) n < mersenneTail (n + 1) := by
  let p := (halfGreedyResidualDisplayedNumerator n).natAbs
  let D := halfGreedyPrefixDenominator n
  let X := 2 ^ (n + 1)
  let a := 2 * D + p - X * p
  have hp0 := halfGreedyResidualDisplayedNumerator_nonneg n
  have hpne : halfGreedyResidualDisplayedNumerator n ≠ 0 := by
    intro hpzero
    rcases halfGreedyResidualDisplayedNumerator_odd n with ⟨j, hj⟩
    rw [hpzero] at hj
    omega
  have hp : 0 < p := by
    exact Int.natAbs_pos.mpr hpne
  have hD : 0 < D := by
    exact Rat.den_pos (halfGreedyPrefixRat n)
  have hskipBlock : ¬ BlockTakeAt p D (n + 1) := by
    simpa only [p, D, greedyHalf_take_iff_BlockTakeAt n] using hskip
  have hskipNat : p * (X - 1) < 2 * D := by
    simpa only [BlockTakeAt, not_le, X] using hskipBlock
  have hmul : p * (X - 1) = X * p - p := by
    rw [Nat.mul_sub_left_distrib]
    simp [Nat.mul_comm]
  have hXp : X * p < 2 * D + p := by
    omega
  have ha : 0 < a := by
    exact Nat.sub_pos_iff_lt.mpr hXp
  have hdecomp : X * p + a = 2 * D + p := by
    dsimp [a]
    omega
  have hmargin' : 3 * p * X ≤ 3 * (2 * D) + p := by
    simpa only [p, D, X] using hmargin
  have hmargin'' : 3 * (X * p) ≤ 3 * (2 * D) + p := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmargin'
  have hdecomp3 :
      3 * (X * p) + 3 * a = 3 * (2 * D) + 3 * p := by
    calc
      3 * (X * p) + 3 * a = 3 * (X * p + a) := by omega
      _ = 3 * (2 * D + p) := by rw [hdecomp]
      _ = 3 * (2 * D) + 3 * p := by omega
  have hsharp : 2 * p ≤ 3 * a := by
    omega
  have htail :=
    HalfGreedyFatalGap.skipSafe_actualTail_of_two_mul_le_three_mul
      (k := n + 1) (u := p) (L := D) (a := a)
      (by omega) hp ha (by simpa only [X] using hdecomp) hsharp
  have hpcast : (p : ℤ) = halfGreedyResidualDisplayedNumerator n := by
    simp [p, Int.natAbs_of_nonneg hp0]
  have hrem :
      greedyMersenneRemainder (1 / 2 : ℝ) n =
        (p : ℝ) / (2 * D) := by
    have hremRat := greedyHalfRemainderRat_eq_displayed_divInt n
    rw [Rat.divInt_eq_div, ← hpcast] at hremRat
    calc
      greedyMersenneRemainder (1 / 2 : ℝ) n =
          ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ) := by
        rw [cast_greedyMersenneRemainderRat]
        norm_num
      _ = (p : ℝ) / (2 * D) := by
        rw [hremRat]
        norm_num [D]
  rw [hrem]
  exact htail

/-- The skipped two-thirds margin at every rank implies half-membership.
Selected ranks transport the full-tail bound exactly; the preceding theorem
supplies the skipped ranks. -/
theorem half_mem_mersenneAchievementSet_of_skippedTwoThirdsMargin
    (hmargin : HalfGreedySkippedTwoThirdsMargin) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  have h0 : (1 / 2 : ℝ) ≤ mersenneTail 0 := by
    have hcap :
        greedyMersenneRemainder (1 / 2 : ℝ) 0 ≤
          halfTwoChannelCap 0 := by
      norm_num [halfTwoChannelCap]
    exact hcap.trans (halfTwoChannelCap_le_mersenneTail 0)
  apply (mem_mersenneAchievementSet_iff_holeFree (by norm_num) h0).2
  intro n hhole
  have hskip :
      ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n :=
    not_le.mpr hhole.2
  have hbelow :=
    halfGreedyRemainder_lt_tail_of_skippedTwoThirdsMargin
      n hskip (hmargin n hskip)
  exact (not_lt_of_ge hbelow.le) hhole.1

/-! ## Unit residual: skip ⇒ dyadic safe (no integer in `(2^k-1, 2^k)`) -/

/-- Abstract unit-numerator skip forces the dyadic margin. -/
theorem blockDyadicSafeAt_of_unit_skip
    {D k : ℕ} (hskip : ¬ BlockTakeAt 1 D k) :
    BlockDyadicSafeAt 1 D k := by
  unfold BlockTakeAt BlockDyadicSafeAt at *
  have hlt : 2 ^ k - 1 < 2 * D := by
    simpa [not_le] using hskip
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
  have : 2 ^ k ≤ 2 * D := by
    have := Nat.add_one_le_of_lt hlt
    rwa [Nat.sub_add_cancel hpow] at this
  simpa using this

/-- Displayed unit numerator converts a real skip into `BlockTakeAt 1`. -/
theorem greedyHalf_unit_skip_blockTake
    (n : ℕ)
    (hp : halfGreedyResidualDisplayedNumerator n = 1)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    ¬ BlockTakeAt 1 (halfGreedyPrefixDenominator n) (n + 1) := by
  have habs :
      (halfGreedyResidualDisplayedNumerator n).natAbs = 1 := by
    simp [hp]
  have hiff := greedyHalf_take_iff_BlockTakeAt n
  rw [hiff, habs] at hskip
  exact hskip

/-- Unit displayed residual: every skip is block-dyadically safe. -/
theorem greedyHalf_unit_skip_blockDyadicSafe
    (n : ℕ)
    (hp : halfGreedyResidualDisplayedNumerator n = 1)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    BlockDyadicSafeAt 1 (halfGreedyPrefixDenominator n) (n + 1) :=
  blockDyadicSafeAt_of_unit_skip
    (greedyHalf_unit_skip_blockTake n hp hskip)

/-- Unit displayed residual: skip ⇒ excess nonpositive. -/
theorem halfGreedy_skip_dyadic_safe_of_unit_numerator
    (n : ℕ)
    (hp : halfGreedyResidualDisplayedNumerator n = 1)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    halfGreedyNextDyadicExcessNumerator n ≤ 0 := by
  have hsafe := greedyHalf_unit_skip_blockDyadicSafe n hp hskip
  have hpabs :
      (halfGreedyResidualDisplayedNumerator n).natAbs = 1 := by
    simp [hp]
  have hsafe' :
      BlockDyadicSafeAt
        (halfGreedyResidualDisplayedNumerator n).natAbs
        (halfGreedyPrefixDenominator n) (n + 1) := by
    simpa [hpabs] using hsafe
  exact (greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos n).1
    (greedyHalfRemainder_le_nextDyadic_of_BlockSafe n hsafe')

/-! ## Finite `p = 1` segment (through `n ≤ 19`) -/

theorem halfGreedyPrefixRat_eq_half_sub_remainder (n : ℕ) :
    halfGreedyPrefixRat n =
      (1 / 2 : ℚ) - greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
  unfold halfGreedyPrefixRat
  linarith [greedyMersenneRemainderRat_eq_sub_finiteErdosSum
    (1 / 2 : ℚ) n]

/-- Ranks `0..19` stay on the unit residual (first `p > 1` after take 20). -/
theorem halfGreedyResidualDisplayedNumerator_eq_one_of_le_19
    (n : ℕ) (hn : n ≤ 19) :
    halfGreedyResidualDisplayedNumerator n = 1 := by
  rw [halfGreedyResidualDisplayedNumerator,
    halfGreedyPrefixDenominator,
    halfGreedyPrefixRat_eq_half_sub_remainder]
  interval_cases n <;>
    norm_num [greedyMersenneRemainderRat, mersenneWeightRat]

/-- Every skip through rank decision `n ≤ 19` is dyadically safe. -/
theorem halfGreedy_skip_dyadic_safe_of_le_19
    (n : ℕ) (hn : n ≤ 19)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    halfGreedyNextDyadicExcessNumerator n ≤ 0 :=
  halfGreedy_skip_dyadic_safe_of_unit_numerator n
    (halfGreedyResidualDisplayedNumerator_eq_one_of_le_19 n hn) hskip

/-- Unit-segment form of the landed actual-block-safe consumer hypothesis. -/
theorem halfGreedy_actualBlockSafe_of_le_19
    (n : ℕ) (hn : n ≤ 19)
    (hskip : ¬ mersenneWeight (n + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) n) :
    BlockDyadicSafeAt
      (halfGreedyResidualDisplayedNumerator n).natAbs
      (halfGreedyPrefixDenominator n) (n + 1) := by
  have hp := halfGreedyResidualDisplayedNumerator_eq_one_of_le_19 n hn
  have hsafe := greedyHalf_unit_skip_blockDyadicSafe n hp hskip
  have habs :
      (halfGreedyResidualDisplayedNumerator n).natAbs = 1 := by
    simp [hp]
  simpa [habs] using hsafe

/-! ## Algebraic post-take contraction -/

/-- If the pre-take residual is already `≤ 2^-(d-1)` and the rank-`d` weight
is selected, the post-take residual is `≤ 2^-d`.

Algebra: `2^-(d-1) - 2^-d = 2^-d ≤ 1/(2^d - 1) = w_d`. -/
theorem rem_sub_mersenneWeight_le_dyadic_of_pred_dyadic
    {r : ℚ} {d : ℕ} (hd : 1 ≤ d)
    (hrem : r ≤ (1 / (2 : ℚ) ^ (d - 1)))
    (_htake : mersenneWeightRat d ≤ r) :
    r - mersenneWeightRat d ≤ (1 / (2 : ℚ) ^ d) := by
  have hpow : (2 : ℚ) ^ d = (2 : ℚ) ^ (d - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  have hdiff :
      (1 / (2 : ℚ) ^ (d - 1)) - (1 / (2 : ℚ) ^ d) =
        (1 / (2 : ℚ) ^ d) := by
    rw [hpow]
    field_simp
    ring
  have hden : (0 : ℚ) < (2 : ℚ) ^ d - 1 := by
    have : (1 : ℚ) < 2 ^ d :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hw :
      (1 / (2 : ℚ) ^ d) ≤ mersenneWeightRat d := by
    unfold mersenneWeightRat
    exact one_div_le_one_div_of_le hden (by linarith)
  have hbound :
      (1 / (2 : ℚ) ^ (d - 1)) - mersenneWeightRat d ≤
        (1 / (2 : ℚ) ^ d) := by
    linarith [hdiff, hw]
  linarith [hrem, hbound]

/-! ## Global reciprocal invariant (unit case closed) -/

/-- `R = 1/rem = 2D/p`. Unsafe skip at `k` iff `R ∈ (2^k-1, 2^k)`
iff `Int.floor (R + 1) = 2^k`. So excluding powers of two among
`Int.floor (R + 1)` kills every unsafe skip. -/
def HalfGreedyReciprocalFloorSuccNotPow2 : Prop :=
  ∀ n : ℕ,
    ¬ ∃ e : ℕ,
      Int.floor
          ((2 * (halfGreedyPrefixDenominator n : ℚ)) /
            (halfGreedyResidualDisplayedNumerator n : ℚ) + 1) =
        ((2 : ℤ) ^ e)

/-- The reciprocal-floor obstruction restricted to the ranks at which the
half-greedy orbit actually skips. -/
def HalfGreedySkippedReciprocalFloorSuccNotPow2 : Prop :=
  ∀ n : ℕ,
    ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) n →
      ¬ ∃ e : ℕ,
        Int.floor
            ((2 * (halfGreedyPrefixDenominator n : ℚ)) /
              (halfGreedyResidualDisplayedNumerator n : ℚ) + 1) =
          ((2 : ℤ) ^ e)

/-- The orbit-wide obstruction implies its weaker skipped-rank form. -/
theorem halfGreedySkippedReciprocalFloorSuccNotPow2_of_all
    (hfloor : HalfGreedyReciprocalFloorSuccNotPow2) :
    HalfGreedySkippedReciprocalFloorSuccNotPow2 := by
  intro n _hskip
  exact hfloor n

/-- An unsafe skipped block places the reciprocal successor in the unique
unit interval whose floor is the corresponding power of two. -/
theorem floor_two_mul_div_add_one_eq_pow_of_unsafe_skip
    {p D k : ℕ} (hp : 0 < p)
    (hskip : ¬ BlockTakeAt p D k)
    (hunsafe : ¬ BlockDyadicSafeAt p D k) :
    Int.floor (((2 * D : ℕ) : ℚ) / p + 1) = ((2 : ℤ) ^ k) := by
  have hskipNat : p * (2 ^ k - 1) < 2 * D := by
    simpa only [BlockTakeAt, not_le] using hskip
  have hunsafeNat : 2 * D < p * 2 ^ k := by
    simpa only [BlockDyadicSafeAt, not_le] using hunsafe
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hlo : ((2 : ℚ) ^ k) ≤ (((2 * D : ℕ) : ℚ) / p + 1) := by
    rw [← sub_le_iff_le_add, le_div_iff₀ hpQ]
    push_cast
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast (by simpa [Nat.mul_comm] using Nat.le_of_lt hskipNat)
  have hhi : (((2 * D : ℕ) : ℚ) / p + 1) < (2 : ℚ) ^ k + 1 := by
    rw [add_lt_add_iff_right, div_lt_iff₀ hpQ]
    push_cast
    exact_mod_cast (by simpa [Nat.mul_comm] using hunsafeNat)
  apply le_antisymm
  · have hfloor_lt :
        Int.floor (((2 * D : ℕ) : ℚ) / p + 1) < ((2 : ℤ) ^ k) + 1 := by
      apply Int.floor_lt.mpr
      exact_mod_cast hhi
    omega
  · apply Int.le_floor.mpr
    exact_mod_cast hlo

/-- Excluding powers of two at skipped reciprocal successors rules out every
dyadically unsafe skipped half-greedy rank. -/
theorem halfGreedySkipDyadicSafe_of_skippedReciprocalFloorSuccNotPow2
    (hfloor : HalfGreedySkippedReciprocalFloorSuccNotPow2) :
    HalfGreedySkipDyadicSafe := by
  intro n hskip
  have hp0 := halfGreedyResidualDisplayedNumerator_nonneg n
  have hpne : halfGreedyResidualDisplayedNumerator n ≠ 0 := by
    intro hpzero
    rcases halfGreedyResidualDisplayedNumerator_odd n with ⟨a, ha⟩
    rw [hpzero] at ha
    omega
  have hpNat : 0 < (halfGreedyResidualDisplayedNumerator n).natAbs :=
    Int.natAbs_pos.mpr hpne
  have hskipBlock :
      ¬ BlockTakeAt
        (halfGreedyResidualDisplayedNumerator n).natAbs
        (halfGreedyPrefixDenominator n) (n + 1) := by
    simpa only [greedyHalf_take_iff_BlockTakeAt n] using hskip
  by_contra hnotSafe
  have hunsafe :
      ¬ BlockDyadicSafeAt
        (halfGreedyResidualDisplayedNumerator n).natAbs
        (halfGreedyPrefixDenominator n) (n + 1) := by
    intro hsafe
    apply hnotSafe
    exact (greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos n).1
      (greedyHalfRemainder_le_nextDyadic_of_BlockSafe n hsafe)
  have heq := floor_two_mul_div_add_one_eq_pow_of_unsafe_skip
    hpNat hskipBlock hunsafe
  apply hfloor n hskip
  refine ⟨n + 1, ?_⟩
  have hpcast :
      (((halfGreedyResidualDisplayedNumerator n).natAbs : ℕ) : ℤ) =
        halfGreedyResidualDisplayedNumerator n := by
    simp [Int.natAbs_of_nonneg hp0]
  have hpcastQ :
      (((halfGreedyResidualDisplayedNumerator n).natAbs : ℕ) : ℚ) =
        (halfGreedyResidualDisplayedNumerator n : ℚ) := by
    rw [← hpcast]
    norm_num
  simpa only [Nat.cast_mul, Nat.cast_ofNat, hpcastQ] using heq

/-- The orbit-wide reciprocal-floor obstruction is a convenient stronger
specialization of the skipped-rank condition. -/
theorem halfGreedySkipDyadicSafe_of_reciprocalFloorSuccNotPow2
    (hfloor : HalfGreedyReciprocalFloorSuccNotPow2) :
    HalfGreedySkipDyadicSafe :=
  halfGreedySkipDyadicSafe_of_skippedReciprocalFloorSuccNotPow2
    (halfGreedySkippedReciprocalFloorSuccNotPow2_of_all hfloor)

/-- The skipped-rank reciprocal-floor obstruction feeds the conditional
achievement-set consumer. -/
theorem half_mem_mersenneAchievementSet_of_skippedReciprocalFloorSuccNotPow2
    (hfloor : HalfGreedySkippedReciprocalFloorSuccNotPow2) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_skipDyadicSafe
    (halfGreedySkipDyadicSafe_of_skippedReciprocalFloorSuccNotPow2 hfloor)

/-- The reciprocal-floor obstruction therefore feeds the existing conditional
achievement-set consumer. -/
theorem half_mem_mersenneAchievementSet_of_reciprocalFloorSuccNotPow2
    (hfloor : HalfGreedyReciprocalFloorSuccNotPow2) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_skipDyadicSafe
    (halfGreedySkipDyadicSafe_of_reciprocalFloorSuccNotPow2 hfloor)

/-- The unit residual makes `R = 2D` integral, so `R + 1` is an odd integer
`≥ 3`, hence never a power of two. -/
theorem halfGreedy_reciprocalFloorSucc_not_pow2_of_unit
    (n : ℕ) (hp : halfGreedyResidualDisplayedNumerator n = 1)
    (hD : 0 < halfGreedyPrefixDenominator n) :
    ¬ ∃ e : ℕ,
      Int.floor
          ((2 * (halfGreedyPrefixDenominator n : ℚ)) /
            (halfGreedyResidualDisplayedNumerator n : ℚ) + 1) =
        ((2 : ℤ) ^ e) := by
  intro h
  rcases h with ⟨e, he⟩
  have hpQ : (halfGreedyResidualDisplayedNumerator n : ℚ) = 1 := by
    exact_mod_cast hp
  rw [hpQ] at he
  have hR :
      (2 * (halfGreedyPrefixDenominator n : ℚ)) / 1 + 1 =
        ((2 * halfGreedyPrefixDenominator n + 1 : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hR] at he
  have hfloor :
      Int.floor (((2 * halfGreedyPrefixDenominator n + 1 : ℕ) : ℚ)) =
        ((2 * halfGreedyPrefixDenominator n + 1 : ℕ) : ℤ) :=
    Int.floor_natCast _
  rw [hfloor] at he
  have hodd : Odd (2 * halfGreedyPrefixDenominator n + 1) :=
    odd_two_mul_add_one _
  have hoddZ :
      Odd (((2 * halfGreedyPrefixDenominator n + 1 : ℕ) : ℤ)) :=
    hodd.natCast
  cases e with
  | zero =>
      have heq :
          ((2 * halfGreedyPrefixDenominator n + 1 : ℕ) : ℤ) = 1 := by
        simpa using he
      have hge :
          (3 : ℤ) ≤ ((2 * halfGreedyPrefixDenominator n + 1 : ℕ) : ℤ) := by
        have : 1 ≤ halfGreedyPrefixDenominator n := hD
        exact_mod_cast (by omega : 3 ≤ 2 * halfGreedyPrefixDenominator n + 1)
      linarith
  | succ e =>
      have heven : Even (((2 : ℤ) ^ (e + 1))) := by
        refine ⟨(2 : ℤ) ^ e, ?_⟩
        rw [pow_succ]
        ring
      have hoddPow : Odd (((2 : ℤ) ^ (e + 1))) := by
        rwa [← he]
      exact Int.not_even_iff_odd.2 hoddPow heven

/-- Unit segment: ranks `≤ 19` satisfy the reciprocal-floor invariant. -/
theorem halfGreedy_reciprocalFloorSucc_not_pow2_of_le_19
    (n : ℕ) (hn : n ≤ 19) :
    ¬ ∃ e : ℕ,
      Int.floor
          ((2 * (halfGreedyPrefixDenominator n : ℚ)) /
            (halfGreedyResidualDisplayedNumerator n : ℚ) + 1) =
        ((2 : ℤ) ^ e) :=
  halfGreedy_reciprocalFloorSucc_not_pow2_of_unit n
    (halfGreedyResidualDisplayedNumerator_eq_one_of_le_19 n hn)
    (Rat.den_pos (halfGreedyPrefixRat n))


/-! ## Unit take-transport + take-20 kill

Nat core `δ(δ+1) < 4D²` under pred-safe unit take (⇒ `α > 2^b+1` analytically).
Half-greedy take 20: concrete `α = 240503379313/120163 ∈ (2^{20}+1, 2^{21})`,
so `⌊α⌋` is not a power of two.

Skip-block equivalence: after take `b` with next take `c`, constant `R'` makes
every skip in `(b,c)` dyadic-safe iff `⌊R'+1⌋ ≠ 2^{c-1}`. The fixture
`(7,17)` fails with `⌊R'+1⌋ = 16`; the invariant is half-greedy-specific.
-/

def unitTakenReciprocalSucc (D b : ℕ) : ℚ :=
  (((2 * D + 1 : ℕ) : ℚ) * ((2 ^ b - 1 : ℕ) : ℚ) - (2 * D : ℕ)) /
    (((2 ^ b - 1 : ℕ) - 2 * D : ℕ) : ℚ)

theorem unitTake_delta_sq_lt_four_D_sq
    {D b : ℕ} (hb : 2 ≤ b)
    (hpred : 2 ^ (b - 1) ≤ 2 * D)
    (hδ : 2 * D < 2 ^ b - 1) :
    let δ := (2 ^ b - 1) - 2 * D
    δ * (δ + 1) < 4 * D ^ 2 := by
  intro δ
  have hb1 : 1 ≤ b := by omega
  have hδmax : δ ≤ 2 ^ (b - 1) - 1 := by
    have : 2 ^ b = 2 * 2 ^ (b - 1) := by
      rw [← pow_succ']
      simp [Nat.sub_add_cancel hb1]
    omega
  have hpow_sq : (2 ^ (b - 1)) ^ 2 = 2 ^ (2 * (b - 1)) := by
    rw [← pow_mul]; ac_rfl
  have h4D : 2 ^ (2 * (b - 1)) ≤ 4 * D ^ 2 := by
    have : (2 ^ (b - 1)) ^ 2 ≤ (2 * D) ^ 2 := Nat.pow_le_pow_left hpred 2
    have hR : (2 * D) ^ 2 = 4 * D ^ 2 := by ring
    rwa [hpow_sq, hR] at this
  have hstrict : δ * (δ + 1) < 2 ^ (2 * (b - 1)) := by
    have h1 : δ + 1 ≤ 2 ^ (b - 1) := by omega
    have hpos : 0 < 2 ^ (b - 1) := Nat.pow_pos (by decide)
    calc
      δ * (δ + 1) ≤ (2 ^ (b - 1) - 1) * 2 ^ (b - 1) :=
        Nat.mul_le_mul hδmax h1
      _ = 2 ^ (b - 1) * 2 ^ (b - 1) - 2 ^ (b - 1) := by
        rw [Nat.sub_mul, one_mul]
      _ = 2 ^ (2 * (b - 1)) - 2 ^ (b - 1) := by
        rw [← pow_add]; simp [two_mul]
      _ < 2 ^ (2 * (b - 1)) := Nat.sub_lt (Nat.pow_pos (by decide)) hpos
  exact lt_of_lt_of_le hstrict h4D

theorem floor_not_pow2_of_mem_Ioo_pow_succ
    {x : ℚ} {n : ℕ}
    (hlo : ((2 : ℚ) ^ n + 1) < x)
    (hhi : x < (2 : ℚ) ^ (n + 1)) :
    ¬ ∃ e : ℕ, Int.floor x = ((2 : ℤ) ^ e) := by
  rintro ⟨e, he⟩
  have hfloor_ge : ((2 : ℕ) ^ n + 1 : ℤ) ≤ Int.floor x := by
    have hle : ((↑(2 ^ n + 1 : ℕ) : ℚ)) ≤ x := by
      have : (↑(2 ^ n + 1 : ℕ) : ℚ) = (2 : ℚ) ^ n + 1 := by
        push_cast; rfl
      linarith
    exact Int.le_floor.mpr hle
  have hfloor_lt : Int.floor x < ((2 : ℕ) ^ (n + 1) : ℤ) := by
    have hlt : x < (↑(2 ^ (n + 1) : ℕ) : ℚ) := by
      have : (↑(2 ^ (n + 1) : ℕ) : ℚ) = (2 : ℚ) ^ (n + 1) := by
        push_cast; rfl
      linarith
    exact Int.floor_lt.mpr hlt
  have hgt : ((2 : ℕ) ^ n : ℤ) < Int.floor x := by omega
  by_cases h : e ≤ n
  · have : (2 : ℤ) ^ e ≤ (2 : ℤ) ^ n :=
      pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) h
    have : Int.floor x ≤ ((2 : ℕ) ^ n : ℤ) := by
      simpa [he] using this
    linarith
  · have : n + 1 ≤ e := by omega
    have : (2 : ℤ) ^ (n + 1) ≤ (2 : ℤ) ^ e :=
      pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) this
    have : ((2 : ℕ) ^ (n + 1) : ℤ) ≤ Int.floor x := by
      simpa [he] using this
    linarith

theorem halfGreedyPrefixDenominator_19 :
    halfGreedyPrefixDenominator 19 = 344043 := by
  rw [halfGreedyPrefixDenominator,
    halfGreedyPrefixRat_eq_half_sub_remainder]
  norm_num [greedyMersenneRemainderRat, mersenneWeightRat]

theorem unitTakenReciprocalSucc_take20 :
    unitTakenReciprocalSucc 344043 20 =
      (240503379313 : ℚ) / 120163 := by
  norm_num [unitTakenReciprocalSucc]

theorem halfGreedy_take20_unitTakenReciprocalSucc_mem_Ioo :
    ((2 : ℚ) ^ 20 + 1) <
        unitTakenReciprocalSucc (halfGreedyPrefixDenominator 19) 20 ∧
      unitTakenReciprocalSucc (halfGreedyPrefixDenominator 19) 20 <
        (2 : ℚ) ^ 21 := by
  rw [halfGreedyPrefixDenominator_19, unitTakenReciprocalSucc_take20]
  constructor <;> norm_num

theorem halfGreedy_take20_reciprocalFloorSucc_not_pow2 :
    ¬ ∃ e : ℕ,
      Int.floor (unitTakenReciprocalSucc (halfGreedyPrefixDenominator 19) 20) =
        ((2 : ℤ) ^ e) :=
  floor_not_pow2_of_mem_Ioo_pow_succ
    halfGreedy_take20_unitTakenReciprocalSucc_mem_Ioo.1
    halfGreedy_take20_unitTakenReciprocalSucc_mem_Ioo.2

/-- Pred-safe unit take forces the Nat inequality behind `α > 2^b+1`.
(Rational lifting deferred; take-20 uses the concrete value above.) -/
theorem unitTake_predSafe_delta_bound
    {D b : ℕ} (hb : 2 ≤ b)
    (hpred : 2 ^ (b - 1) ≤ 2 * D)
    (hδ : 2 * D < 2 ^ b - 1) :
    ((2 ^ b - 1) - 2 * D) * (((2 ^ b - 1) - 2 * D) + 1) < 4 * D ^ 2 :=
  unitTake_delta_sq_lt_four_D_sq hb hpred hδ

#print axioms unitTake_delta_sq_lt_four_D_sq
#print axioms floor_two_mul_div_add_one_eq_pow_of_unsafe_skip
#print axioms halfGreedySkipDyadicSafe_of_skippedReciprocalFloorSuccNotPow2
#print axioms half_mem_mersenneAchievementSet_of_skippedReciprocalFloorSuccNotPow2
#print axioms halfGreedySkipDyadicSafe_of_reciprocalFloorSuccNotPow2
#print axioms half_mem_mersenneAchievementSet_of_reciprocalFloorSuccNotPow2
#print axioms floor_not_pow2_of_mem_Ioo_pow_succ
#print axioms halfGreedy_take20_reciprocalFloorSucc_not_pow2
#print axioms twoThirdsMargin_of_blockDyadicSafe
#print axioms blockDyadicSafeAt_of_halfGreedyNextDyadicExcess_nonpos
#print axioms halfGreedySkippedTwoThirdsMargin_of_skipDyadicSafe
#print axioms exists_twoThirdsMargin_not_blockDyadicSafe
#print axioms halfGreedyRemainder_lt_tail_of_skippedTwoThirdsMargin
#print axioms half_mem_mersenneAchievementSet_of_skippedTwoThirdsMargin

/-! ## Consecutive-take auto-safety

If after take at `b` one has `rem ≥ w_{b+1}`, then `rem` lies in **no**
unsafe sliver `(2^{-k}, w_k)` for any `k > b`:
- at `k = b+1`: `rem ≥ w_{b+1}` exits the open sliver;
- at `k > b+1`: `w_k < w_{b+1} ≤ rem` blocks `rem < w_k`.

So every consecutive take run preserves dyadic safety of all future skips
until the residual drops below the next weight (singleton case).
-/

/-- Mersenne weights are strictly decreasing. -/
theorem mersenneWeightRat_strictAnti
    {k m : ℕ} (hk : 1 ≤ k) (hlt : k < m) :
    mersenneWeightRat m < mersenneWeightRat k := by
  unfold mersenneWeightRat
  have hden : (2 : ℚ) ^ k - 1 < (2 : ℚ) ^ m - 1 := by
    have : (2 : ℚ) ^ k < (2 : ℚ) ^ m :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℚ) < 2) hlt
    linarith
  have hpos : (0 : ℚ) < (2 : ℚ) ^ k - 1 := by
    have : (1 : ℚ) < 2 ^ k :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  exact one_div_lt_one_div_of_lt hpos hden

/-- Unsafe open sliver at rank `k`. -/
def unsafeDyadicSliver (k : ℕ) : Set ℚ :=
  Set.Ioo (1 / (2 : ℚ) ^ k) (mersenneWeightRat k)

/-- Consecutive take ⇒ post-residual avoids every later unsafe sliver. -/
theorem consecutiveTake_avoids_unsafeSliver
    {b : ℕ} {rem : ℚ} (hb : 1 ≤ b)
    (hnext : mersenneWeightRat (b + 1) ≤ rem) :
    ∀ k : ℕ, b < k → rem ∉ unsafeDyadicSliver k := by
  intro k hk
  intro hin
  have hlo : 1 / (2 : ℚ) ^ k < rem := hin.1
  have hhi : rem < mersenneWeightRat k := hin.2
  cases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hk) with
  | inl heq =>
      -- k = b+1
      have : k = b + 1 := by omega
      subst this
      linarith [hnext, hhi]
  | inr hlt =>
      -- k ≥ b+2 ⇒ w_k < w_{b+1} ≤ rem
      have hk' : b + 1 < k := by omega
      have hw : mersenneWeightRat k < mersenneWeightRat (b + 1) :=
        mersenneWeightRat_strictAnti (by omega) hk'
      linarith [hnext, hhi, hw]

#print axioms consecutiveTake_avoids_unsafeSliver

/-! ## Unit take ⇒ consecutive when `α < 2^{b+1}`

After pred-safe unit take, `α > 2^b+1`. If also `α < 2^{b+1}`, then
`R' < 2^{b+1}-1`, i.e. `rem' > w_{b+1}`, so the next decision is a take —
and `consecutiveTake_avoids_unsafeSliver` finishes the post-state.
Half-greedy take 20 is exactly this branch, discharged below by the concrete
post-residual rather than through the general `α = R' + 1` rewrite (which is
the one step this file does not carry).
-/

/-- Take-20 post-residual meets `w_21` (consecutive branch). -/
theorem halfGreedy_take20_post_exceeds_nextWeight :
    mersenneWeightRat 21 ≤
      (120163 : ℚ) / 240503259150 := by
  norm_num [mersenneWeightRat]

/-- Combine: take-20 post-state avoids every later unsafe sliver. -/
theorem halfGreedy_take20_avoids_later_unsafeSliver :
    ∀ k : ℕ, 20 < k →
      (120163 : ℚ) / 240503259150 ∉ unsafeDyadicSliver k :=
  consecutiveTake_avoids_unsafeSliver (b := 20) (by omega)
    halfGreedy_take20_post_exceeds_nextWeight

#print axioms halfGreedy_take20_avoids_later_unsafeSliver

end Erdos249257
