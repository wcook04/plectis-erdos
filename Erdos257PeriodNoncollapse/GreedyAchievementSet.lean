import Erdos257PeriodNoncollapse.CertificateKernel
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Perfect

/-!
# Greedy geometry for the Mersenne achievement set

For positive exponents put `w(n) = 1 / (2^n - 1)` and let `T(n)` be the
mass strictly after exponent `n`.  This file formalizes the dependency-critical
part of the greedy-achievement route for Erdős problem #257:

* summability, tail recurrence, and the strict superincreasing inequality;
* the quantitative gap asymptotic `(2/3)·4⁻ⁿ + O(8⁻ⁿ)` with an explicit
  higher-channel remainder bound;
* normalized support coding through the existing `erdosSupportSeries`;
* compactness and perfection from a continuous injective binary coding;
* nested finite-cylinder stages, their exact Lebesgue measures, and continuity
  from above;
* the measure-one and nowhere-dense conclusions, hence the precise fat-Cantor
  status of the achievement set;
* exact real and rational greedy recurrences;
* the all-level survival characterization, with the necessary nonnegativity
  guard made explicit;
* finite rational upper enclosures for tails and sound death certificates;
* the exact level-one death certificate for `3/4`;
* uniqueness of normalized support coding and computability of the digits of
  a rational value already known to belong to the achievement set.

`CertifiedGreedyMersenneDeath` is one-sided: a certificate proves
nonmembership, while
failure to find a certificate or survival through any finite depth proves
nothing about membership.  The index-zero support bit is normalized away
because its analytic weight is zero.  Nothing here settles the universal
problem, and no finite computation is promoted to an infinite-support claim.

No novelty or priority claim is made for the theorems in this file.
-/

namespace Erdos257PeriodNoncollapse

open scoped ENNReal

open Filter Set MeasureTheory Topology

/-! ## Weights and tails -/

/-- The exact rational Mersenne weight `1 / (2^n - 1)`.  Its meaningful
support indices are positive; at index zero Lean's division convention gives
zero. -/
def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

/-- The real Mersenne weight `1 / (2^n - 1)`. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

@[simp] theorem mersenneWeightRat_zero : mersenneWeightRat 0 = 0 := by
  norm_num [mersenneWeightRat]

@[simp] theorem mersenneWeight_zero : mersenneWeight 0 = 0 := by
  norm_num [mersenneWeight]

@[simp] theorem cast_mersenneWeightRat (n : ℕ) :
    ((mersenneWeightRat n : ℚ) : ℝ) = mersenneWeight n := by
  simp [mersenneWeightRat, mersenneWeight]

theorem mersenneWeight_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneWeight n := by
  unfold mersenneWeight
  have hpow : (1 : ℝ) < 2 ^ n :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  exact one_div_pos.mpr (sub_pos.mpr hpow)

theorem mersenneWeightRat_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneWeightRat n := by
  unfold mersenneWeightRat
  have hpow : (1 : ℚ) < 2 ^ n :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  exact one_div_pos.mpr (sub_pos.mpr hpow)

/-- The positive-index Mersenne weights form a summable real series. -/
theorem summable_mersenneWeight :
    Summable (fun k : ℕ => mersenneWeight (k + 1)) := by
  simpa [mersenneWeight] using
    (summable_erdos_term 2 (by norm_num) (fun k : ℕ => k + 1)
      (fun _ _ h => Nat.add_lt_add_right h 1) (by norm_num))

/-- The remaining mass after processing exponents `1, ..., n`. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

theorem summable_mersenneTail (n : ℕ) :
    Summable (fun k : ℕ => mersenneWeight (n + k + 1)) := by
  have h := (summable_nat_add_iff n).mpr summable_mersenneWeight
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem mersenneTail_nonneg (n : ℕ) : 0 ≤ mersenneTail n := by
  unfold mersenneTail
  exact tsum_nonneg fun k => (mersenneWeight_pos (by omega : 0 < n + k + 1)).le

theorem mersenneTail_pos (n : ℕ) : 0 < mersenneTail n := by
  unfold mersenneTail
  exact (summable_mersenneTail n).tsum_pos
    (fun k => (mersenneWeight_pos (by omega : 0 < n + k + 1)).le)
    0 (mersenneWeight_pos (by omega : 0 < n + 0 + 1))

/-- Splitting off the next positive exponent gives the exact tail recurrence. -/
theorem mersenneTail_eq_weight_add (n : ℕ) :
    mersenneTail n = mersenneWeight (n + 1) + mersenneTail (n + 1) := by
  unfold mersenneTail
  rw [(summable_mersenneTail n).tsum_eq_zero_add]
  congr 1
  apply tsum_congr
  intro k
  congr 1
  omega

/-- Adjacent weights shrink by strictly more than a factor of two. -/
theorem two_mul_mersenneWeight_succ_lt {n : ℕ} (hn : 0 < n) :
    2 * mersenneWeight (n + 1) < mersenneWeight n := by
  have hx : (1 : ℝ) < 2 ^ n :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  have hpow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by
    rw [pow_succ]
    ring
  rw [mersenneWeight, mersenneWeight, hpow]
  have hden₁ : (0 : ℝ) < 2 ^ n - 1 := by linarith
  have hden₂ : (0 : ℝ) < 2 * 2 ^ n - 1 := by linarith
  rw [mul_one_div, div_lt_div_iff₀ hden₂ hden₁]
  linarith

/-- Iterating the adjacent ratio gives a geometric envelope. -/
theorem mersenneWeight_add_le_geometric (n j : ℕ) (hn : 0 < n) :
    mersenneWeight (n + j) ≤ mersenneWeight n * ((1 : ℝ) / 2) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep := two_mul_mersenneWeight_succ_lt (n := n + j) (by omega)
      calc
        mersenneWeight (n + (j + 1)) = mersenneWeight (n + j + 1) := by
          congr 1
        _ ≤ mersenneWeight (n + j) / 2 := by linarith
        _ ≤ (mersenneWeight n * ((1 : ℝ) / 2) ^ j) / 2 := by linarith
        _ = mersenneWeight n * ((1 : ℝ) / 2) ^ (j + 1) := by
          rw [pow_succ]
          ring

/-- A simple exact-rational upper enclosure for the remaining infinite tail. -/
theorem mersenneTail_le_two_mul_weight (n : ℕ) :
    mersenneTail n ≤ 2 * mersenneWeight (n + 1) := by
  have hf := summable_mersenneTail n
  have hg : Summable
      (fun k : ℕ => mersenneWeight (n + 1) * ((1 : ℝ) / 2) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)).mul_left _
  calc
    mersenneTail n
        ≤ ∑' k : ℕ, mersenneWeight (n + 1) * ((1 : ℝ) / 2) ^ k := by
          unfold mersenneTail
          exact hf.tsum_le_tsum
            (fun k => by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                mersenneWeight_add_le_geometric (n + 1) k (by omega)) hg
    _ = mersenneWeight (n + 1) *
          ∑' k : ℕ, ((1 : ℝ) / 2) ^ k := tsum_mul_left
    _ = 2 * mersenneWeight (n + 1) := by
      rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)]
      norm_num
      ring

/-- **Strict superincreasingness.**  Every positive-index weight is larger
than the entire tail following it. -/
theorem mersenneTail_lt_weight {n : ℕ} (hn : 0 < n) :
    mersenneTail n < mersenneWeight n := by
  exact lt_of_le_of_lt (mersenneTail_le_two_mul_weight n)
    (two_mul_mersenneWeight_succ_lt hn)

/-- The one-step enclosure is in fact strict. -/
theorem mersenneTail_lt_two_mul_weight (n : ℕ) :
    mersenneTail n < 2 * mersenneWeight (n + 1) := by
  rw [mersenneTail_eq_weight_add]
  have h := mersenneTail_lt_weight (n := n + 1) (by omega)
  linarith

/-- The remaining Mersenne mass tends to zero. -/
theorem tendsto_mersenneTail_zero :
    Tendsto mersenneTail atTop (nhds 0) := by
  have h := tendsto_sum_nat_add (fun k : ℕ => mersenneWeight (k + 1))
  have hshift := h.comp (tendsto_add_atTop_nat 0)
  simpa [mersenneTail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift

/-! ## Quantitative gap asymptotic -/

/-- The contribution of geometric channels of order at least three in one
Mersenne weight. -/
noncomputable def mersenneWeightRemainder (n : ℕ) : ℝ :=
  ((1 : ℝ) / 8) ^ n / (1 - ((1 : ℝ) / 2) ^ n)

/-- Exact separation of the first two geometric channels. -/
theorem mersenneWeight_eq_two_channels_add_remainder
    {n : ℕ} (hn : 0 < n) :
    mersenneWeight n
      = ((1 : ℝ) / 2) ^ n
        + ((1 : ℝ) / 4) ^ n
        + mersenneWeightRemainder n := by
  have hpow : (1 : ℝ) < 2 ^ n :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
  have hden : (2 : ℝ) ^ n - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hpow)
  have hpow0 : (2 : ℝ) ^ n ≠ 0 :=
    ne_of_gt (pow_pos (by norm_num) n)
  have hone : 1 - ((1 : ℝ) / 2) ^ n ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr
      (pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hn)))
  have hfour : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    conv_lhs => rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have height : (8 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 3 := by
    conv_lhs => rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  unfold mersenneWeight mersenneWeightRemainder
  simp only [div_pow, one_pow]
  rw [hfour, height]
  field_simp
  ring

theorem mersenneWeightRemainder_nonneg
    {n : ℕ} (hn : 0 < n) :
    0 ≤ mersenneWeightRemainder n := by
  unfold mersenneWeightRemainder
  exact div_nonneg (by positivity) (sub_nonneg.mpr (by
    exact
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans
        (by norm_num)))

theorem mersenneWeightRemainder_pos
    {n : ℕ} (hn : 0 < n) :
    0 < mersenneWeightRemainder n := by
  unfold mersenneWeightRemainder
  exact div_pos (by positivity) (sub_pos.mpr
    (pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hn)))

/-- Uniform third-channel bound for one weight. -/
theorem mersenneWeightRemainder_le
    {n : ℕ} (hn : 0 < n) :
    mersenneWeightRemainder n ≤ 2 * ((1 : ℝ) / 8) ^ n := by
  have hxle : ((1 : ℝ) / 2) ^ n ≤ (1 : ℝ) / 2 := by
    calc
      ((1 : ℝ) / 2) ^ n ≤ ((1 : ℝ) / 2) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = (1 : ℝ) / 2 := pow_one _
  have hden : 0 < 1 - ((1 : ℝ) / 2) ^ n := by linarith
  unfold mersenneWeightRemainder
  rw [div_le_iff₀ hden]
  have ha : 0 ≤ ((1 : ℝ) / 8) ^ n := by positivity
  nlinarith

/-- A shifted geometric series in the form used by all three channels. -/
theorem tsum_geometric_nat_add_succ
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑' k : ℕ, r ^ (n + k + 1) = r ^ (n + 1) * (1 - r)⁻¹ := by
  calc
    ∑' k : ℕ, r ^ (n + k + 1)
        = ∑' k : ℕ, r ^ (n + 1) * r ^ k := by
          apply tsum_congr
          intro k
          rw [← pow_add]
          congr 1
          omega
    _ = r ^ (n + 1) * ∑' k : ℕ, r ^ k := tsum_mul_left
    _ = r ^ (n + 1) * (1 - r)⁻¹ := by
      rw [tsum_geometric_of_lt_one hr0 hr1]

theorem tsum_half_nat_add_succ (n : ℕ) :
    ∑' k : ℕ, ((1 : ℝ) / 2) ^ (n + k + 1) = ((1 : ℝ) / 2) ^ n := by
  rw [tsum_geometric_nat_add_succ _ (by norm_num) (by norm_num)]
  rw [pow_succ]
  norm_num
  ring

theorem tsum_quarter_nat_add_succ (n : ℕ) :
    ∑' k : ℕ, ((1 : ℝ) / 4) ^ (n + k + 1)
      = (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n := by
  rw [tsum_geometric_nat_add_succ _ (by norm_num) (by norm_num)]
  rw [pow_succ]
  norm_num
  ring

theorem tsum_eighth_nat_add_succ (n : ℕ) :
    ∑' k : ℕ, ((1 : ℝ) / 8) ^ (n + k + 1)
      = (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n := by
  rw [tsum_geometric_nat_add_succ _ (by norm_num) (by norm_num)]
  rw [pow_succ]
  norm_num
  ring

/-- The accumulated contribution of channels of order at least three after
exponent `n`. -/
noncomputable def mersenneWeightRemainderTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeightRemainder (n + k + 1)

theorem summable_mersenneWeightRemainderTail (n : ℕ) :
    Summable (fun k : ℕ => mersenneWeightRemainder (n + k + 1)) := by
  have hgeo : Summable (fun k : ℕ =>
      2 * ((1 : ℝ) / 8) ^ (n + k + 1)) := by
    have hbase := summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 : ℝ) / 8 < 1)
    have hshift := (summable_nat_add_iff (n + 1)).mpr hbase
    have hmul := hshift.mul_left 2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmul
  exact Summable.of_nonneg_of_le
    (fun k => mersenneWeightRemainder_nonneg (by omega))
    (fun k => mersenneWeightRemainder_le (by omega)) hgeo

theorem mersenneWeightRemainderTail_nonneg (n : ℕ) :
    0 ≤ mersenneWeightRemainderTail n := by
  unfold mersenneWeightRemainderTail
  exact tsum_nonneg fun k => mersenneWeightRemainder_nonneg (by omega)

theorem mersenneWeightRemainderTail_pos (n : ℕ) :
    0 < mersenneWeightRemainderTail n := by
  unfold mersenneWeightRemainderTail
  exact (summable_mersenneWeightRemainderTail n).tsum_pos
    (fun k => (mersenneWeightRemainder_pos (by omega)).le)
    0 (mersenneWeightRemainder_pos (by omega))

/-- The accumulated higher-channel tail is at most `(2/7)·8⁻ⁿ`. -/
theorem mersenneWeightRemainderTail_le (n : ℕ) :
    mersenneWeightRemainderTail n
      ≤ (2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n := by
  have henv : Summable (fun k : ℕ =>
      2 * ((1 : ℝ) / 8) ^ (n + k + 1)) := by
    have hbase := summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 : ℝ) / 8 < 1)
    have hshift := (summable_nat_add_iff (n + 1)).mpr hbase
    have hmul := hshift.mul_left 2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmul
  calc
    mersenneWeightRemainderTail n
        ≤ ∑' k : ℕ, 2 * ((1 : ℝ) / 8) ^ (n + k + 1) := by
          unfold mersenneWeightRemainderTail
          exact (summable_mersenneWeightRemainderTail n).tsum_le_tsum
            (fun k => mersenneWeightRemainder_le (by omega)) henv
    _ = 2 * ∑' k : ℕ, ((1 : ℝ) / 8) ^ (n + k + 1) := tsum_mul_left
    _ = (2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n := by
      rw [tsum_eighth_nat_add_succ]
      ring

/-- The third geometric channel is a strict lower enclosure of the complete
higher-channel tail. -/
theorem one_seventh_eighth_pow_lt_mersenneWeightRemainderTail (n : ℕ) :
    (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n <
      mersenneWeightRemainderTail n := by
  have hle : ∀ k : ℕ,
      ((1 : ℝ) / 8) ^ (n + k + 1) ≤
        mersenneWeightRemainder (n + k + 1) := by
    intro k
    unfold mersenneWeightRemainder
    have hden : 0 < 1 - ((1 : ℝ) / 2) ^ (n + k + 1) := by
      exact sub_pos.mpr
        (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))
    rw [le_div_iff₀ hden]
    have hx : 0 ≤ ((1 : ℝ) / 8) ^ (n + k + 1) := by positivity
    have hy : 0 ≤ ((1 : ℝ) / 2) ^ (n + k + 1) := by positivity
    have hxy : 0 ≤ ((1 : ℝ) / 8) ^ (n + k + 1) *
        ((1 : ℝ) / 2) ^ (n + k + 1) := mul_nonneg hx hy
    nlinarith
  have hstrict :
      ((1 : ℝ) / 8) ^ (n + 0 + 1) <
        mersenneWeightRemainder (n + 0 + 1) := by
    unfold mersenneWeightRemainder
    have hden : 0 < 1 - ((1 : ℝ) / 2) ^ (n + 0 + 1) := by
      exact sub_pos.mpr
        (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))
    rw [lt_div_iff₀ hden]
    have hx : 0 < ((1 : ℝ) / 8) ^ (n + 0 + 1) := by positivity
    have hy : 0 < ((1 : ℝ) / 2) ^ (n + 0 + 1) := by positivity
    have hxy : 0 < ((1 : ℝ) / 8) ^ (n + 0 + 1) *
        ((1 : ℝ) / 2) ^ (n + 0 + 1) := mul_pos hx hy
    nlinarith
  have hsum := Summable.tsum_lt_tsum_of_nonneg (i := 0)
    (f := fun k : ℕ => ((1 : ℝ) / 8) ^ (n + k + 1))
    (g := fun k : ℕ => mersenneWeightRemainder (n + k + 1))
    (fun k => by positivity) hle hstrict
    (summable_mersenneWeightRemainderTail n)
  rw [tsum_eighth_nat_add_succ] at hsum
  exact hsum

/-- Exact tail expansion through the second geometric channel. -/
theorem mersenneTail_eq_two_channels_add_remainderTail (n : ℕ) :
    mersenneTail n
      = ((1 : ℝ) / 2) ^ n
        + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
        + mersenneWeightRemainderTail n := by
  have hhalf : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ (n + k + 1)) := by
    have hbase := summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    have hshift := (summable_nat_add_iff (n + 1)).mpr hbase
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have hquarter : Summable (fun k : ℕ => ((1 : ℝ) / 4) ^ (n + k + 1)) := by
    have hbase := summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 : ℝ) / 4 < 1)
    have hshift := (summable_nat_add_iff (n + 1)).mpr hbase
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have hrem := summable_mersenneWeightRemainderTail n
  calc
    mersenneTail n
        = ∑' k : ℕ, (((1 : ℝ) / 2) ^ (n + k + 1)
            + ((1 : ℝ) / 4) ^ (n + k + 1)
            + mersenneWeightRemainder (n + k + 1)) := by
          unfold mersenneTail
          apply tsum_congr
          intro k
          exact mersenneWeight_eq_two_channels_add_remainder (by omega)
    _ = (∑' k : ℕ, ((1 : ℝ) / 2) ^ (n + k + 1))
          + (∑' k : ℕ, ((1 : ℝ) / 4) ^ (n + k + 1))
          + ∑' k : ℕ, mersenneWeightRemainder (n + k + 1) := by
          rw [(hhalf.add hquarter).tsum_add hrem, hhalf.tsum_add hquarter]
    _ = ((1 : ℝ) / 2) ^ n
          + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
          + mersenneWeightRemainderTail n := by
          rw [tsum_half_nat_add_succ, tsum_quarter_nat_add_succ]
          rfl

/-- The Mersenne gap has leading term `(2/3)·4⁻ⁿ`; its exact error is the
difference of the one-weight and tail higher-channel remainders. -/
theorem mersenneGap_sub_main_eq_remainder_sub_tail
    {n : ℕ} (hn : 0 < n) :
    (mersenneWeight n - mersenneTail n)
        - (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
      = mersenneWeightRemainder n - mersenneWeightRemainderTail n := by
  rw [mersenneWeight_eq_two_channels_add_remainder hn,
    mersenneTail_eq_two_channels_add_remainderTail]
  ring

/-- Explicit norm certificate for the formal development.s gap asymptotic. -/
theorem mersenneGap_asymptotic_bound {n : ℕ} (hn : 0 < n) :
    ‖(mersenneWeight n - mersenneTail n)
        - (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n‖
      ≤ 3 * ‖((1 : ℝ) / 8) ^ n‖ := by
  rw [mersenneGap_sub_main_eq_remainder_sub_tail hn]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hR0 := mersenneWeightRemainder_nonneg hn
  have hT0 := mersenneWeightRemainderTail_nonneg n
  have hR := mersenneWeightRemainder_le hn
  have hT := mersenneWeightRemainderTail_le n
  have hpow : 0 ≤ ((1 : ℝ) / 8) ^ n := by positivity
  calc
    |mersenneWeightRemainder n - mersenneWeightRemainderTail n|
        ≤ |mersenneWeightRemainder n| + |mersenneWeightRemainderTail n| :=
          abs_sub _ _
    _ = mersenneWeightRemainder n + mersenneWeightRemainderTail n := by
      rw [abs_of_nonneg hR0, abs_of_nonneg hT0]
    _ ≤ 2 * ((1 : ℝ) / 8) ^ n
          + (2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n := add_le_add hR hT
    _ ≤ 3 * |((1 : ℝ) / 8) ^ n| := by
      rw [abs_of_nonneg hpow]
      nlinarith

/-- **gap asymptotic.**  In positive indexing,
`w_n - T_n = (2/3)·4⁻ⁿ + O(8⁻ⁿ)`, with an explicit valid `O` constant `3`. -/
theorem mersenneGap_isBigOWith :
    Asymptotics.IsBigOWith 3 atTop
      (fun n : ℕ =>
        (mersenneWeight n - mersenneTail n)
          - (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n)
      (fun n : ℕ => ((1 : ℝ) / 8) ^ n) := by
  apply Asymptotics.IsBigOWith.of_bound
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact mersenneGap_asymptotic_bound (by omega)

/-! ## Normalized support coding -/

/-- The value coded by a set of positive exponents.  The sequence index is
zero-based while the exponent supplied to the weight is `k+1`. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

theorem summable_positiveMersenneSupportIndicator (A : Set ℕ) :
    Summable (fun k : ℕ => Set.indicator A mersenneWeight (k + 1)) := by
  have h := summable_mersenneWeight.indicator {k : ℕ | k + 1 ∈ A}
  refine h.congr fun k => ?_
  by_cases hk : k + 1 ∈ A
  · simp [hk]
  · simp [hk]

/-- The portion of a support code strictly after exponent `n`. -/
noncomputable def positiveMersenneSupportSuffix (A : Set ℕ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (n + k + 1)

theorem summable_positiveMersenneSupportSuffix (A : Set ℕ) (n : ℕ) :
    Summable (fun k : ℕ => Set.indicator A mersenneWeight (n + k + 1)) := by
  have h := (summable_nat_add_iff n).mpr
    (summable_positiveMersenneSupportIndicator A)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem positiveMersenneSupportSuffix_nonneg (A : Set ℕ) (n : ℕ) :
    0 ≤ positiveMersenneSupportSuffix A n := by
  unfold positiveMersenneSupportSuffix
  exact tsum_nonneg fun k => by
    by_cases hk : n + k + 1 ∈ A
    · rw [Set.indicator_of_mem hk]
      exact (mersenneWeight_pos (by omega)).le
    · rw [Set.indicator_of_notMem hk]

/-- A coded suffix is bounded by the full remaining mass. -/
theorem positiveMersenneSupportSuffix_le_tail (A : Set ℕ) (n : ℕ) :
    positiveMersenneSupportSuffix A n ≤ mersenneTail n := by
  unfold positiveMersenneSupportSuffix mersenneTail
  exact (summable_positiveMersenneSupportSuffix A n).tsum_le_tsum
    (fun k => by
      by_cases hk : n + k + 1 ∈ A
      · rw [Set.indicator_of_mem hk]
      · rw [Set.indicator_of_notMem hk]
        exact (mersenneWeight_pos (by omega)).le)
    (summable_mersenneTail n)

/-- Exact recurrence for a coded support suffix. -/
theorem positiveMersenneSupportSuffix_eq_indicator_add
    (A : Set ℕ) (n : ℕ) :
    positiveMersenneSupportSuffix A n
      = Set.indicator A mersenneWeight (n + 1)
        + positiveMersenneSupportSuffix A (n + 1) := by
  unfold positiveMersenneSupportSuffix
  rw [(summable_positiveMersenneSupportSuffix A n).tsum_eq_zero_add]
  congr 1
  apply tsum_congr
  intro k
  congr 2
  omega

/-- Finite-prefix decomposition of a normalized support code. -/
theorem positiveMersenneSupportValue_eq_prefix_add_suffix
    (A : Set ℕ) (n : ℕ) :
    positiveMersenneSupportValue A
      = (∑ k ∈ Finset.range n, Set.indicator A mersenneWeight (k + 1))
        + positiveMersenneSupportSuffix A n := by
  have h := (summable_positiveMersenneSupportIndicator A).sum_add_tsum_nat_add n
  simpa [positiveMersenneSupportValue, positiveMersenneSupportSuffix,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm

/-- The reindexed support value is exactly the existing #257 support series. -/
theorem positiveMersenneSupportValue_eq_erdosSupportSeries (A : Set ℕ) :
    positiveMersenneSupportValue A = erdosSupportSeries 2 A := by
  have hwhole : Summable (fun a : ℕ => Set.indicator A mersenneWeight a) := by
    refine (summable_erdosSupport_indicator 2 A (by norm_num)).congr fun a => ?_
    rfl
  have hsplit := hwhole.tsum_eq_zero_add
  have hzero : Set.indicator A mersenneWeight 0 = 0 := by
    by_cases hA : 0 ∈ A <;> simp [hA]
  calc
    positiveMersenneSupportValue A
        = ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1) := rfl
    _ = ∑' k : ℕ, Set.indicator A mersenneWeight k := by
      simpa [hzero] using hsplit.symm
    _ = erdosSupportSeries 2 A := by rfl

/-- The Mersenne achievement set, with the analytically invisible zero bit
normalized away. -/
def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

/-! ## Binary coding, compactness, and perfection -/

/-- One term of the binary coding of the achievement set. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)

/-- The support value coded by a binary sequence. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b

/-- The normalized positive support represented by a binary sequence. -/
def mersenneDigitSupport (b : ℕ → Fin 2) : Set ℕ :=
  {m : ℕ | ∃ k : ℕ, m = k + 1 ∧ b k = 1}

@[simp] theorem zero_not_mem_mersenneDigitSupport (b : ℕ → Fin 2) :
    0 ∉ mersenneDigitSupport b := by
  simp [mersenneDigitSupport]

@[simp] theorem succ_mem_mersenneDigitSupport_iff (b : ℕ → Fin 2) (k : ℕ) :
    k + 1 ∈ mersenneDigitSupport b ↔ b k = 1 := by
  constructor
  · rintro ⟨j, hj, hb⟩
    have hjk : j = k := by omega
    simpa [hjk] using hb
  · intro hb
    exact ⟨k, rfl, hb⟩

theorem positiveMersenneDigitValue_eq_supportValue (b : ℕ → Fin 2) :
    positiveMersenneDigitValue b
      = positiveMersenneSupportValue (mersenneDigitSupport b) := by
  unfold positiveMersenneDigitValue positiveMersenneSupportValue
  apply tsum_congr
  intro k
  by_cases hbk : b k = 0
  · simp [mersenneDigitTerm, mersenneDigitSupport, hbk]
  · have hbk' : b k = 1 := Fin.eq_one_of_ne_zero (b k) hbk
    simp [mersenneDigitTerm, mersenneDigitSupport, hbk']

theorem continuous_mersenneDigitTerm (k : ℕ) :
    Continuous (mersenneDigitTerm k) := by
  unfold mersenneDigitTerm
  fun_prop

theorem norm_mersenneDigitTerm_le (k : ℕ) (b : ℕ → Fin 2) :
    ‖mersenneDigitTerm k b‖ ≤ mersenneWeight (k + 1) := by
  by_cases hbk : b k = 0
  · simp [mersenneDigitTerm, hbk,
      (mersenneWeight_pos (n := k + 1) (by omega)).le]
  · have hbk' : b k = 1 := Fin.eq_one_of_ne_zero (b k) hbk
    simp only [mersenneDigitTerm, hbk', Fin.val_one, Nat.cast_one, one_mul,
      Real.norm_eq_abs]
    rw [abs_of_pos (mersenneWeight_pos (n := k + 1) (by omega))]

/-- The binary support coding is continuous in the product topology. -/
theorem continuous_positiveMersenneDigitValue :
    Continuous positiveMersenneDigitValue := by
  unfold positiveMersenneDigitValue
  exact continuous_tsum continuous_mersenneDigitTerm
    summable_mersenneWeight norm_mersenneDigitTerm_le

/-- The binary coding has exactly the normalized Mersenne achievement set as
its range. -/
theorem range_positiveMersenneDigitValue_eq :
    Set.range positiveMersenneDigitValue = mersenneAchievementSet := by
  classical
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨mersenneDigitSupport b, zero_not_mem_mersenneDigitSupport b,
      positiveMersenneDigitValue_eq_supportValue b⟩
  · rintro ⟨A, hA0, rfl⟩
    let b : ℕ → Fin 2 := fun k => if k + 1 ∈ A then 1 else 0
    refine ⟨b, ?_⟩
    unfold positiveMersenneDigitValue positiveMersenneSupportValue
    apply tsum_congr
    intro k
    by_cases hk : k + 1 ∈ A
    · simp [mersenneDigitTerm, b, hk]
    · simp [mersenneDigitTerm, b, hk]

/-- **compactness.**  The achievement set is the continuous image
of compact binary sequence space. -/
theorem isCompact_mersenneAchievementSet : IsCompact mersenneAchievementSet := by
  rw [← range_positiveMersenneDigitValue_eq, ← Set.image_univ]
  exact isCompact_univ.image continuous_positiveMersenneDigitValue

theorem isClosed_mersenneAchievementSet : IsClosed mersenneAchievementSet :=
  isCompact_mersenneAchievementSet.isClosed

/-! ## Nested cylinder stages -/

/-- Starting after exponent `n`, retain `depth` binary choices and replace the
unresolved suffix by its full interval enclosure. -/
noncomputable def mersenneCylinderStageFrom (n : ℕ) : ℕ → Set ℝ
  | 0 => Set.Icc 0 (mersenneTail n)
  | depth + 1 =>
      mersenneCylinderStageFrom (n + 1) depth ∪
        (fun x : ℝ => mersenneWeight (n + 1) + x) ''
          mersenneCylinderStageFrom (n + 1) depth

/-- The depth-`n` cylinder enclosure of the full achievement set. -/
noncomputable def mersenneCylinderStage (depth : ℕ) : Set ℝ :=
  mersenneCylinderStageFrom 0 depth

/-- Every tail-cylinder stage stays inside its unresolved convex hull. -/
theorem mersenneCylinderStageFrom_subset_Icc (n depth : ℕ) :
    mersenneCylinderStageFrom n depth ⊆ Set.Icc 0 (mersenneTail n) := by
  induction depth generalizing n with
  | zero =>
      intro x hx
      simpa [mersenneCylinderStageFrom] using hx
  | succ depth ih =>
      intro x hx
      simp only [mersenneCylinderStageFrom, Set.mem_union] at hx
      rcases hx with hx | hx
      · have hxb := ih (n := n + 1) hx
        have hrec := mersenneTail_eq_weight_add n
        have hw := mersenneWeight_pos (n := n + 1) (by omega)
        exact ⟨hxb.1, by linarith [hxb.2]⟩
      · rcases hx with ⟨y, hy, rfl⟩
        have hyb := ih (n := n + 1) hy
        have hrec := mersenneTail_eq_weight_add n
        have hw := mersenneWeight_pos (n := n + 1) (by omega)
        exact ⟨by linarith [hyb.1], by linarith [hyb.2]⟩

theorem isCompact_mersenneCylinderStageFrom (n depth : ℕ) :
    IsCompact (mersenneCylinderStageFrom n depth) := by
  induction depth generalizing n with
  | zero => simpa [mersenneCylinderStageFrom] using
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (mersenneTail n)))
  | succ depth ih =>
      rw [mersenneCylinderStageFrom]
      exact (ih (n := n + 1)).union
        ((ih (n := n + 1)).image (continuous_const.add continuous_id))

theorem isClosed_mersenneCylinderStageFrom (n depth : ℕ) :
    IsClosed (mersenneCylinderStageFrom n depth) :=
  (isCompact_mersenneCylinderStageFrom n depth).isClosed

theorem measurableSet_mersenneCylinderStageFrom (n depth : ℕ) :
    MeasurableSet (mersenneCylinderStageFrom n depth) :=
  (isClosed_mersenneCylinderStageFrom n depth).measurableSet

/-- Strict superincreasingness separates the two children at every cylinder
split. -/
theorem disjoint_mersenneCylinderStageFrom_split (n depth : ℕ) :
    Disjoint (mersenneCylinderStageFrom (n + 1) depth)
      ((fun x : ℝ => mersenneWeight (n + 1) + x) ''
        mersenneCylinderStageFrom (n + 1) depth) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rcases hx' with ⟨y, hy, rfl⟩
  have hxb := mersenneCylinderStageFrom_subset_Icc (n + 1) depth hx
  have hyb := mersenneCylinderStageFrom_subset_Icc (n + 1) depth hy
  have hgap := mersenneTail_lt_weight (n := n + 1) (by omega)
  linarith [hxb.2, hyb.1]

/-- Increasing the retained depth shrinks the cylinder enclosure. -/
theorem mersenneCylinderStageFrom_succ_subset (n depth : ℕ) :
    mersenneCylinderStageFrom n (depth + 1)
      ⊆ mersenneCylinderStageFrom n depth := by
  induction depth generalizing n with
  | zero => exact mersenneCylinderStageFrom_subset_Icc n 1
  | succ depth ih =>
      intro x hx
      simp only [mersenneCylinderStageFrom, Set.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ih (n := n + 1) hx)
      · rcases hx with ⟨y, hy, rfl⟩
        exact Or.inr ⟨y, ih (n := n + 1) hy, rfl⟩

theorem antitone_mersenneCylinderStageFrom (n : ℕ) :
    Antitone (mersenneCylinderStageFrom n) :=
  antitone_nat_of_succ_le (mersenneCylinderStageFrom_succ_subset n)

theorem antitone_mersenneCylinderStage : Antitone mersenneCylinderStage := by
  intro a b hab
  exact antitone_mersenneCylinderStageFrom 0 hab

@[simp] theorem positiveMersenneSupportSuffix_zero_index (A : Set ℕ) :
    positiveMersenneSupportSuffix A 0 = positiveMersenneSupportValue A := by
  unfold positiveMersenneSupportSuffix positiveMersenneSupportValue
  congr 1
  funext k
  congr 2
  omega

/-- Removing the current exponent shifts a coded suffix by one place. -/
theorem positiveMersenneSupportSuffix_diff_current (A : Set ℕ) (n : ℕ) :
    positiveMersenneSupportSuffix (A \ {n + 1}) n
      = positiveMersenneSupportSuffix A (n + 1) := by
  rw [positiveMersenneSupportSuffix_eq_indicator_add]
  have hnot : n + 1 ∉ A \ {n + 1} := by simp
  rw [Set.indicator_of_notMem hnot, zero_add]
  unfold positiveMersenneSupportSuffix
  apply tsum_congr
  intro k
  have hne : n + 1 + k ≠ n := by omega
  by_cases hk : n + 1 + k + 1 ∈ A <;> simp [hk, hne]

/-- Inserting the current exponent splits off exactly its weight. -/
theorem positiveMersenneSupportSuffix_insert_current (A : Set ℕ) (n : ℕ) :
    positiveMersenneSupportSuffix (insert (n + 1) A) n
      = mersenneWeight (n + 1) + positiveMersenneSupportSuffix A (n + 1) := by
  rw [positiveMersenneSupportSuffix_eq_indicator_add,
    Set.indicator_of_mem (Set.mem_insert (n + 1) A)]
  congr 1
  unfold positiveMersenneSupportSuffix
  apply tsum_congr
  intro k
  have hne : n + 1 + k ≠ n := by omega
  by_cases hk : n + 1 + k + 1 ∈ A <;> simp [hk, hne]

/-- Every coded suffix belongs to every corresponding finite-cylinder
enclosure. -/
theorem positiveMersenneSupportSuffix_mem_cylinderStageFrom
    (A : Set ℕ) (n depth : ℕ) :
    positiveMersenneSupportSuffix A n ∈ mersenneCylinderStageFrom n depth := by
  induction depth generalizing n with
  | zero =>
      exact ⟨positiveMersenneSupportSuffix_nonneg A n,
        positiveMersenneSupportSuffix_le_tail A n⟩
  | succ depth ih =>
      simp only [mersenneCylinderStageFrom, Set.mem_union]
      by_cases hA : n + 1 ∈ A
      · rw [positiveMersenneSupportSuffix_eq_indicator_add,
          Set.indicator_of_mem hA]
        exact Or.inr ⟨positiveMersenneSupportSuffix A (n + 1),
          ih (n := n + 1), rfl⟩
      · rw [positiveMersenneSupportSuffix_eq_indicator_add,
          Set.indicator_of_notMem hA, zero_add]
        exact Or.inl (ih (n := n + 1))

theorem mersenneAchievementSet_subset_cylinderStage (depth : ℕ) :
    mersenneAchievementSet ⊆ mersenneCylinderStage depth := by
  rintro x ⟨A, hA0, rfl⟩
  simpa [mersenneCylinderStage] using
    positiveMersenneSupportSuffix_mem_cylinderStageFrom A 0 depth

/-- Every point of a finite-cylinder stage is within the unresolved tail of
an actual normalized support value. -/
theorem exists_normalized_support_near_of_mem_cylinderStageFrom
    {x : ℝ} {n depth : ℕ} (hx : x ∈ mersenneCylinderStageFrom n depth) :
    ∃ A : Set ℕ, 0 ∉ A ∧
      dist x (positiveMersenneSupportSuffix A n) ≤ mersenneTail (n + depth) := by
  induction depth generalizing n x with
  | zero =>
      have hxb : x ∈ Set.Icc 0 (mersenneTail n) := by
        simpa [mersenneCylinderStageFrom] using hx
      refine ⟨∅, by simp, ?_⟩
      simpa [positiveMersenneSupportSuffix, Real.dist_eq,
        abs_of_nonneg hxb.1] using hxb.2
  | succ depth ih =>
      simp only [mersenneCylinderStageFrom, Set.mem_union] at hx
      rcases hx with hx | hx
      · rcases ih (n := n + 1) hx with ⟨A, hA0, hdist⟩
        refine ⟨A \ {n + 1}, by simpa using hA0, ?_⟩
        rw [positiveMersenneSupportSuffix_diff_current]
        have hidx : n + 1 + depth = n + (depth + 1) := by omega
        simpa only [hidx] using hdist
      · rcases hx with ⟨y, hy, rfl⟩
        rcases ih (n := n + 1) hy with ⟨A, hA0, hdist⟩
        refine ⟨insert (n + 1) A, ?_, ?_⟩
        · simpa using hA0
        · rw [positiveMersenneSupportSuffix_insert_current]
          have hidx : n + 1 + depth = n + (depth + 1) := by omega
          simpa only [dist_add_left, hidx] using hdist

/-- The achievement set is exactly the decreasing intersection of its finite
cylinder enclosures. -/
theorem mersenneAchievementSet_eq_iInter_cylinderStage :
    mersenneAchievementSet = ⋂ depth : ℕ, mersenneCylinderStage depth := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_iInter.2 fun depth =>
      mersenneAchievementSet_subset_cylinderStage depth hx
  · intro x hx
    have hstage : ∀ depth : ℕ, x ∈ mersenneCylinderStage depth :=
      Set.mem_iInter.1 hx
    have happ (depth : ℕ) :
        ∃ A : Set ℕ, 0 ∉ A ∧
          dist x (positiveMersenneSupportValue A) ≤ mersenneTail depth := by
      simpa [mersenneCylinderStage] using
        (exists_normalized_support_near_of_mem_cylinderStageFrom
          (n := 0) (depth := depth) (hstage depth))
    let A : ℕ → Set ℕ := fun depth => Classical.choose (happ depth)
    let y : ℕ → ℝ := fun depth => positiveMersenneSupportValue (A depth)
    have hspec (depth : ℕ) := Classical.choose_spec (happ depth)
    have hy_mem (depth : ℕ) : y depth ∈ mersenneAchievementSet := by
      exact ⟨A depth, (hspec depth).1, rfl⟩
    have hdist_le (depth : ℕ) : dist (y depth) x ≤ mersenneTail depth := by
      simpa [y, dist_comm] using (hspec depth).2
    have hdist_tendsto : Tendsto (fun depth => dist (y depth) x)
        atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_mersenneTail_zero (fun _ => dist_nonneg) hdist_le
    have hy_tendsto : Tendsto y atTop (nhds x) :=
      tendsto_iff_dist_tendsto_zero.2 hdist_tendsto
    exact isClosed_mersenneAchievementSet.mem_of_tendsto hy_tendsto
      (Filter.Eventually.of_forall hy_mem)

/-! ## Exact cylinder measures and the measure-one limit -/

/-- A depth-`d` tail stage is a disjoint union of `2^d` intervals, each of
length `mersenneTail (n+d)`. -/
theorem volume_mersenneCylinderStageFrom (n depth : ℕ) :
    volume (mersenneCylinderStageFrom n depth)
      = (2 : ℝ≥0∞) ^ depth * ENNReal.ofReal (mersenneTail (n + depth)) := by
  induction depth generalizing n with
  | zero =>
      rw [mersenneCylinderStageFrom, Real.volume_Icc]
      simp
  | succ depth ih =>
      rw [mersenneCylinderStageFrom]
      have hmeas : MeasurableSet
          ((fun x : ℝ => mersenneWeight (n + 1) + x) ''
            mersenneCylinderStageFrom (n + 1) depth) :=
        ((isCompact_mersenneCylinderStageFrom (n + 1) depth).image
          (continuous_const.add continuous_id)).isClosed.measurableSet
      rw [measure_union (disjoint_mersenneCylinderStageFrom_split n depth) hmeas]
      rw [Set.image_add_left, measure_preimage_add, ih]
      calc
        (2 : ℝ≥0∞) ^ depth * ENNReal.ofReal (mersenneTail (n + 1 + depth))
              + (2 : ℝ≥0∞) ^ depth * ENNReal.ofReal (mersenneTail (n + 1 + depth))
            = 2 * ((2 : ℝ≥0∞) ^ depth *
                ENNReal.ofReal (mersenneTail (n + 1 + depth))) := by ring
        _ = (2 : ℝ≥0∞) ^ (depth + 1) *
              ENNReal.ofReal (mersenneTail (n + (depth + 1))) := by
          rw [pow_succ]
          rw [show n + 1 + depth = n + (depth + 1) by omega]
          ring

theorem volume_mersenneCylinderStage (depth : ℕ) :
    volume (mersenneCylinderStage depth)
      = (2 : ℝ≥0∞) ^ depth * ENNReal.ofReal (mersenneTail depth) := by
  simpa [mersenneCylinderStage] using volume_mersenneCylinderStageFrom 0 depth

/-- The higher-channel part of the scaled unresolved tail vanishes. -/
theorem tendsto_two_pow_mul_mersenneWeightRemainderTail_zero :
    Tendsto
      (fun n : ℕ => (2 : ℝ) ^ n * mersenneWeightRemainderTail n)
      atTop (nhds 0) := by
  have hup0 : Tendsto (fun n : ℕ => ((1 : ℝ) / 4) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 : ℝ) / 4 < 1)
  have hup : Tendsto (fun n : ℕ => (2 / 7 : ℝ) * ((1 : ℝ) / 4) ^ n)
      atTop (nhds 0) := by
    simpa using hup0.const_mul (2 / 7 : ℝ)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      mul_nonneg (pow_nonneg (by norm_num) n)
        (mersenneWeightRemainderTail_nonneg n)
  · exact Filter.Eventually.of_forall fun n => by
      calc
        (2 : ℝ) ^ n * mersenneWeightRemainderTail n
            ≤ (2 : ℝ) ^ n *
                ((2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n) :=
              mul_le_mul_of_nonneg_left (mersenneWeightRemainderTail_le n)
                (pow_nonneg (by norm_num) n)
        _ = (2 / 7 : ℝ) * ((1 : ℝ) / 4) ^ n := by
              calc
                (2 : ℝ) ^ n * ((2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n)
                    = (2 / 7 : ℝ) *
                        ((2 : ℝ) ^ n * ((1 : ℝ) / 8) ^ n) := by ring
                _ = (2 / 7 : ℝ) * ((1 : ℝ) / 4) ^ n := by
                      rw [← mul_pow]
                      norm_num
  · exact hup

/-- The total length of the level-`n` cylinder cover tends to one. -/
theorem tendsto_two_pow_mul_mersenneTail_one :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ n * mersenneTail n)
      atTop (nhds 1) := by
  have hhalf : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num) (by norm_num)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hlim :=
    (hone.add (hhalf.const_mul (1 / 3 : ℝ))).add
      tendsto_two_pow_mul_mersenneWeightRemainderTail_zero
  convert hlim using 1
  · funext n
    rw [mersenneTail_eq_two_channels_add_remainderTail]
    have hfirst : (2 : ℝ) ^ n * ((1 : ℝ) / 2) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    have hsecond : (2 : ℝ) ^ n * ((1 : ℝ) / 4) ^ n =
        ((1 : ℝ) / 2) ^ n := by
      rw [← mul_pow]
      norm_num
    rw [mul_add, mul_add, hfirst]
    rw [show (2 : ℝ) ^ n *
        ((1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n) =
          (1 / 3 : ℝ) * ((1 : ℝ) / 2) ^ n by
      calc
        (2 : ℝ) ^ n * ((1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n)
            = (1 / 3 : ℝ) *
                ((2 : ℝ) ^ n * ((1 : ℝ) / 4) ^ n) := by ring
        _ = (1 / 3 : ℝ) * ((1 : ℝ) / 2) ^ n := by rw [hsecond]]
  · norm_num

theorem tendsto_volume_mersenneCylinderStage_one :
    Tendsto (fun depth : ℕ => volume (mersenneCylinderStage depth))
      atTop (nhds 1) := by
  have hreal := ENNReal.tendsto_ofReal tendsto_two_pow_mul_mersenneTail_one
  have heq : (fun depth : ℕ => volume (mersenneCylinderStage depth)) =
      (fun depth : ℕ =>
        ENNReal.ofReal ((2 : ℝ) ^ depth * mersenneTail depth)) := by
    funext depth
    rw [volume_mersenneCylinderStage,
      ENNReal.ofReal_mul (pow_nonneg (by norm_num) depth),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [heq]
  simpa using hreal

/-- **measure one.**  Continuity from above transfers the exact
cylinder measures to their decreasing intersection. -/
theorem volume_mersenneAchievementSet : volume mersenneAchievementSet = 1 := by
  have hfinite : ∃ depth : ℕ,
      volume (mersenneCylinderStage depth) ≠ ∞ := by
    refine ⟨0, ?_⟩
    rw [volume_mersenneCylinderStage]
    simp
  have hcont := tendsto_measure_iInter_atTop (μ := volume)
    (fun depth => (measurableSet_mersenneCylinderStageFrom 0 depth).nullMeasurableSet)
    antitone_mersenneCylinderStage hfinite
  have hcont' : Tendsto
      (fun depth : ℕ => volume (mersenneCylinderStage depth))
      atTop (nhds (volume mersenneAchievementSet)) := by
    rw [mersenneAchievementSet_eq_iInter_cylinderStage]
    simpa [mersenneCylinderStage, Function.comp_def] using hcont
  exact tendsto_nhds_unique hcont' tendsto_volume_mersenneCylinderStage_one

/-! ## Exact greedy recurrences -/

/-- Real greedy residual after processing exponents `1, ..., n`. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

/-- Exact rational version of the greedy residual. -/
def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n

@[simp] theorem greedyMersenneRemainder_zero (x : ℝ) :
    greedyMersenneRemainder x 0 = x := rfl

@[simp] theorem greedyMersenneRemainderRat_zero (x : ℚ) :
    greedyMersenneRemainderRat x 0 = x := rfl

theorem greedyMersenneRemainder_succ (x : ℝ) (n : ℕ) :
    greedyMersenneRemainder x (n + 1)
      = if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
          greedyMersenneRemainder x n - mersenneWeight (n + 1)
        else greedyMersenneRemainder x n := rfl

theorem greedyMersenneRemainderRat_succ (x : ℚ) (n : ℕ) :
    greedyMersenneRemainderRat x (n + 1)
      = if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
          greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
        else greedyMersenneRemainderRat x n := rfl

/-! ## Exact rational sliver coordinates

The sharp skip-branch analysis is most naturally expressed after doubling
the usual dyadic excess coordinate.  This normalization is deliberate: it
makes the constant term in a selected-step update exactly `-2`, so the
limiting affine map is `ρ ↦ 4 * ρ - 2` and its fixed point is `2 / 3`.
The undoubled coordinate has constant term `-1` and fixed point `1 / 3`.
-/

/-- Undoubled excess above the dyadic point at scale `n`.  This is the
coordinate whose finite-level selected-step law has constant term `-1`.
Keeping it separate from the doubled coordinate prevents the two limiting
fixed points from being compared under different normalizations. -/
def mersenneSliverCoordinateRat (n : ℕ) (r : ℚ) : ℚ :=
  ((2 : ℚ) ^ n * r - 1) * ((2 : ℚ) ^ n - 1)

/-- Doubled excess above the dyadic point at scale `n`.  For an exact
rational remainder `r`, this is
`2 * (2^n * r - 1) * (2^n - 1)`. -/
def sharpMersenneSliverCoordinateRat (n : ℕ) (r : ℚ) : ℚ :=
  2 * ((2 : ℚ) ^ n * r - 1) * ((2 : ℚ) ^ n - 1)

theorem sharpMersenneSliverCoordinateRat_eq_two_mul (n : ℕ) (r : ℚ) :
    sharpMersenneSliverCoordinateRat n r =
      2 * mersenneSliverCoordinateRat n r := by
  simp [sharpMersenneSliverCoordinateRat, mersenneSliverCoordinateRat, mul_assoc]

/-- Exact selected-step law for the undoubled coordinate.  Its limiting map
is `ρ ↦ 4 * ρ - 1`, with limiting fixed point `1 / 3`; the `-2` and `2 / 3`
constants belong to `sharpMersenneSliverCoordinateRat`. -/
theorem mersenneSliverCoordinateRat_selected_step
    {n : ℕ} (hn : 0 < n) (r : ℚ) :
    mersenneSliverCoordinateRat (n + 1)
        (r - mersenneWeightRat (n + 1)) =
      (4 + 2 / ((2 : ℚ) ^ n - 1)) *
          mersenneSliverCoordinateRat n r - 1 := by
  have hpow : ((2 : ℚ) ^ n - 1) ≠ 0 := by
    have hlt : (1 : ℚ) < 2 ^ n := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
    linarith
  have hweight : ((2 : ℚ) ^ (n + 1) - 1) ≠ 0 := by
    have hlt : (1 : ℚ) < 2 ^ (n + 1) :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  unfold mersenneSliverCoordinateRat mersenneWeightRat
  field_simp [hpow, hweight]
  ring

/-- Exact finite-level selected-step law for the doubled sliver coordinate.
The final term is the complete finite-level correction to the limiting map
`ρ ↦ 4 * ρ - 2`; no asymptotic estimate is used here. -/
theorem sharpMersenneSliverCoordinateRat_selected_step
    {n : ℕ} (hn : 0 < n) (r : ℚ) :
    sharpMersenneSliverCoordinateRat (n + 1)
        (r - mersenneWeightRat (n + 1)) =
      4 * sharpMersenneSliverCoordinateRat n r - 2 +
        2 * sharpMersenneSliverCoordinateRat n r /
          ((2 : ℚ) ^ n - 1) := by
  have hpow : ((2 : ℚ) ^ n - 1) ≠ 0 := by
    have hlt : (1 : ℚ) < 2 ^ n := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
    linarith
  have hweight : ((2 : ℚ) ^ (n + 1) - 1) ≠ 0 := by
    have hlt : (1 : ℚ) < 2 ^ (n + 1) :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  unfold sharpMersenneSliverCoordinateRat mersenneWeightRat
  field_simp [hpow, hweight]
  ring

/-- Greedy subtraction preserves nonnegativity. -/
theorem greedyMersenneRemainder_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ greedyMersenneRemainder x n := by
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [greedyMersenneRemainder_succ]
      split_ifs with h
      · linarith
      · exact ih

/-- Rational and real greedy execution agree exactly under casting. -/
@[simp] theorem cast_greedyMersenneRemainderRat (x : ℚ) (n : ℕ) :
    ((greedyMersenneRemainderRat x n : ℚ) : ℝ)
      = greedyMersenneRemainder (x : ℝ) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [greedyMersenneRemainderRat_succ, greedyMersenneRemainder_succ]
      by_cases h : mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n
      · have h' : mersenneWeight (n + 1)
            ≤ greedyMersenneRemainder (x : ℝ) n := by
          have hc : ((mersenneWeightRat (n + 1) : ℚ) : ℝ)
              ≤ ((greedyMersenneRemainderRat x n : ℚ) : ℝ) := by
            exact_mod_cast h
          rw [← ih]
          simpa using hc
        rw [if_pos h, if_pos h']
        push_cast
        rw [cast_mersenneWeightRat, ih]
      · have h' : ¬ mersenneWeight (n + 1)
            ≤ greedyMersenneRemainder (x : ℝ) n := by
          intro hreal
          apply h
          rw [← ih] at hreal
          have hc : ((mersenneWeightRat (n + 1) : ℚ) : ℝ)
              ≤ ((greedyMersenneRemainderRat x n : ℚ) : ℝ) := by
            simpa using hreal
          exact_mod_cast hc
        rw [if_neg h, if_neg h', ih]

/-! ## Skipped-branch cap transport -/

/-- The first geometric channel of the Mersenne tail. -/
noncomputable def halfDyadicCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n

/-- The first two geometric channels of the Mersenne tail.  This cap is
strictly weaker than the dyadic cap while still lying below the full tail. -/
noncomputable def halfTwoChannelCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
    + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n

/-- If selected greedy branches transport a cap and skipped branches satisfy
the next cap directly, then the cap holds at every level.  This isolates the
only branch on which a channel-cap proof has a genuine arithmetic burden. -/
theorem greedyMersenneRemainder_le_cap_of_skipBarrier
    (c : ℕ → ℝ)
    (hbase : greedyMersenneRemainder (1 / 2 : ℝ) 0 ≤ c 0)
    (hselected : ∀ n : ℕ,
      c n - mersenneWeight (n + 1) ≤ c (n + 1))
    (hskipped : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n ≤ c (n + 1)) :
    ∀ n : ℕ, greedyMersenneRemainder (1 / 2 : ℝ) n ≤ c n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
      rw [greedyMersenneRemainder_succ]
      by_cases htake :
          mersenneWeight (n + 1) ≤ greedyMersenneRemainder (1 / 2 : ℝ) n
      · rw [if_pos htake]
        exact (sub_le_sub_right ih _).trans (hselected n)
      · rw [if_neg htake]
        exact hskipped n htake

/-- The one-channel cap is contained in the two-channel cap. -/
theorem halfDyadicCap_le_halfTwoChannelCap (n : ℕ) :
    halfDyadicCap n ≤ halfTwoChannelCap n := by
  unfold halfDyadicCap halfTwoChannelCap
  have hquarter : 0 ≤ (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n := by positivity
  linarith

/-- The two-channel cap is a lower enclosure of the exact Mersenne tail. -/
theorem halfTwoChannelCap_le_mersenneTail (n : ℕ) :
    halfTwoChannelCap n ≤ mersenneTail n := by
  rw [mersenneTail_eq_two_channels_add_remainderTail]
  unfold halfTwoChannelCap
  exact le_add_of_nonneg_right (mersenneWeightRemainderTail_nonneg n)

/-- The two-channel truncation is strictly below the true tail.  The omitted
higher channels are the exact positive gap, rather than a factor-two margin
against a `2 / 3` sliver threshold. -/
theorem halfTwoChannelCap_lt_mersenneTail (n : ℕ) :
    halfTwoChannelCap n < mersenneTail n := by
  rw [mersenneTail_eq_two_channels_add_remainderTail]
  unfold halfTwoChannelCap
  have hrem := mersenneWeightRemainderTail_pos n
  linarith

/-- A selected greedy branch transports the dyadic cap strictly. -/
theorem halfDyadicCap_selected_strict (n : ℕ) :
    halfDyadicCap n - mersenneWeight (n + 1)
      < halfDyadicCap (n + 1) := by
  rw [mersenneWeight_eq_two_channels_add_remainder (by omega)]
  unfold halfDyadicCap
  simp only [pow_succ]
  have hquarter : 0 < ((1 : ℝ) / 4) ^ n := by positivity
  have hrem := mersenneWeightRemainder_nonneg (n := n + 1) (by omega)
  nlinarith

/-- A selected greedy branch transports the two-channel cap strictly. -/
theorem halfTwoChannelCap_selected_strict (n : ℕ) :
    halfTwoChannelCap n - mersenneWeight (n + 1)
      < halfTwoChannelCap (n + 1) := by
  rw [mersenneWeight_eq_two_channels_add_remainder (by omega)]
  unfold halfTwoChannelCap
  simp only [pow_succ]
  have hrem := mersenneWeightRemainder_pos (n := n + 1) (by omega)
  nlinarith

/-- Non-strict transport form consumed by the generic skip barrier. -/
theorem halfDyadicCap_selected (n : ℕ) :
    halfDyadicCap n - mersenneWeight (n + 1)
      ≤ halfDyadicCap (n + 1) :=
  (halfDyadicCap_selected_strict n).le

/-- Non-strict transport form consumed by the generic skip barrier. -/
theorem halfTwoChannelCap_selected (n : ℕ) :
    halfTwoChannelCap n - mersenneWeight (n + 1)
      ≤ halfTwoChannelCap (n + 1) :=
  (halfTwoChannelCap_selected_strict n).le

/-- The set of positive exponents selected by the real greedy recursion. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

/-- The positive exponents omitted by the real greedy recursion. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

@[simp] theorem zero_not_mem_greedyMersenneSupport (x : ℝ) :
    0 ∉ greedyMersenneSupport x := by
  simp [greedyMersenneSupport]

@[simp] theorem zero_not_mem_greedyMersenneSkippedSupport (x : ℝ) :
    0 ∉ greedyMersenneSkippedSupport x := by
  simp [greedyMersenneSkippedSupport]

@[simp] theorem succ_mem_greedyMersenneSupport_iff (x : ℝ) (n : ℕ) :
    n + 1 ∈ greedyMersenneSupport x
      ↔ mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n := by
  simp [greedyMersenneSupport]

@[simp] theorem succ_mem_greedyMersenneSkippedSupport_iff (x : ℝ) (n : ℕ) :
    n + 1 ∈ greedyMersenneSkippedSupport x
      ↔ ¬ mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n := by
  simp [greedyMersenneSkippedSupport]

/-- Exact finite-prefix identity for the real greedy recursion. -/
theorem greedyMersenne_prefix_add_remainder (x : ℝ) (n : ℕ) :
    x = (∑ k ∈ Finset.range n,
          Set.indicator (greedyMersenneSupport x) mersenneWeight (k + 1))
        + greedyMersenneRemainder x n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n
      · rw [Set.indicator_of_mem ((succ_mem_greedyMersenneSupport_iff x n).2 h),
          greedyMersenneRemainder_succ, if_pos h]
        linarith
      · rw [Set.indicator_of_notMem (by
            simpa only [succ_mem_greedyMersenneSupport_iff] using h),
          greedyMersenneRemainder_succ, if_neg h, add_zero]
        exact ih

/-! ## Recovery, survival, and uniqueness -/

/-- On a genuine support value, the greedy residual is exactly the unprocessed
support suffix. -/
theorem greedyMersenneRemainder_supportValue (A : Set ℕ) (n : ℕ) :
    greedyMersenneRemainder (positiveMersenneSupportValue A) n
      = positiveMersenneSupportSuffix A n := by
  induction n with
  | zero => simp [positiveMersenneSupportValue, positiveMersenneSupportSuffix]
  | succ n ih =>
      rw [greedyMersenneRemainder_succ, ih,
        positiveMersenneSupportSuffix_eq_indicator_add]
      by_cases hA : n + 1 ∈ A
      · rw [Set.indicator_of_mem hA]
        have hnonneg := positiveMersenneSupportSuffix_nonneg A (n + 1)
        have htake : mersenneWeight (n + 1)
            ≤ mersenneWeight (n + 1) + positiveMersenneSupportSuffix A (n + 1) := by
          linarith
        rw [if_pos htake]
        ring
      · rw [Set.indicator_of_notMem hA, zero_add]
        have hsuffix := positiveMersenneSupportSuffix_le_tail A (n + 1)
        have htail := mersenneTail_lt_weight (n := n + 1) (by omega)
        have hskip : ¬ mersenneWeight (n + 1)
            ≤ positiveMersenneSupportSuffix A (n + 1) := by
          linarith
        rw [if_neg hskip]

/-- Greedy selection recovers every positive bit of a representing support. -/
theorem succ_mem_greedySupport_supportValue_iff (A : Set ℕ) (n : ℕ) :
    n + 1 ∈ greedyMersenneSupport (positiveMersenneSupportValue A)
      ↔ n + 1 ∈ A := by
  rw [succ_mem_greedyMersenneSupport_iff,
    greedyMersenneRemainder_supportValue]
  constructor
  · intro htake
    by_contra hA
    have hsuffix := positiveMersenneSupportSuffix_le_tail A (n + 1)
    have htail := mersenneTail_lt_weight (n := n + 1) (by omega)
    rw [positiveMersenneSupportSuffix_eq_indicator_add,
      Set.indicator_of_notMem hA, zero_add] at htake
    linarith
  · intro hA
    rw [positiveMersenneSupportSuffix_eq_indicator_add,
      Set.indicator_of_mem hA]
    have hnonneg := positiveMersenneSupportSuffix_nonneg A (n + 1)
    linarith

/-- A normalized support is recovered exactly, including the forced-zero bit
at exponent zero. -/
theorem greedySupport_supportValue_eq (A : Set ℕ) (hA0 : 0 ∉ A) :
    greedyMersenneSupport (positiveMersenneSupportValue A) = A := by
  ext m
  rcases m with _ | n
  · simp [hA0]
  · simpa [Nat.succ_eq_add_one] using succ_mem_greedySupport_supportValue_iff A n

/-- Every support value is nonnegative. -/
theorem positiveMersenneSupportValue_nonneg (A : Set ℕ) :
    0 ≤ positiveMersenneSupportValue A := by
  rw [positiveMersenneSupportValue_eq_prefix_add_suffix A 0]
  simpa using positiveMersenneSupportSuffix_nonneg A 0

/-- Membership implies the exact all-level upper-tail survival inequalities. -/
theorem greedy_survives_of_mem_mersenneAchievementSet {x : ℝ}
    (hx : x ∈ mersenneAchievementSet) :
    0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  rcases hx with ⟨A, hA0, rfl⟩
  refine ⟨positiveMersenneSupportValue_nonneg A, fun n => ?_⟩
  rw [greedyMersenneRemainder_supportValue]
  exact positiveMersenneSupportSuffix_le_tail A n

/-- If all greedy residuals stay below the remaining mass, they converge to
zero.  The nonnegativity guard excludes the false negative-target variant. -/
theorem tendsto_greedyMersenneRemainder_zero {x : ℝ} (hx : 0 ≤ x)
    (hsurvive : ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) :
    Tendsto (greedyMersenneRemainder x) atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tendsto_mersenneTail_zero
    (Filter.Eventually.of_forall fun n => greedyMersenneRemainder_nonneg hx n)
    (Filter.Eventually.of_forall hsurvive)

/-- All-level survival constructs a genuine normalized support code. -/
theorem mem_mersenneAchievementSet_of_greedy_survival {x : ℝ} (hx : 0 ≤ x)
    (hsurvive : ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) :
    x ∈ mersenneAchievementSet := by
  let A := greedyMersenneSupport x
  have hsum := summable_positiveMersenneSupportIndicator A
  have htoSum : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        Set.indicator A mersenneWeight (k + 1)) atTop
      (nhds (positiveMersenneSupportValue A)) := by
    simpa [positiveMersenneSupportValue] using hsum.tendsto_sum_tsum_nat
  have hrem := tendsto_greedyMersenneRemainder_zero hx hsurvive
  have htoX : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        Set.indicator A mersenneWeight (k + 1)) atTop (nhds x) := by
    have hsub : Tendsto (fun n : ℕ => x - greedyMersenneRemainder x n)
        atTop (nhds (x - 0)) := tendsto_const_nhds.sub hrem
    convert hsub using 1
    · funext n
      have hprefix := greedyMersenne_prefix_add_remainder x n
      change (∑ k ∈ Finset.range n,
        Set.indicator (greedyMersenneSupport x) mersenneWeight (k + 1))
          = x - greedyMersenneRemainder x n
      linarith
    · simp
  have hvalue : positiveMersenneSupportValue A = x :=
    tendsto_nhds_unique htoSum htoX
  exact ⟨A, zero_not_mem_greedyMersenneSupport x, hvalue.symm⟩

/-- It is enough to establish the two-channel cap only when the actual greedy
orbit skips the next exponent.  Selected branches and the final membership
composition are discharged here. -/
theorem half_mem_mersenneAchievementSet_of_skipped_twoChannelCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ halfTwoChannelCap (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  have hall : ∀ n : ℕ,
      greedyMersenneRemainder (1 / 2 : ℝ) n ≤ halfTwoChannelCap n := by
    apply greedyMersenneRemainder_le_cap_of_skipBarrier
    · norm_num [halfTwoChannelCap]
    · exact halfTwoChannelCap_selected
    · exact hskip
  apply mem_mersenneAchievementSet_of_greedy_survival (by norm_num)
  intro n
  exact (hall n).trans (halfTwoChannelCap_le_mersenneTail n)

/-- The stronger one-channel skipped-branch obligation is therefore also a
sufficient membership criterion. -/
theorem half_mem_mersenneAchievementSet_of_skipped_dyadicCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ halfDyadicCap (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_skipped_twoChannelCap
  intro n hskipped
  exact (hskip n hskipped).trans (halfDyadicCap_le_halfTwoChannelCap (n + 1))

/-- **Greedy membership criterion.**  A real target belongs to the Mersenne
achievement set exactly when it is nonnegative and every residual is at most
the full remaining tail. -/
theorem mem_mersenneAchievementSet_iff_greedy_survival (x : ℝ) :
    x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  constructor
  · exact greedy_survives_of_mem_mersenneAchievementSet
  · rintro ⟨hx, hsurvive⟩
    exact mem_mersenneAchievementSet_of_greedy_survival hx hsurvive

/-! ## Fatal-state dichotomy -/

/-- A greedy state is fatal when its residual is already larger than all
remaining Mersenne mass. -/
def GreedyMersenneFatalAt (x : ℝ) (n : ℕ) : Prop :=
  mersenneTail n < greedyMersenneRemainder x n

theorem greedyMersenneFatalAt_iff_not_survives (x : ℝ) (n : ℕ) :
    GreedyMersenneFatalAt x n ↔
      ¬ greedyMersenneRemainder x n ≤ mersenneTail n := by
  simp [GreedyMersenneFatalAt]

/-- Fatality is absorbing: the next exponent is selected and the next state
is fatal again. -/
theorem greedyMersenneFatalAt_succ {x : ℝ} {n : ℕ}
    (hfatal : GreedyMersenneFatalAt x n) :
    mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n ∧
      GreedyMersenneFatalAt x (n + 1) := by
  have htail := mersenneTail_eq_weight_add n
  have htailNonneg := mersenneTail_nonneg (n + 1)
  have htake :
      mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n := by
    unfold GreedyMersenneFatalAt at hfatal
    linarith
  refine ⟨htake, ?_⟩
  unfold GreedyMersenneFatalAt at hfatal ⊢
  rw [greedyMersenneRemainder_succ, if_pos htake]
  linarith

/-- Once a fatal state is reached, every later state is fatal. -/
theorem greedyMersenneFatalAt_add {x : ℝ} {n : ℕ}
    (hfatal : GreedyMersenneFatalAt x n) (k : ℕ) :
    GreedyMersenneFatalAt x (n + k) := by
  induction k with
  | zero => simpa using hfatal
  | succ k ih =>
      simpa [Nat.add_assoc] using (greedyMersenneFatalAt_succ ih).2

/-- Every exponent after a fatal state is selected by the greedy recursion. -/
theorem mem_greedyMersenneSupport_of_fatalAt_add_succ
    {x : ℝ} {n : ℕ} (hfatal : GreedyMersenneFatalAt x n) (k : ℕ) :
    n + k + 1 ∈ greedyMersenneSupport x := by
  rw [succ_mem_greedyMersenneSupport_iff]
  exact (greedyMersenneFatalAt_succ
    (greedyMersenneFatalAt_add hfatal k)).1

/-- A fatal state leaves only finitely many omitted exponents. -/
theorem finite_greedyMersenneSkippedSupport_of_fatalAt
    {x : ℝ} {n : ℕ} (hfatal : GreedyMersenneFatalAt x n) :
    (greedyMersenneSkippedSupport x).Finite := by
  refine (Finset.finite_toSet (Finset.range (n + 1))).subset ?_
  intro m hm
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hnot
  have hge : n + 1 ≤ m := by omega
  have hselected := mem_greedyMersenneSupport_of_fatalAt_add_succ
    hfatal (m - (n + 1))
  have hmEq : n + (m - (n + 1)) + 1 = m := by omega
  exact hm.2 (hmEq ▸ hselected)

/-- Infinitely many omitted exponents rule out every fatal state and hence
force exact achievement-set membership. -/
theorem mem_mersenneAchievementSet_of_greedySkippedSupport_infinite
    {x : ℝ} (hx : 0 ≤ x)
    (hskips : (greedyMersenneSkippedSupport x).Infinite) :
    x ∈ mersenneAchievementSet := by
  apply (mem_mersenneAchievementSet_iff_greedy_survival x).2
  refine ⟨hx, fun n => ?_⟩
  by_contra hnot
  have hfatal : GreedyMersenneFatalAt x n :=
    (greedyMersenneFatalAt_iff_not_survives x n).2 hnot
  exact hskips (finite_greedyMersenneSkippedSupport_of_fatalAt hfatal)

/-- Infinitely many omitted exponents are exactly a cofinal supply of skipped
greedy branches.  This is the order-theoretic bridge from support cardinality
to an orbit statement at arbitrarily late ranks. -/
theorem greedyMersenneSkippedSupport_infinite_iff_cofinal_skips (x : ℝ) :
    (greedyMersenneSkippedSupport x).Infinite ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
        ¬ mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n := by
  constructor
  · intro hinfinite K
    obtain ⟨m, hm, hKm⟩ := hinfinite.exists_gt K
    have hm0 : m ≠ 0 := hm.1
    have hsucc : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)
    refine ⟨m - 1, by omega, ?_⟩
    apply (succ_mem_greedyMersenneSkippedSupport_iff x (m - 1)).mp
    simpa [hsucc] using hm
  · intro hcofinal
    apply Set.infinite_iff_exists_gt.mpr
    intro K
    obtain ⟨n, hKn, hskip⟩ := hcofinal K
    refine ⟨n + 1, (succ_mem_greedyMersenneSkippedSupport_iff x n).2 hskip, by omega⟩

/-- Strict superincreasingness makes normalized support coding injective. -/
theorem positiveMersenneSupportValue_injective_normalized
    {A B : Set ℕ} (hA0 : 0 ∉ A) (hB0 : 0 ∉ B)
    (hvalue : positiveMersenneSupportValue A = positiveMersenneSupportValue B) :
    A = B := by
  rw [← greedySupport_supportValue_eq A hA0,
    ← greedySupport_supportValue_eq B hB0, hvalue]

/-- The support coding through the existing #257 series is likewise unique
after the zero-bit normalization. -/
theorem erdosSupportSeries_two_injective_normalized
    {A B : Set ℕ} (hA0 : 0 ∉ A) (hB0 : 0 ∉ B)
    (hvalue : erdosSupportSeries 2 A = erdosSupportSeries 2 B) :
    A = B := by
  apply positiveMersenneSupportValue_injective_normalized hA0 hB0
  simpa only [positiveMersenneSupportValue_eq_erdosSupportSeries] using hvalue

/-! ## No isolated points -/

/-- Strict superincreasingness makes the binary coding injective. -/
theorem positiveMersenneDigitValue_injective :
    Function.Injective positiveMersenneDigitValue := by
  intro b c hbc
  have hsupp : mersenneDigitSupport b = mersenneDigitSupport c :=
    positiveMersenneSupportValue_injective_normalized
      (zero_not_mem_mersenneDigitSupport b)
      (zero_not_mem_mersenneDigitSupport c) (by
        rw [← positiveMersenneDigitValue_eq_supportValue,
          ← positiveMersenneDigitValue_eq_supportValue]
        exact hbc)
  funext k
  have hk : b k = 1 ↔ c k = 1 := by
    simpa only [succ_mem_mersenneDigitSupport_iff] using
      Set.ext_iff.mp hsupp (k + 1)
  by_cases hb1 : b k = 1
  · rw [hb1, hk.mp hb1]
  · have hb0 : b k = 0 := by
      by_contra hb0
      exact hb1 (Fin.eq_one_of_ne_zero (b k) hb0)
    have hc1 : c k ≠ 1 := fun hc1 => hb1 (hk.mpr hc1)
    have hc0 : c k = 0 := by
      by_contra hc0
      exact hc1 (Fin.eq_one_of_ne_zero (c k) hc0)
    rw [hb0, hc0]

/-- Flip one binary coordinate. -/
def mersenneBitFlip (a : Fin 2) : Fin 2 :=
  if a = 0 then 1 else 0

theorem mersenneBitFlip_ne (a : Fin 2) : mersenneBitFlip a ≠ a := by
  by_cases ha : a = 0
  · simp [mersenneBitFlip, ha]
  · have ha1 : a = 1 := Fin.eq_one_of_ne_zero a ha
    simp [mersenneBitFlip, ha1]

/-- Cantor binary space has no isolated points.  This is proved directly from
the finite-coordinate basis of the product topology. -/
theorem preperfect_univ_mersenneDigits :
    Preperfect (Set.univ : Set (ℕ → Fin 2)) := by
  rw [preperfect_iff_nhds]
  intro b _ U hU
  rw [nhds_pi, Filter.mem_pi'] at hU
  rcases hU with ⟨I, t, ht, hsub⟩
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset I
  let b' := Function.update b n (mersenneBitFlip (b n))
  refine ⟨b', ⟨?_, Set.mem_univ b'⟩, ?_⟩
  · apply hsub
    intro i hi
    have hin : i ≠ n := by
      intro h
      apply hn
      simpa [h] using hi
    change Function.update b n (mersenneBitFlip (b n)) i ∈ t i
    simpa [Function.update, hin] using mem_of_mem_nhds (ht i)
  · intro h
    have hnEq := congrFun h n
    change Function.update b n (mersenneBitFlip (b n)) n = b n at hnEq
    exact mersenneBitFlip_ne (b n) (by simpa [Function.update] using hnEq)

theorem preperfect_range_positiveMersenneDigitValue :
    Preperfect (Set.range positiveMersenneDigitValue) := by
  rw [preperfect_iff_nhds]
  rintro x ⟨b, rfl⟩ U hU
  have hpre := (preperfect_iff_nhds.mp preperfect_univ_mersenneDigits)
    b (Set.mem_univ b)
    (positiveMersenneDigitValue ⁻¹' U)
    (continuous_positiveMersenneDigitValue.continuousAt hU)
  rcases hpre with ⟨c, hc, hcb⟩
  refine ⟨positiveMersenneDigitValue c, ⟨hc.1, ⟨c, rfl⟩⟩, ?_⟩
  intro h
  exact hcb (positiveMersenneDigitValue_injective h)

/-- **perfection.**  The compact achievement set has no isolated
points. -/
theorem perfect_mersenneAchievementSet : Perfect mersenneAchievementSet := by
  refine ⟨isClosed_mersenneAchievementSet, ?_⟩
  rw [← range_positiveMersenneDigitValue_eq]
  exact preperfect_range_positiveMersenneDigitValue

/-! ## Total disconnectedness and nowhere density -/

theorem isEmbedding_positiveMersenneDigitValue :
    IsEmbedding positiveMersenneDigitValue := by
  have hclosed : IsClosedMap positiveMersenneDigitValue := by
    intro s hs
    exact (hs.isCompact.image continuous_positiveMersenneDigitValue).isClosed
  exact (IsClosedEmbedding.of_continuous_injective_isClosedMap
    continuous_positiveMersenneDigitValue
    positiveMersenneDigitValue_injective hclosed).isEmbedding

theorem isTotallyDisconnected_mersenneAchievementSet :
    IsTotallyDisconnected mersenneAchievementSet := by
  rw [← range_positiveMersenneDigitValue_eq]
  exact isEmbedding_positiveMersenneDigitValue.isTotallyDisconnected_range.mpr
    inferInstance

/-- **nowhere density.**  If the closed achievement set contained
an open ball, total disconnectedness would put a complementary point between
two points of that ball. -/
theorem isNowhereDense_mersenneAchievementSet :
    IsNowhereDense mersenneAchievementSet := by
  rw [isClosed_mersenneAchievementSet.isNowhereDense_iff]
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxK : x ∈ mersenneAchievementSet := interior_subset hx
  have hnhds : mersenneAchievementSet ∈ 𝓝 x :=
    mem_interior_iff_mem_nhds.mp hx
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hball⟩
  let y : ℝ := x + ε / 2
  have hxy : x < y := by dsimp [y]; linarith
  have hyball : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [y]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hyK : y ∈ mersenneAchievementSet := hball hyball
  rcases (isTotallyDisconnected_iff_lt.mp
      isTotallyDisconnected_mersenneAchievementSet)
      x hxK y hyK hxy with ⟨z, hzK, hxyz⟩
  have hxz : x < z := hxyz.1
  have hzy : z < y := hxyz.2
  apply hzK
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  rw [abs_of_pos (sub_pos.mpr hxz)]
  dsimp [y] at hzy
  linarith

/-! ## Finite exact-rational death certificates -/

/-- Split a tail after any finite lookahead. -/
theorem mersenneTail_eq_prefix_add_tail (n lookahead : ℕ) :
    mersenneTail n
      = (∑ k ∈ Finset.range lookahead, mersenneWeight (n + k + 1))
        + mersenneTail (n + lookahead) := by
  have h := (summable_mersenneTail n).sum_add_tsum_nat_add lookahead
  simpa [mersenneTail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm

/-- A finite rational upper enclosure for `mersenneTail n`.  The lookahead
parameter exposes a family of exact rational bounds without comparing an
infinite real tail numerically. -/
def mersenneTailUpperRat (n lookahead : ℕ) : ℚ :=
  (∑ k ∈ Finset.range lookahead, mersenneWeightRat (n + k + 1))
    + 2 * mersenneWeightRat (n + lookahead + 1)

/-- Every finite rational enclosure lies strictly above the actual tail. -/
theorem mersenneTail_lt_cast_tailUpperRat (n lookahead : ℕ) :
    mersenneTail n < ((mersenneTailUpperRat n lookahead : ℚ) : ℝ) := by
  rw [mersenneTail_eq_prefix_add_tail]
  have htail := mersenneTail_lt_two_mul_weight (n + lookahead)
  have hcast : ((mersenneTailUpperRat n lookahead : ℚ) : ℝ)
      = (∑ k ∈ Finset.range lookahead, mersenneWeight (n + k + 1))
        + 2 * mersenneWeight (n + lookahead + 1) := by
    unfold mersenneTailUpperRat
    push_cast
    simp
  rw [hcast]
  linarith

/-- Semantic greedy death: the current nonnegative residual is already larger
than all remaining available mass. -/
def GreedyMersenneDeath (x : ℝ) (level : ℕ) : Prop :=
  mersenneTail level < greedyMersenneRemainder x level

/-- Any semantic death level proves nonmembership. -/
theorem greedyMersenneDeath_not_mem {x : ℝ} {level : ℕ}
    (hdeath : GreedyMersenneDeath x level) :
    x ∉ mersenneAchievementSet := by
  intro hx
  have hsurvive := (mem_mersenneAchievementSet_iff_greedy_survival x).mp hx
  exact (not_lt_of_ge (hsurvive.2 level)) hdeath

/-- A decidable finite certificate: an exact rational upper enclosure is no
larger than the exact rational greedy residual. -/
def CertifiedGreedyMersenneDeath
    (x : ℚ) (level lookahead : ℕ) : Prop :=
  mersenneTailUpperRat level lookahead
    ≤ greedyMersenneRemainderRat x level

/-- Every finite exact-rational death certificate is sound. -/
theorem certifiedGreedyMersenneDeath_not_mem
    {x : ℚ} {level lookahead : ℕ}
    (hcert : CertifiedGreedyMersenneDeath x level lookahead) :
    ((x : ℚ) : ℝ) ∉ mersenneAchievementSet := by
  apply greedyMersenneDeath_not_mem
  unfold GreedyMersenneDeath
  have htail := mersenneTail_lt_cast_tailUpperRat level lookahead
  have hcertReal : ((mersenneTailUpperRat level lookahead : ℚ) : ℝ)
      ≤ ((greedyMersenneRemainderRat x level : ℚ) : ℝ) := by
    exact_mod_cast hcert
  rw [cast_greedyMersenneRemainderRat] at hcertReal
  exact lt_of_lt_of_le htail hcertReal

/-- **Exact level-one certificate.**  Greedy skips weight `w₁=1` at `3/4`,
leaving residual `3/4`; the zero-lookahead enclosure of the remaining tail is
`2*w₂ = 2/3`. -/
theorem three_fourths_certifiedGreedyMersenneDeath :
    CertifiedGreedyMersenneDeath (3 / 4 : ℚ) 1 0 := by
  norm_num [CertifiedGreedyMersenneDeath, mersenneTailUpperRat,
    greedyMersenneRemainderRat, mersenneWeightRat]

/-- Consequently `3/4` is not in the Mersenne achievement set. -/
theorem three_fourths_not_mem_mersenneAchievementSet :
    (3 / 4 : ℝ) ∉ mersenneAchievementSet := by
  simpa using certifiedGreedyMersenneDeath_not_mem
    (x := (3 / 4 : ℚ)) (level := 1) (lookahead := 0)
      three_fourths_certifiedGreedyMersenneDeath

/-! ## Rational greedy prefixes and computable digits -/

/-- Positive exponents selected through a finite exact-rational greedy run. -/
def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)

@[simp] theorem zero_not_mem_greedyMersennePrefixRat (x : ℚ) (n : ℕ) :
    0 ∉ greedyMersennePrefixRat x n := by
  classical
  simp [greedyMersennePrefixRat]

/-- Exact telescoping identity for a finite rational greedy run. -/
theorem greedyMersenneRat_prefix_add_remainder (x : ℚ) (n : ℕ) :
    x = (∑ k ∈ Finset.range n,
          if mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k then
            mersenneWeightRat (k + 1)
          else 0)
        + greedyMersenneRemainderRat x n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, greedyMersenneRemainderRat_succ]
      by_cases h : mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n
      · rw [if_pos h, if_pos h]
        linarith
      · rw [if_neg h, if_neg h, add_zero]
        exact ih

/-- The finite prefix selected by the rational greedy run is exactly an
instance of the existing audited finite Erdős sum. -/
theorem finiteErdosSum_greedyMersennePrefixRat (x : ℚ) (n : ℕ) :
    finiteErdosSum (greedyMersennePrefixRat x n) 2
      = ∑ k ∈ Finset.range n,
          if mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k then
            mersenneWeightRat (k + 1)
          else 0 := by
  classical
  unfold finiteErdosSum greedyMersennePrefixRat
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    rfl
  · exact Set.injOn_of_injective (by
      intro a b hab
      exact Nat.add_right_cancel hab)

/-- Exact interface to the finite denominator/noncollapse kernel: the rational
greedy residual is the target minus an audited `finiteErdosSum`. -/
theorem greedyMersenneRemainderRat_eq_sub_finiteErdosSum
    (x : ℚ) (n : ℕ) :
    greedyMersenneRemainderRat x n
      = x - finiteErdosSum (greedyMersennePrefixRat x n) 2 := by
  have hprefix := greedyMersenneRat_prefix_add_remainder x n
  rw [finiteErdosSum_greedyMersennePrefixRat]
  linarith

/-- A rational comparison decides exactly the same greedy bit as the real
comparison after casting. -/
theorem rational_greedy_take_iff_real (x : ℚ) (n : ℕ) :
    mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n
      ↔ mersenneWeight (n + 1) ≤ greedyMersenneRemainder (x : ℝ) n := by
  constructor
  · intro h
    have hc : ((mersenneWeightRat (n + 1) : ℚ) : ℝ)
        ≤ ((greedyMersenneRemainderRat x n : ℚ) : ℝ) := by
      exact_mod_cast h
    simpa using hc
  · intro h
    rw [← cast_greedyMersenneRemainderRat x n] at h
    have hc : ((mersenneWeightRat (n + 1) : ℚ) : ℝ)
        ≤ ((greedyMersenneRemainderRat x n : ℚ) : ℝ) := by
      simpa using h
    exact_mod_cast hc

/-- A rational value already known to have normalized support has computable
support bits, recovered by the exact rational greedy recurrence.  This does
not assert decidability of achievement-set membership. -/
theorem rational_member_support_bit_iff
    (x : ℚ) (A : Set ℕ) (hA0 : 0 ∉ A)
    (hvalue : ((x : ℚ) : ℝ) = positiveMersenneSupportValue A) (n : ℕ) :
    n + 1 ∈ A ↔
      mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n := by
  rw [rational_greedy_take_iff_real]
  rw [hvalue]
  have hset := greedySupport_supportValue_eq A hA0
  have hmem : n + 1 ∈ A ↔
      n + 1 ∈ greedyMersenneSupport (positiveMersenneSupportValue A) := by
    rw [hset]
  exact hmem.trans (succ_mem_greedyMersenneSupport_iff _ n)

/-! ## Exact regression fixtures -/

/-- The formal development.s exact worked prefix identity.  Selecting exponents
`{2,3,6,7,14}` from the target `1/2` leaves the rational residual
`1/688086`. -/
theorem half_sub_five_term_prefix_eq :
    (1 / 2 : ℚ)
      - finiteErdosSum ({2, 3, 6, 7, 14} : Finset ℕ) 2
      = 1 / 688086 := by
  norm_num [finiteErdosSum]

/-! ## Half-prefix forcing and the dyadic boundary obstruction

The finite greedy computation for the target `1/2` admits a sharper
interpretation than level-by-level survival.  Splitting each Mersenne weight
into its binary skeleton and a positive correction turns a sufficiently long
support prefix into a narrow interval for the correction value.  If those
intervals are trapped in compatible dyadic cylinders of unbounded depth, the
correction and complementary-binary values coincide, giving an exact support
identity.  This section formalizes that coinductive limit interface and the
elementary arithmetic at a crossed dyadic boundary.  It does *not* prove that
the generated forcing chain is unbounded.
-/

/-- The unresolved correction after exponent `n`: the full Mersenne tail
minus its binary skeleton. -/
noncomputable def mersenneCorrectionTail (n : ℕ) : ℝ :=
  mersenneTail n - ((1 : ℝ) / 2) ^ n

/-- The checked two-channel expansion is exactly the correction-tail
decomposition used by prefix forcing. -/
theorem mersenneCorrectionTail_eq (n : ℕ) :
    mersenneCorrectionTail n
      = (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
        + mersenneWeightRemainderTail n := by
  rw [mersenneCorrectionTail, mersenneTail_eq_two_channels_add_remainderTail]
  ring

theorem mersenneCorrectionTail_nonneg (n : ℕ) :
    0 ≤ mersenneCorrectionTail n := by
  rw [mersenneCorrectionTail_eq]
  exact add_nonneg (mul_nonneg (by norm_num) (by positivity))
    (mersenneWeightRemainderTail_nonneg n)

theorem mersenneCorrectionTail_pos (n : ℕ) :
    0 < mersenneCorrectionTail n := by
  rw [mersenneCorrectionTail_eq]
  have hquarter : 0 < (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n := by positivity
  have hrem := mersenneWeightRemainderTail_nonneg n
  linarith

/-- Explicit enclosure for the unresolved correction. -/
theorem mersenneCorrectionTail_le (n : ℕ) :
    mersenneCorrectionTail n
      ≤ (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
        + (2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n := by
  rw [mersenneCorrectionTail_eq]
  exact add_le_add (le_refl _) (mersenneWeightRemainderTail_le n)

/-- A simple explicit block length already makes the unresolved correction
smaller than the higher-channel gap at the starting level.  The sharper
`ceil(m/2)+1` length is not needed for the cap consumer; `m+1` keeps the
formal inequality transparent while remaining linear and uniform. -/
theorem mersenneCorrectionTail_add_self_succ_lt_remainderTail
    {m : ℕ} (hm : 0 < m) :
    mersenneCorrectionTail (m + (m + 1)) <
      mersenneWeightRemainderTail m := by
  have hcorr := mersenneCorrectionTail_le (m + (m + 1))
  have hhalf : ((1 : ℝ) / 2) ^ m ≤ (1 : ℝ) / 2 := by
    calc
      ((1 : ℝ) / 2) ^ m ≤ ((1 : ℝ) / 2) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = (1 : ℝ) / 2 := pow_one _
  have height : ((1 : ℝ) / 8) ^ m ≤ (1 : ℝ) / 8 := by
    calc
      ((1 : ℝ) / 8) ^ m ≤ ((1 : ℝ) / 8) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = (1 : ℝ) / 8 := pow_one _
  have hfour_id :
      ((1 : ℝ) / 4) ^ (m + (m + 1)) =
        ((1 : ℝ) / 8) ^ m * ((1 : ℝ) / 2) ^ m * ((1 : ℝ) / 4) := by
    calc
      ((1 : ℝ) / 4) ^ (m + (m + 1))
          = (((1 : ℝ) / 4) * ((1 : ℝ) / 4)) ^ m *
              ((1 : ℝ) / 4) := by
            rw [pow_add, pow_succ, mul_pow]
            ring
      _ = ((1 : ℝ) / 8) ^ m * ((1 : ℝ) / 2) ^ m *
              ((1 : ℝ) / 4) := by
            rw [show ((1 : ℝ) / 4) * ((1 : ℝ) / 4) =
              ((1 : ℝ) / 8) * ((1 : ℝ) / 2) by norm_num, mul_pow]
  have height_id :
      ((1 : ℝ) / 8) ^ (m + (m + 1)) =
        ((1 : ℝ) / 8) ^ m * ((1 : ℝ) / 8) ^ m * ((1 : ℝ) / 8) := by
    rw [pow_add, pow_succ]
    ring
  have hfour_le :
      ((1 : ℝ) / 4) ^ (m + (m + 1)) ≤
        (1 / 8 : ℝ) * ((1 : ℝ) / 8) ^ m := by
    rw [hfour_id]
    calc
      ((1 : ℝ) / 8) ^ m * ((1 : ℝ) / 2) ^ m * ((1 : ℝ) / 4)
          ≤ ((1 : ℝ) / 8) ^ m * ((1 : ℝ) / 2) * ((1 : ℝ) / 4) := by
            gcongr
      _ = (1 / 8 : ℝ) * ((1 : ℝ) / 8) ^ m := by ring
  have height_le :
      ((1 : ℝ) / 8) ^ (m + (m + 1)) ≤
        (1 / 64 : ℝ) * ((1 : ℝ) / 8) ^ m := by
    rw [height_id]
    calc
      ((1 : ℝ) / 8) ^ m * ((1 : ℝ) / 8) ^ m * ((1 : ℝ) / 8)
          ≤ ((1 : ℝ) / 8) ^ m * ((1 : ℝ) / 8) * ((1 : ℝ) / 8) := by
            gcongr
      _ = (1 / 64 : ℝ) * ((1 : ℝ) / 8) ^ m := by ring
  have hpow : 0 < ((1 : ℝ) / 8) ^ m := by positivity
  have hsmall :
      (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ (m + (m + 1)) +
          (2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ (m + (m + 1)) <
        (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ m := by
    have hfour_scaled := mul_le_mul_of_nonneg_left hfour_le (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have height_scaled := mul_le_mul_of_nonneg_left height_le (by norm_num : (0 : ℝ) ≤ 2 / 7)
    nlinarith
  exact lt_trans (hcorr.trans_lt hsmall)
    (one_seventh_eighth_pow_lt_mersenneWeightRemainderTail m)

/-- Sharp explicit block length from the corrected paper analysis:
`ceil(m/2)+1`, written over naturals as `(m+1)/2+1`. -/
theorem mersenneCorrectionTail_ceilingHalf_add_one_lt_remainderTail
    {m : ℕ} (hm : 0 < m) :
    let J := (m + 1) / 2 + 1
    mersenneCorrectionTail (m + J) < mersenneWeightRemainderTail m := by
  dsimp only
  let J : ℕ := (m + 1) / 2 + 1
  have hcorr := mersenneCorrectionTail_le (m + J)
  have hexpFour : 3 * m + 2 ≤ 2 * (m + J) := by
    dsimp [J]
    omega
  have hexpEight : 3 * m + 6 ≤ 3 * (m + J) := by
    have hJ : 2 ≤ J := by
      dsimp [J]
      omega
    omega
  have hfour_source :
      ((1 : ℝ) / 4) ^ (m + J) =
        ((1 : ℝ) / 2) ^ (2 * (m + J)) := by
    rw [show ((1 : ℝ) / 4) = ((1 : ℝ) / 2) ^ 2 by norm_num, pow_mul]
  have hfour_target :
      (1 / 4 : ℝ) * ((1 : ℝ) / 8) ^ m =
        ((1 : ℝ) / 2) ^ (3 * m + 2) := by
    rw [show ((1 : ℝ) / 4) = ((1 : ℝ) / 2) ^ 2 by norm_num,
      show ((1 : ℝ) / 8) = ((1 : ℝ) / 2) ^ 3 by norm_num,
      ← pow_mul, ← pow_add]
    congr 1
    omega
  have height_source :
      ((1 : ℝ) / 8) ^ (m + J) =
        ((1 : ℝ) / 2) ^ (3 * (m + J)) := by
    rw [show ((1 : ℝ) / 8) = ((1 : ℝ) / 2) ^ 3 by norm_num, pow_mul]
  have height_target :
      (1 / 64 : ℝ) * ((1 : ℝ) / 8) ^ m =
        ((1 : ℝ) / 2) ^ (3 * m + 6) := by
    rw [show ((1 : ℝ) / 64) = ((1 : ℝ) / 2) ^ 6 by norm_num,
      show ((1 : ℝ) / 8) = ((1 : ℝ) / 2) ^ 3 by norm_num,
      ← pow_mul, ← pow_add]
    congr 1
    omega
  have hfour_le :
      ((1 : ℝ) / 4) ^ (m + J) ≤
        (1 / 4 : ℝ) * ((1 : ℝ) / 8) ^ m := by
    rw [hfour_source, hfour_target]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hexpFour
  have height_le :
      ((1 : ℝ) / 8) ^ (m + J) ≤
        (1 / 64 : ℝ) * ((1 : ℝ) / 8) ^ m := by
    rw [height_source, height_target]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hexpEight
  have hpow : 0 < ((1 : ℝ) / 8) ^ m := by positivity
  have hsmall :
      (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ (m + J) +
          (2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ (m + J) <
        (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ m := by
    have hfour_scaled := mul_le_mul_of_nonneg_left hfour_le
      (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have height_scaled := mul_le_mul_of_nonneg_left height_le
      (by norm_num : (0 : ℝ) ≤ 2 / 7)
    nlinarith
  exact lt_trans (hcorr.trans_lt hsmall)
    (one_seventh_eighth_pow_lt_mersenneWeightRemainderTail m)

theorem tendsto_mersenneCorrectionTail_zero :
    Tendsto mersenneCorrectionTail atTop (nhds 0) := by
  unfold mersenneCorrectionTail
  simpa using tendsto_mersenneTail_zero.sub
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 : ℝ) / 2)
      (by norm_num) (by norm_num))

/-! ## Exact finite-block sliver return geometry -/

/-- `C(m,J)`: the exact initial remainder which lands on the dyadic boundary
after subtracting the next `J` consecutive Mersenne weights. -/
noncomputable def mersenneForcedReturnThreshold (m J : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ (m + J) +
    ∑ k ∈ Finset.range J, mersenneWeight (m + k + 1)

@[simp] theorem mersenneForcedReturnThreshold_zero (m : ℕ) :
    mersenneForcedReturnThreshold m 0 = ((1 : ℝ) / 2) ^ m := by
  simp [mersenneForcedReturnThreshold]

/-- The threshold is exactly the full tail minus the unresolved correction
at the post-block level. -/
theorem mersenneForcedReturnThreshold_eq_tail_sub_correction
    (m J : ℕ) :
    mersenneForcedReturnThreshold m J =
      mersenneTail m - mersenneCorrectionTail (m + J) := by
  rw [mersenneTail_eq_prefix_add_tail]
  unfold mersenneForcedReturnThreshold mersenneCorrectionTail
  ring

/-- Finite-block return is a single exact scalar comparison. -/
theorem forcedBlock_le_dyadic_iff_le_returnThreshold
    (m J : ℕ) (r : ℝ) :
    r - (∑ k ∈ Finset.range J, mersenneWeight (m + k + 1))
        ≤ ((1 : ℝ) / 2) ^ (m + J) ↔
      r ≤ mersenneForcedReturnThreshold m J := by
  constructor <;> intro h <;> unfold mersenneForcedReturnThreshold at * <;>
    linarith

theorem mersenneForcedReturnThreshold_succ (m J : ℕ) :
    mersenneForcedReturnThreshold m (J + 1) =
      mersenneForcedReturnThreshold m J + mersenneWeight (m + J + 1) -
        ((1 : ℝ) / 2) ^ (m + J + 1) := by
  unfold mersenneForcedReturnThreshold
  rw [Finset.sum_range_succ]
  simp only [pow_succ]
  ring

/-- Every extra forced take strictly enlarges the return region. -/
theorem mersenneForcedReturnThreshold_strictMono (m J : ℕ) :
    mersenneForcedReturnThreshold m J <
      mersenneForcedReturnThreshold m (J + 1) := by
  rw [mersenneForcedReturnThreshold_succ]
  have hweight := mersenneWeight_eq_two_channels_add_remainder
    (n := m + J + 1) (by omega)
  have hquarter : 0 < ((1 : ℝ) / 4) ^ (m + J + 1) := by positivity
  have hrem := mersenneWeightRemainder_nonneg (n := m + J + 1) (by omega)
  linarith

/-- The finite return thresholds increase to the true separatrix `T_m`. -/
theorem tendsto_mersenneForcedReturnThreshold (m : ℕ) :
    Tendsto (fun J : ℕ => mersenneForcedReturnThreshold m J)
      atTop (nhds (mersenneTail m)) := by
  have hcorr : Tendsto (fun J : ℕ => mersenneCorrectionTail (m + J))
      atTop (nhds 0) := by
    have h := tendsto_mersenneCorrectionTail_zero.comp (tendsto_add_atTop_nat m)
    simpa [Nat.add_comm] using h
  have heq : (fun J : ℕ => mersenneForcedReturnThreshold m J) =
      (fun J : ℕ => mersenneTail m - mersenneCorrectionTail (m + J)) := by
    funext J
    exact mersenneForcedReturnThreshold_eq_tail_sub_correction m J
  rw [heq]
  have hconst : Tendsto (fun _ : ℕ => mersenneTail m)
      atTop (nhds (mersenneTail m)) := tendsto_const_nhds
  simpa using hconst.sub hcorr

/-- Any relaxed state strictly below the full remaining tail returns to the
dyadic-safe side after finitely many consecutive takes. -/
theorem exists_forcedBlock_return_of_lt_tail
    {m : ℕ} {r : ℝ} (hr : r < mersenneTail m) :
    ∃ J : ℕ,
      r - (∑ k ∈ Finset.range J, mersenneWeight (m + k + 1))
        ≤ ((1 : ℝ) / 2) ^ (m + J) := by
  have hlim := tendsto_mersenneForcedReturnThreshold m
  obtain ⟨J, hJ⟩ := ((tendsto_order.1 hlim).1 r hr).exists
  exact ⟨J,
    (forcedBlock_le_dyadic_iff_le_returnThreshold m J r).2 hJ.le⟩

/-- On the separatrix, subtracting a forced block leaves exactly the later
tail. -/
theorem tail_sub_forcedBlock_eq_tail (m J : ℕ) :
    mersenneTail m -
        (∑ k ∈ Finset.range J, mersenneWeight (m + k + 1)) =
      mersenneTail (m + J) := by
  have htail := mersenneTail_eq_prefix_add_tail m J
  linarith

/-- Above the separatrix, the positive excess over the tail survives every
forced block; in particular the state never reaches the dyadic-safe side. -/
theorem dyadic_lt_forcedBlock_of_tail_lt
    {m J : ℕ} {r : ℝ} (hr : mersenneTail m < r) :
    ((1 : ℝ) / 2) ^ (m + J) <
      r - (∑ k ∈ Finset.range J, mersenneWeight (m + k + 1)) := by
  have htail := mersenneTail_eq_prefix_add_tail m J
  have hdyadic : ((1 : ℝ) / 2) ^ (m + J) < mersenneTail (m + J) := by
    have hcorr := mersenneCorrectionTail_pos (m + J)
    unfold mersenneCorrectionTail at hcorr
    linarith
  linarith

/-- Explicit linear return bound for the two-channel cap.  At every positive
starting level `m`, `m+1` consecutive forced takes suffice. -/
theorem halfTwoChannelCap_lt_forcedReturnThreshold_add_one
    {m : ℕ} (hm : 0 < m) :
    halfTwoChannelCap m < mersenneForcedReturnThreshold m (m + 1) := by
  rw [mersenneForcedReturnThreshold_eq_tail_sub_correction,
    mersenneTail_eq_two_channels_add_remainderTail]
  unfold halfTwoChannelCap
  have hsmall := mersenneCorrectionTail_add_self_succ_lt_remainderTail hm
  linarith

theorem forcedBlock_return_of_le_twoChannelCap_add_one
    {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : r ≤ halfTwoChannelCap m) :
    r - (∑ k ∈ Finset.range (m + 1), mersenneWeight (m + k + 1))
      ≤ ((1 : ℝ) / 2) ^ (m + (m + 1)) := by
  apply (forcedBlock_le_dyadic_iff_le_returnThreshold m (m + 1) r).2
  exact hr.trans
    (halfTwoChannelCap_lt_forcedReturnThreshold_add_one hm).le

/-- Sharp paper-grade return bound for the landed two-channel cap. -/
theorem halfTwoChannelCap_lt_forcedReturnThreshold_ceilingHalf
    {m : ℕ} (hm : 0 < m) :
    let J := (m + 1) / 2 + 1
    halfTwoChannelCap m < mersenneForcedReturnThreshold m J := by
  dsimp only
  rw [mersenneForcedReturnThreshold_eq_tail_sub_correction,
    mersenneTail_eq_two_channels_add_remainderTail]
  unfold halfTwoChannelCap
  have hsmall := mersenneCorrectionTail_ceilingHalf_add_one_lt_remainderTail hm
  linarith

theorem forcedBlock_return_of_le_twoChannelCap_ceilingHalf
    {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : r ≤ halfTwoChannelCap m) :
    let J := (m + 1) / 2 + 1
    r - (∑ k ∈ Finset.range J, mersenneWeight (m + k + 1))
      ≤ ((1 : ℝ) / 2) ^ (m + J) := by
  dsimp only
  apply (forcedBlock_le_dyadic_iff_le_returnThreshold
    m ((m + 1) / 2 + 1) r).2
  exact hr.trans
    (halfTwoChannelCap_lt_forcedReturnThreshold_ceilingHalf hm).le

/-- The landed two-channel cap is strictly inside the finite-return region
for some block length.  This is generic return geometry only: proving that
the actual half orbit satisfies the cap at every skip remains the arithmetic
producer. -/
theorem exists_forcedBlock_return_of_le_twoChannelCap
    {m : ℕ} {r : ℝ} (hr : r ≤ halfTwoChannelCap m) :
    ∃ J : ℕ,
      r - (∑ k ∈ Finset.range J, mersenneWeight (m + k + 1))
        ≤ ((1 : ℝ) / 2) ^ (m + J) := by
  exact exists_forcedBlock_return_of_lt_tail
    (hr.trans_lt (halfTwoChannelCap_lt_mersenneTail m))

/-! ## Exact sliver-normalization regression fixtures -/

/-- An undoubled coordinate below `2 / 3` does not force return for a generic
relaxed sliver state. -/
theorem undoubled_twoThirds_relaxed_escape_fixture :
    let r : ℚ := 37 / 280
    (((1 : ℚ) / 2) ^ 3 < r ∧ r < mersenneWeightRat 3) ∧
      mersenneSliverCoordinateRat 3 r = 2 / 5 ∧
      mersenneWeightRat 5 <
        (r - mersenneWeightRat 4) - mersenneWeightRat 5 := by
  norm_num [mersenneSliverCoordinateRat, mersenneWeightRat]

/-- Even the doubled coordinate can lie below `2 / 3` while a generic state
is already above the true tail.  This prevents the limiting frozen-map fixed
point from being reused as an exact finite separatrix. -/
theorem doubled_twoThirds_below_but_above_tail_fixture :
    let r : ℚ := 67 / 512
    (((1 : ℚ) / 2) ^ 3 < r ∧ r < mersenneWeightRat 3) ∧
      sharpMersenneSliverCoordinateRat 3 r = 21 / 32 ∧
      mersenneTail 3 < (r : ℝ) := by
  dsimp
  constructor
  · norm_num [mersenneWeightRat]
  constructor
  · norm_num [sharpMersenneSliverCoordinateRat]
  · rw [mersenneTail_eq_two_channels_add_remainderTail]
    have hrem := mersenneWeightRemainderTail_le 3
    norm_num at hrem ⊢
    linarith

/-- The Mersenne part of the greedy prefix for the target `1/2`. -/
noncomputable def halfGreedyMersennePrefix (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    Set.indicator (greedyMersenneSupport (1 / 2 : ℝ)) mersenneWeight (k + 1)

/-- The binary-skeleton part selected by the same finite greedy prefix. -/
noncomputable def halfGreedyDyadicPrefix (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    Set.indicator (greedyMersenneSupport (1 / 2 : ℝ))
      (fun m : ℕ => ((1 : ℝ) / 2) ^ m) (k + 1)

/-- The selected correction prefix `E_N`.  Exponent one is harmless because
the greedy run for `1/2` omits it. -/
noncomputable def halfGreedyCorrectionPrefix (n : ℕ) : ℝ :=
  halfGreedyMersennePrefix n - halfGreedyDyadicPrefix n

/-- The complementary dyadic prefix `C_N`.  For positive `n`, the omitted
exponent-one digit and the finite geometric sum reduce this to
`1/2 - 2^{-n}` minus the selected dyadic prefix. -/
noncomputable def halfGreedyComplementPrefix (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) - ((1 : ℝ) / 2) ^ n - halfGreedyDyadicPrefix n

/-- The finite correction/complement difference is exactly the dyadic
boundary minus the greedy residual. -/
theorem halfGreedyCorrectionPrefix_sub_complementPrefix (n : ℕ) :
    halfGreedyCorrectionPrefix n - halfGreedyComplementPrefix n
      = ((1 : ℝ) / 2) ^ n
        - greedyMersenneRemainder (1 / 2 : ℝ) n := by
  have hprefix := greedyMersenne_prefix_add_remainder (1 / 2 : ℝ) n
  change (1 / 2 : ℝ) = halfGreedyMersennePrefix n
    + greedyMersenneRemainder (1 / 2 : ℝ) n at hprefix
  unfold halfGreedyCorrectionPrefix halfGreedyComplementPrefix
  linarith

/-- The complete correction enclosure is trapped in the current
complementary dyadic cylinder exactly on the residual self-trapping strip. -/
theorem halfGreedyCorrectionInterval_subset_complementInterval_iff (n : ℕ) :
    Set.Icc (halfGreedyCorrectionPrefix n)
        (halfGreedyCorrectionPrefix n + mersenneCorrectionTail n) ⊆
      Set.Icc (halfGreedyComplementPrefix n)
        (halfGreedyComplementPrefix n + ((1 : ℝ) / 2) ^ n) ↔
      mersenneCorrectionTail n
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n ∧
        greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ ((1 : ℝ) / 2) ^ n := by
  have hdiff := halfGreedyCorrectionPrefix_sub_complementPrefix n
  have heta := mersenneCorrectionTail_nonneg n
  constructor
  · intro hsubset
    have hlower := hsubset
      (show halfGreedyCorrectionPrefix n ∈
          Set.Icc (halfGreedyCorrectionPrefix n)
            (halfGreedyCorrectionPrefix n + mersenneCorrectionTail n) by
        exact ⟨le_rfl, le_add_of_nonneg_right heta⟩)
    have hupper := hsubset
      (show halfGreedyCorrectionPrefix n + mersenneCorrectionTail n ∈
          Set.Icc (halfGreedyCorrectionPrefix n)
            (halfGreedyCorrectionPrefix n + mersenneCorrectionTail n) by
        exact ⟨le_add_of_nonneg_right heta, le_rfl⟩)
    obtain ⟨hlow1, hlow2⟩ := Set.mem_Icc.mp hlower
    obtain ⟨hup1, hup2⟩ := Set.mem_Icc.mp hupper
    constructor <;> linarith
  · rintro ⟨hetaRem, hremDyadic⟩ z ⟨hzLower, hzUpper⟩
    constructor <;> linarith

/-- The complementary part of the surviving tail mass. -/
noncomputable def greedyMersenneComplementRemainder (x : ℝ) (n : ℕ) : ℝ :=
  mersenneTail n - greedyMersenneRemainder x n

/-- Signed difference between the residual and its complementary tail bin. -/
noncomputable def greedyMersenneSignedBalance (x : ℝ) (n : ℕ) : ℝ :=
  greedyMersenneRemainder x n - greedyMersenneComplementRemainder x n

/-- The positive gap between one Mersenne weight and the tail after it. -/
noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n

theorem greedyMersenneSignedBalance_eq (x : ℝ) (n : ℕ) :
    greedyMersenneSignedBalance x n
      = 2 * greedyMersenneRemainder x n - mersenneTail n := by
  unfold greedyMersenneSignedBalance greedyMersenneComplementRemainder
  ring

theorem mersenneGap_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneGap n := by
  unfold mersenneGap
  exact sub_pos.mpr (mersenneTail_lt_weight hn)

/-- In the signed-balance coordinate, the self-trapping strip is the centered
interval of radius `2^{-N} - η_N`. -/
theorem halfGreedy_selfTrapping_iff_abs_signedBalance_le (n : ℕ) :
    (mersenneCorrectionTail n
        ≤ greedyMersenneRemainder (1 / 2 : ℝ) n ∧
      greedyMersenneRemainder (1 / 2 : ℝ) n
        ≤ ((1 : ℝ) / 2) ^ n) ↔
      |greedyMersenneSignedBalance (1 / 2 : ℝ) n|
        ≤ ((1 : ℝ) / 2) ^ n - mersenneCorrectionTail n := by
  rw [greedyMersenneSignedBalance_eq, abs_le]
  unfold mersenneCorrectionTail
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Exact one-step affine recurrence before folding: a selected weight moves
the balance left by that weight, while an omitted weight moves it right. -/
theorem greedyMersenneSignedBalance_succ (x : ℝ) (n : ℕ) :
    greedyMersenneSignedBalance x (n + 1)
      = if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
          greedyMersenneSignedBalance x n - mersenneWeight (n + 1)
        else
          greedyMersenneSignedBalance x n + mersenneWeight (n + 1) := by
  rw [greedyMersenneSignedBalance_eq, greedyMersenneSignedBalance_eq,
    greedyMersenneRemainder_succ]
  have htail := mersenneTail_eq_weight_add n
  split_ifs <;> linarith

/-- For a currently surviving residual, survival of the next greedy step is
equivalent to the signed balance avoiding the open gap around zero. -/
theorem greedyMersenne_next_survives_iff_gap_le_abs_signedBalance
    {x : ℝ} {n : ℕ}
    (_hremNonneg : 0 ≤ greedyMersenneRemainder x n)
    (hremTail : greedyMersenneRemainder x n ≤ mersenneTail n) :
    greedyMersenneRemainder x (n + 1) ≤ mersenneTail (n + 1) ↔
      mersenneGap (n + 1) ≤ |greedyMersenneSignedBalance x n| := by
  have htailRec := mersenneTail_eq_weight_add n
  have hgapPos := mersenneGap_pos (n := n + 1) (by omega)
  rw [greedyMersenneRemainder_succ]
  by_cases htake :
      mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n
  · rw [if_pos htake]
    have hbalanceNonneg :
        0 ≤ greedyMersenneSignedBalance x n := by
      rw [greedyMersenneSignedBalance_eq]
      unfold mersenneGap at hgapPos
      linarith
    rw [abs_of_nonneg hbalanceNonneg]
    constructor <;> intro _
    · rw [greedyMersenneSignedBalance_eq]
      unfold mersenneGap
      linarith
    · linarith
  · rw [if_neg htake]
    constructor
    · intro hnext
      have hbalanceNonpos :
          greedyMersenneSignedBalance x n ≤ 0 := by
        rw [greedyMersenneSignedBalance_eq]
        linarith
      rw [abs_of_nonpos hbalanceNonpos]
      rw [greedyMersenneSignedBalance_eq]
      unfold mersenneGap
      linarith
    · intro hgap
      by_contra hnotNext
      have hnextLt :
          mersenneTail (n + 1) < greedyMersenneRemainder x n :=
        lt_of_not_ge hnotNext
      have hbalanceLtGap :
          |greedyMersenneSignedBalance x n| < mersenneGap (n + 1) := by
        rw [abs_lt]
        rw [greedyMersenneSignedBalance_eq]
        unfold mersenneGap
        constructor <;> linarith
      linarith

/-- On a surviving next step, the signed balance follows the exact folded
subtraction recurrence. -/
theorem abs_greedyMersenneSignedBalance_succ
    {x : ℝ} {n : ℕ}
    (_hremTail : greedyMersenneRemainder x n ≤ mersenneTail n)
    (hnext : greedyMersenneRemainder x (n + 1) ≤ mersenneTail (n + 1)) :
    |greedyMersenneSignedBalance x (n + 1)|
      = abs (|greedyMersenneSignedBalance x n| - mersenneWeight (n + 1)) := by
  rw [greedyMersenneSignedBalance_succ]
  by_cases htake :
      mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n
  · rw [if_pos htake]
    have hbalanceNonneg :
        0 ≤ greedyMersenneSignedBalance x n := by
      rw [greedyMersenneSignedBalance_eq]
      have htailGap := mersenneTail_lt_weight (n := n + 1) (by omega)
      have htail := mersenneTail_eq_weight_add n
      linarith
    rw [abs_of_nonneg hbalanceNonneg]
  · rw [if_neg htake]
    have hnext' :
        greedyMersenneRemainder x n ≤ mersenneTail (n + 1) := by
      rw [greedyMersenneRemainder_succ, if_neg htake] at hnext
      exact hnext
    have hbalanceNonpos :
        greedyMersenneSignedBalance x n ≤ 0 := by
      rw [greedyMersenneSignedBalance_eq, mersenneTail_eq_weight_add]
      have hweightPos := mersenneWeight_pos (n := n + 1) (by omega)
      linarith
    rw [abs_of_nonpos hbalanceNonpos, ← abs_neg]
    congr 1
    ring

/-! ## Greedy shadows and the second-channel separation interface -/

/-- The Erdős–Borwein constant, expressed in the positive Mersenne-tail
coordinate already used throughout this file. -/
noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0

/-- The tail-coordinate version of the Erdős–Borwein constant inherits the
unconditional irrationality theorem already proved in the certificate
kernel. -/
theorem irrational_erdosBorweinMersenneConstant :
    Irrational erdosBorweinMersenneConstant := by
  simpa [erdosBorweinMersenneConstant, mersenneTail, mersenneWeight] using
    irrational_erdosBorwein_series

/-- Selected and omitted positive exponents partition the full
Erdős–Borwein series. -/
theorem erdosBorweinMersenneConstant_eq_greedy_add_skipped (x : ℝ) :
    erdosBorweinMersenneConstant
      = positiveMersenneSupportValue (greedyMersenneSupport x)
        + positiveMersenneSupportValue (greedyMersenneSkippedSupport x) := by
  rw [erdosBorweinMersenneConstant, mersenneTail,
    positiveMersenneSupportValue, positiveMersenneSupportValue,
    ← (summable_positiveMersenneSupportIndicator
      (greedyMersenneSupport x)).tsum_add
        (summable_positiveMersenneSupportIndicator
          (greedyMersenneSkippedSupport x))]
  apply tsum_congr
  intro k
  by_cases hk : k + 1 ∈ greedyMersenneSupport x
  · simp [greedyMersenneSkippedSupport, hk]
  · simp [greedyMersenneSkippedSupport, hk]

/-- A finite normalized support value is the real cast of its exact rational
finite Erdős sum. -/
theorem positiveMersenneSupportValue_eq_cast_finiteErdosSum
    (F : Finset ℕ) :
    positiveMersenneSupportValue (↑F : Set ℕ)
      = ((finiteErdosSum F 2 : ℚ) : ℝ) := by
  rw [positiveMersenneSupportValue_eq_erdosSupportSeries]
  calc
    erdosSupportSeries 2 (↑F : Set ℕ)
        = ∑ a ∈ F, mersenneWeight a := by
            unfold erdosSupportSeries
            rw [tsum_eq_sum (s := F)]
            · exact Finset.sum_congr rfl fun a ha => by
                simp [mersenneWeight, ha]
            · intro a ha
              simp [ha]
    _ = ((∑ a ∈ F, mersenneWeightRat a : ℚ) : ℝ) := by
          push_cast
          simp only [cast_mersenneWeightRat]
    _ = ((finiteErdosSum F 2 : ℚ) : ℝ) := by
          congr 1

/-- If a rational number is represented, its canonical greedy expansion must
omit infinitely many positive exponents.  Otherwise the irrational full
Erdős–Borwein constant would be a rational number plus a finite rational
Mersenne sum. -/
theorem infinite_greedyMersenneSkippedSupport_of_rat_mem
    {q : ℚ} (hmem : (q : ℝ) ∈ mersenneAchievementSet) :
    (greedyMersenneSkippedSupport (q : ℝ)).Infinite := by
  classical
  intro hfinite
  let F : Finset ℕ := hfinite.toFinset
  have hF : (↑F : Set ℕ) = greedyMersenneSkippedSupport (q : ℝ) := by
    dsimp [F]
    exact hfinite.coe_toFinset
  have hgreedy :
      positiveMersenneSupportValue (greedyMersenneSupport (q : ℝ))
        = (q : ℝ) := by
    rcases hmem with ⟨A, hA0, hvalue⟩
    have hsupport : greedyMersenneSupport (q : ℝ) = A := by
      rw [hvalue, greedySupport_supportValue_eq A hA0]
    rw [hsupport, ← hvalue]
  have hskipped :
      positiveMersenneSupportValue (greedyMersenneSkippedSupport (q : ℝ))
        = ((finiteErdosSum F 2 : ℚ) : ℝ) := by
    rw [← hF]
    exact positiveMersenneSupportValue_eq_cast_finiteErdosSum F
  apply (irrational_erdosBorweinMersenneConstant.ne_rat
    (q + finiteErdosSum F 2))
  rw [erdosBorweinMersenneConstant_eq_greedy_add_skipped,
    hgreedy, hskipped]
  push_cast
  rfl

/-- The rational skip criterion specializes to the target `1/2`. -/
theorem infinite_greedyMersenneSkippedSupport_of_half_mem
    (hhalf : (1 / 2 : ℝ) ∈ mersenneAchievementSet) :
    (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite := by
  have hhalf' : (((1 : ℚ) / 2 : ℚ) : ℝ) ∈ mersenneAchievementSet := by
    simpa using hhalf
  simpa using
    (infinite_greedyMersenneSkippedSupport_of_rat_mem
      (q := (1 : ℚ) / 2) hhalf')

/-- **Rational greedy skip dichotomy.**  A nonnegative rational target belongs
to the Mersenne achievement set exactly when its canonical greedy orbit omits
infinitely many positive exponents. -/
theorem rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (q : ℝ)).Infinite := by
  constructor
  · exact infinite_greedyMersenneSkippedSupport_of_rat_mem
  · exact mem_mersenneAchievementSet_of_greedySkippedSupport_infinite
      (by exact_mod_cast hq)

/-- **Cofinal lower-branch criterion for rational targets.**  A nonnegative
rational target belongs to the Mersenne achievement set exactly when its
greedy orbit skips at arbitrarily late ranks. -/
theorem rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
        ¬ mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (q : ℝ) n := by
  rw [rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite q hq,
    greedyMersenneSkippedSupport_infinite_iff_cofinal_skips]

/-- **Greedy skip dichotomy for the half target.**  Exact half-membership is
equivalent to the canonical greedy orbit omitting infinitely many exponents.
The forward direction uses Erdős–Borwein irrationality; the reverse direction
uses absorbing fatal states. -/
theorem half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite := by
  constructor
  · exact infinite_greedyMersenneSkippedSupport_of_half_mem
  · exact mem_mersenneAchievementSet_of_greedySkippedSupport_infinite
      (by norm_num)

/-- The total mass of the first `n` positive Mersenne weights. -/
noncomputable def mersennePrefixMass (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, mersenneWeight (k + 1)

/-- The mass selected by an arbitrary support through exponent `n`. -/
noncomputable def mersenneSupportPrefix (A : Set ℕ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, Set.indicator A mersenneWeight (k + 1)

theorem mersenneSupportPrefix_succ (A : Set ℕ) (n : ℕ) :
    mersenneSupportPrefix A (n + 1)
      = mersenneSupportPrefix A n
        + Set.indicator A mersenneWeight (n + 1) := by
  unfold mersenneSupportPrefix
  rw [Finset.sum_range_succ]

/-- The signed Mersenne shadow associated with an arbitrary support prefix. -/
noncomputable def mersenneShadowOfPrefix (A : Set ℕ) (n : ℕ) : ℝ :=
  1 + mersennePrefixMass n - 2 * mersenneSupportPrefix A n

/-- The shadow of the actual greedy prefix for the target `1/2`. -/
noncomputable def halfGreedyMersenneShadow (n : ℕ) : ℝ :=
  1 + mersennePrefixMass n - 2 * halfGreedyMersennePrefix n

theorem erdosBorweinMersenneConstant_eq_prefix_add_tail (n : ℕ) :
    erdosBorweinMersenneConstant = mersennePrefixMass n + mersenneTail n := by
  rw [erdosBorweinMersenneConstant, mersennePrefixMass]
  simpa using mersenneTail_eq_prefix_add_tail 0 n

/-- Exact shadow/signed-balance duality.  This turns a death-hole hit into an
Archimedean near-hit of the Erdős–Borwein constant without introducing a new
dynamical model. -/
theorem halfGreedyMersenneShadow_sub_constant_eq_signedBalance (n : ℕ) :
    halfGreedyMersenneShadow n - erdosBorweinMersenneConstant
      = greedyMersenneSignedBalance (1 / 2 : ℝ) n := by
  have htotal := erdosBorweinMersenneConstant_eq_prefix_add_tail n
  have hprefix := greedyMersenne_prefix_add_remainder (1 / 2 : ℝ) n
  change (1 / 2 : ℝ) = halfGreedyMersennePrefix n
    + greedyMersenneRemainder (1 / 2 : ℝ) n at hprefix
  rw [greedyMersenneSignedBalance_eq]
  unfold halfGreedyMersenneShadow
  linarith

/-- Once strict superincreasingness supplies a tail-sized separation from a
competing prefix, the surviving greedy prefix is strictly closer to the
Erdős–Borwein constant.  This is the reusable analytic core of the proposed
global nearest-shadow argument. -/
theorem halfGreedyShadow_closer_of_prefix_separation
    {n : ℕ}
    (hsurvive :
      greedyMersenneRemainder (1 / 2 : ℝ) n ≤ mersenneTail n)
    {A : Set ℕ}
    (hseparate :
      mersenneTail n <
        |mersenneSupportPrefix A n - halfGreedyMersennePrefix n|) :
    |erdosBorweinMersenneConstant - halfGreedyMersenneShadow n|
      < |erdosBorweinMersenneConstant - mersenneShadowOfPrefix A n| := by
  have hremNonneg := greedyMersenneRemainder_nonneg
    (x := (1 / 2 : ℝ)) (by norm_num) n
  have hprefix := greedyMersenne_prefix_add_remainder (1 / 2 : ℝ) n
  change (1 / 2 : ℝ) = halfGreedyMersennePrefix n
    + greedyMersenneRemainder (1 / 2 : ℝ) n at hprefix
  have htotal := erdosBorweinMersenneConstant_eq_prefix_add_tail n
  let b : ℝ := mersenneTail n
    - 2 * greedyMersenneRemainder (1 / 2 : ℝ) n
  let d : ℝ := mersenneSupportPrefix A n - halfGreedyMersennePrefix n
  have hb : |b| ≤ mersenneTail n := by
    dsimp [b]
    rw [abs_le]
    constructor <;> linarith
  have hd : mersenneTail n < |d| := by
    simpa [d] using hseparate
  have htriangle : 2 * |d| ≤ |b + 2 * d| + |b| := by
    calc
      2 * |d| = |2 * d| := by rw [abs_mul]; norm_num
      _ = |(b + 2 * d) + (-b)| := by congr 1 <;> ring
      _ ≤ |b + 2 * d| + |-b| := abs_add_le _ _
      _ = |b + 2 * d| + |b| := by rw [abs_neg]
  have hcloser : |b| < |b + 2 * d| := by
    linarith
  have hgreedy :
      erdosBorweinMersenneConstant - halfGreedyMersenneShadow n = b := by
    unfold halfGreedyMersenneShadow
    dsimp [b]
    linarith
  have hother :
      erdosBorweinMersenneConstant - mersenneShadowOfPrefix A n
        = b + 2 * d := by
    unfold mersenneShadowOfPrefix
    dsimp [b, d]
    linarith
  rw [hgreedy, hother]
  exact hcloser

/-- Under current survival, next-step survival is exactly separation of the
greedy shadow from the open Mersenne-gap neighbourhood of the constant. -/
theorem halfGreedy_next_survives_iff_shadow_separated
    {n : ℕ}
    (hsurvive :
      greedyMersenneRemainder (1 / 2 : ℝ) n ≤ mersenneTail n) :
    greedyMersenneRemainder (1 / 2 : ℝ) (n + 1)
        ≤ mersenneTail (n + 1) ↔
      mersenneGap (n + 1) ≤
        |halfGreedyMersenneShadow n - erdosBorweinMersenneConstant| := by
  have hnonneg := greedyMersenneRemainder_nonneg
    (x := (1 / 2 : ℝ)) (by norm_num) n
  simpa [halfGreedyMersenneShadow_sub_constant_eq_signedBalance] using
    (greedyMersenne_next_survives_iff_gap_le_abs_signedBalance
      hnonneg hsurvive)

/-- The normalized phase at the first scale where the second geometric
channel of the Mersenne tail is visible. -/
noncomputable def greedyMersenneSecondChannelPhase (n : ℕ) : ℝ :=
  (4 : ℝ) ^ n *
    (2 * greedyMersenneRemainder (1 / 2 : ℝ) n
      - ((1 : ℝ) / 2) ^ n)

/-- The two-channel cap is exactly the one-sided phase inequality
`greedyMersenneSecondChannelPhase n ≤ 1 / 6`.  This is an algebraic
equivalence and assumes no greedy branch decision. -/
theorem greedyMersenneSecondChannelPhase_le_one_six_iff_twoChannelCap
    (n : ℕ) :
    greedyMersenneSecondChannelPhase n ≤ 1 / 6 ↔
      greedyMersenneRemainder (1 / 2 : ℝ) n ≤ halfTwoChannelCap (n + 1) := by
  have hhalf :
      (4 : ℝ) ^ n * ((1 : ℝ) / 2) ^ n = (2 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have hquarter :
      (4 : ℝ) ^ n * ((1 : ℝ) / 4) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hscale : 0 < 2 * (4 : ℝ) ^ n := by positivity
  have hid :
      greedyMersenneSecondChannelPhase n - 1 / 6 =
        2 * (4 : ℝ) ^ n *
          (greedyMersenneRemainder (1 / 2 : ℝ) n -
            halfTwoChannelCap (n + 1)) := by
    unfold greedyMersenneSecondChannelPhase halfTwoChannelCap
    simp only [pow_succ]
    nlinarith
  constructor <;> intro h
  · have hnonpos :
        2 * (4 : ℝ) ^ n *
          (greedyMersenneRemainder (1 / 2 : ℝ) n -
            halfTwoChannelCap (n + 1)) ≤ 0 := by
      rw [← hid]
      linarith
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hnonpos hscale)
  · have hnonpos :
        greedyMersenneRemainder (1 / 2 : ℝ) n -
          halfTwoChannelCap (n + 1) ≤ 0 := sub_nonpos.mpr h
    rw [← sub_nonpos, hid]
    exact mul_nonpos_of_nonneg_of_nonpos hscale.le hnonpos

/-- Rational form of the second-channel phase.  Its branch arithmetic can be
proved over `ℚ` and then transferred to the real coordinate below. -/
def greedyMersenneSecondChannelPhaseRat (n : ℕ) : ℚ :=
  (4 : ℚ) ^ n *
    (2 * greedyMersenneRemainderRat (1 / 2 : ℚ) n
      - ((1 : ℚ) / 2) ^ n)

/-- Expanded form of the rational second-channel coordinate. -/
theorem greedyMersenneSecondChannelPhaseRat_eq_scaled_remainder (n : ℕ) :
    greedyMersenneSecondChannelPhaseRat n =
      2 * (4 : ℚ) ^ n *
          greedyMersenneRemainderRat (1 / 2 : ℚ) n -
        (2 : ℚ) ^ n := by
  have hhalf :
      ((1 : ℚ) / 2) ^ n * (4 : ℚ) ^ n = (2 : ℚ) ^ n := by
    rw [← mul_pow]
    norm_num
  unfold greedyMersenneSecondChannelPhaseRat
  calc
    (4 : ℚ) ^ n *
          (2 * greedyMersenneRemainderRat (1 / 2 : ℚ) n -
            ((1 : ℚ) / 2) ^ n) =
        2 * (4 : ℚ) ^ n *
            greedyMersenneRemainderRat (1 / 2 : ℚ) n -
          ((1 : ℚ) / 2) ^ n * (4 : ℚ) ^ n := by ring
    _ = 2 * (4 : ℚ) ^ n *
            greedyMersenneRemainderRat (1 / 2 : ℚ) n -
          (2 : ℚ) ^ n := by rw [hhalf]

/-- In the second-channel coordinate, the greedy branch decision is a single
moving threshold.  This removes the residual from the dynamical system:
rank `n+1` is selected exactly when
`2^n / (2^(n+1)-1) ≤ φ_n`. -/
theorem mersenneWeightRat_succ_le_half_iff_secondChannelPhaseRat
    (n : ℕ) :
    mersenneWeightRat (n + 1) ≤
        greedyMersenneRemainderRat (1 / 2 : ℚ) n ↔
      (2 : ℚ) ^ n / ((2 : ℚ) ^ (n + 1) - 1) ≤
        greedyMersenneSecondChannelPhaseRat n := by
  have hden : ((2 : ℚ) ^ (n + 1) - 1) ≠ 0 := by
    have hpow : (1 : ℚ) < 2 ^ (n + 1) :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hscale : 0 < 2 * (4 : ℚ) ^ n := by positivity
  have hphase :
      greedyMersenneSecondChannelPhaseRat n =
        2 * (4 : ℚ) ^ n *
            greedyMersenneRemainderRat (1 / 2 : ℚ) n -
          (2 : ℚ) ^ n :=
    greedyMersenneSecondChannelPhaseRat_eq_scaled_remainder n
  have hweight :
      2 * (4 : ℚ) ^ n * mersenneWeightRat (n + 1) =
        (2 : ℚ) ^ n +
          (2 : ℚ) ^ n / ((2 : ℚ) ^ (n + 1) - 1) := by
    unfold mersenneWeightRat
    have hfour :
        (4 : ℚ) ^ n = (2 : ℚ) ^ n * (2 : ℚ) ^ n := by
      rw [← mul_pow]
      norm_num
    field_simp [hden]
    rw [pow_succ, hfour]
    ring
  constructor <;> intro h
  · have hscaled := mul_le_mul_of_nonneg_left h hscale.le
    rw [hweight] at hscaled
    rw [hphase]
    linarith
  · have hscaled :
        2 * (4 : ℚ) ^ n * mersenneWeightRat (n + 1) ≤
          2 * (4 : ℚ) ^ n *
            greedyMersenneRemainderRat (1 / 2 : ℚ) n := by
      rw [hweight]
      rw [hphase] at h
      linarith
    nlinarith

/-- Exact branch dynamics of the rational second-channel phase.  A skipped
weight applies the expanding affine map
`φ ↦ 4 * φ + 2^(n+1)`.  A selected weight applies the same expansion
together with the complete finite-level Mersenne correction; the final
fraction is not an asymptotic error term. -/
theorem greedyMersenneSecondChannelPhaseRat_succ (n : ℕ) :
    greedyMersenneSecondChannelPhaseRat (n + 1) =
      if (2 : ℚ) ^ n / ((2 : ℚ) ^ (n + 1) - 1) ≤
          greedyMersenneSecondChannelPhaseRat n then
        4 * greedyMersenneSecondChannelPhaseRat n
          - (2 : ℚ) ^ (n + 1) - 2
          - 2 / ((2 : ℚ) ^ (n + 1) - 1)
      else
        4 * greedyMersenneSecondChannelPhaseRat n
          + (2 : ℚ) ^ (n + 1) := by
  by_cases h :
      mersenneWeightRat (n + 1) ≤
        greedyMersenneRemainderRat (1 / 2 : ℚ) n
  · have hphase :=
      (mersenneWeightRat_succ_le_half_iff_secondChannelPhaseRat n).mp h
    rw [if_pos hphase]
    rw [greedyMersenneSecondChannelPhaseRat_eq_scaled_remainder (n + 1),
      greedyMersenneSecondChannelPhaseRat_eq_scaled_remainder n,
      greedyMersenneRemainderRat_succ, if_pos h]
    have hden : ((2 : ℚ) ^ (n + 1) - 1) ≠ 0 := by
      have hpow : (1 : ℚ) < 2 ^ (n + 1) :=
        one_lt_pow₀ (by norm_num) (by omega)
      linarith
    have hfour :
        (4 : ℚ) ^ n = (2 : ℚ) ^ (n * 2) := by
      calc
        (4 : ℚ) ^ n = ((2 : ℚ) ^ 2) ^ n := by norm_num
        _ = (2 : ℚ) ^ (2 * n) := by rw [pow_mul]
        _ = (2 : ℚ) ^ (n * 2) := by congr 1 <;> omega
    unfold mersenneWeightRat
    field_simp [hden]
    simp only [pow_succ]
    rw [hfour]
    ring
  · have hphase :
        ¬ ((2 : ℚ) ^ n / ((2 : ℚ) ^ (n + 1) - 1) ≤
          greedyMersenneSecondChannelPhaseRat n) := by
      intro hphase
      exact h
        ((mersenneWeightRat_succ_le_half_iff_secondChannelPhaseRat n).mpr
          hphase)
    rw [if_neg hphase]
    rw [greedyMersenneSecondChannelPhaseRat_eq_scaled_remainder (n + 1),
      greedyMersenneSecondChannelPhaseRat_eq_scaled_remainder n,
      greedyMersenneRemainderRat_succ, if_neg h]
    simp only [pow_succ]
    ring

/-- Any hypothetical entry into the open unit interval has an exact
one-step predecessor window.  The two alternatives retain the actual greedy
branch condition, so this is a backward reachability statement rather than
an unconstrained affine estimate. -/
theorem secondChannelPhaseRat_unit_preimage
    {n : ℕ}
    (hzero : 0 < greedyMersenneSecondChannelPhaseRat (n + 1))
    (hone : greedyMersenneSecondChannelPhaseRat (n + 1) < 1) :
    (((2 : ℚ) ^ n / ((2 : ℚ) ^ (n + 1) - 1) ≤
          greedyMersenneSecondChannelPhaseRat n) ∧
        (2 : ℚ) ^ (n + 1) + 2 +
            2 / ((2 : ℚ) ^ (n + 1) - 1) <
          4 * greedyMersenneSecondChannelPhaseRat n ∧
        4 * greedyMersenneSecondChannelPhaseRat n <
          (2 : ℚ) ^ (n + 1) + 3 +
            2 / ((2 : ℚ) ^ (n + 1) - 1)) ∨
      (greedyMersenneSecondChannelPhaseRat n <
          (2 : ℚ) ^ n / ((2 : ℚ) ^ (n + 1) - 1) ∧
        -((2 : ℚ) ^ (n + 1)) <
          4 * greedyMersenneSecondChannelPhaseRat n ∧
        4 * greedyMersenneSecondChannelPhaseRat n <
          1 - (2 : ℚ) ^ (n + 1)) := by
  rw [greedyMersenneSecondChannelPhaseRat_succ] at hzero hone
  split_ifs at hzero hone with hbranch
  · left
    exact ⟨hbranch, by linarith, by linarith⟩
  · right
    exact ⟨lt_of_not_ge hbranch, by linarith, by linarith⟩

@[simp] theorem cast_greedyMersenneSecondChannelPhaseRat (n : ℕ) :
    ((greedyMersenneSecondChannelPhaseRat n : ℚ) : ℝ)
      = greedyMersenneSecondChannelPhase n := by
  unfold greedyMersenneSecondChannelPhaseRat
    greedyMersenneSecondChannelPhase
  push_cast
  rw [cast_greedyMersenneRemainderRat]
  norm_num

/-- Decidable rational form of the shrinking-hole avoidance condition. -/
def HalfSecondChannelSeparatedRat (n : ℕ) : Prop :=
  (1 / 6 : ℚ) + (37 / 56 : ℚ) * ((1 : ℚ) / 2) ^ n
    ≤ |greedyMersenneSecondChannelPhaseRat n - 1 / 3|

/-- From rank two onward, avoiding the open unit interval implies the exact
shrinking-hole separation condition.  This is only a sufficient reduction:
the theorem does not prove that the actual phase orbit avoids `(0, 1)`. -/
theorem halfSecondChannelSeparatedRat_of_outside_unit
    {n : ℕ} (hn : 2 ≤ n)
    (hout :
      greedyMersenneSecondChannelPhaseRat n ≤ 0 ∨
        1 ≤ greedyMersenneSecondChannelPhaseRat n) :
    HalfSecondChannelSeparatedRat n := by
  unfold HalfSecondChannelSeparatedRat
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hk :
      ((1 : ℚ) / 2) ^ k ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hpow :
      ((1 : ℚ) / 2) ^ (2 + k) ≤ 1 / 4 := by
    rw [pow_add]
    norm_num
    nlinarith
  rcases hout with hnonpos | hone
  · rw [abs_of_nonpos (by linarith)]
    nlinarith
  · rw [abs_of_nonneg (by linarith)]
    nlinarith

/-!
The recurrence and predecessor windows above identify an exact arithmetic
frontier, but they do not rule out visits to `(0, 1)`.  Consequently they do
not prove that one half is absent from the Mersenne achievement set and do not
settle Erdős #257.
-/

instance (n : ℕ) : Decidable (HalfSecondChannelSeparatedRat n) :=
  by
    unfold HalfSecondChannelSeparatedRat
    infer_instance

/-- The rational certificate casts directly to the real separation estimate
consumed by the greedy-survival theorem. -/
theorem secondChannelSeparation_of_rat {n : ℕ}
    (h : HalfSecondChannelSeparatedRat n) :
    (1 / 6 : ℝ) + (37 / 56 : ℝ) * ((1 : ℝ) / 2) ^ n
      ≤ |greedyMersenneSecondChannelPhase n - 1 / 3| := by
  unfold HalfSecondChannelSeparatedRat at h
  have hc :
      (((1 / 6 : ℚ) + (37 / 56 : ℚ) * ((1 : ℚ) / 2) ^ n : ℚ) : ℝ)
        ≤ ((|greedyMersenneSecondChannelPhaseRat n - 1 / 3| : ℚ) : ℝ) := by
    exact_mod_cast h
  rw [Rat.cast_abs] at hc
  push_cast at hc
  norm_num at hc
  exact hc

/-- Exact finite certificate for the only small levels visible in the
second-channel numerics.  The infinite producer can therefore start at
`n = 7`, where the observed margin is already large. -/
theorem halfSecondChannelSeparatedRat_of_pos_le_six
    {n : ℕ} (hn : 0 < n) (h6 : n ≤ 6) :
    HalfSecondChannelSeparatedRat n := by
  interval_cases n <;>
    norm_num [HalfSecondChannelSeparatedRat,
      greedyMersenneSecondChannelPhaseRat, greedyMersenneRemainderRat,
      mersenneWeightRat] at hn ⊢

/-- Exact decomposition of the scaled signed balance into its second-channel
phase, the universal `1/3` centre, and the higher-channel tail. -/
theorem four_pow_mul_signedBalance_eq_secondChannelPhase_sub (n : ℕ) :
    (4 : ℝ) ^ n * greedyMersenneSignedBalance (1 / 2 : ℝ) n
      = greedyMersenneSecondChannelPhase n - 1 / 3
        - (4 : ℝ) ^ n * mersenneWeightRemainderTail n := by
  have hfour :
      (4 : ℝ) ^ n * ((1 : ℝ) / 4) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [greedyMersenneSignedBalance_eq,
    greedyMersenneSecondChannelPhase,
    mersenneTail_eq_two_channels_add_remainderTail]
  nlinarith

/-- Scaling the higher-channel tail by `4^n` leaves an explicit exponentially
small error. -/
theorem four_pow_mul_mersenneWeightRemainderTail_le (n : ℕ) :
    (4 : ℝ) ^ n * mersenneWeightRemainderTail n
      ≤ (2 / 7 : ℝ) * ((1 : ℝ) / 2) ^ n := by
  have hscale :
      (4 : ℝ) ^ n * ((1 : ℝ) / 8) ^ n
        = ((1 : ℝ) / 2) ^ n := by
    rw [← mul_pow]
    norm_num
  calc
    (4 : ℝ) ^ n * mersenneWeightRemainderTail n
        ≤ (4 : ℝ) ^ n *
            ((2 / 7 : ℝ) * ((1 : ℝ) / 8) ^ n) :=
          mul_le_mul_of_nonneg_left (mersenneWeightRemainderTail_le n)
            (by positivity)
    _ = (2 / 7 : ℝ) *
          ((4 : ℝ) ^ n * ((1 : ℝ) / 8) ^ n) := by ring
    _ = (2 / 7 : ℝ) * ((1 : ℝ) / 2) ^ n := by rw [hscale]

/-- The next Mersenne gap at second-channel scale, including the exact
higher-channel error budget used by the separation consumer. -/
theorem four_pow_mul_next_mersenneGap_le (n : ℕ) :
    (4 : ℝ) ^ n * mersenneGap (n + 1)
      ≤ (1 / 6 : ℝ) + (3 / 8 : ℝ) * ((1 : ℝ) / 2) ^ n := by
  have h := mersenneGap_asymptotic_bound (n := n + 1) (by omega)
  change ‖mersenneGap (n + 1)
      - (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ (n + 1)‖
      ≤ 3 * ‖((1 : ℝ) / 8) ^ (n + 1)‖ at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity :
      0 ≤ ((1 : ℝ) / 8) ^ (n + 1))] at h
  have hu := (abs_le.mp h).2
  have hmul := mul_le_mul_of_nonneg_left hu
    (show 0 ≤ (4 : ℝ) ^ n by positivity)
  have hmain :
      (4 : ℝ) ^ n *
          ((2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ (n + 1))
        = (1 / 6 : ℝ) := by
    rw [pow_succ]
    have hfour :
        (4 : ℝ) ^ n * ((1 : ℝ) / 4) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    nlinarith
  have herr :
      (4 : ℝ) ^ n *
          (3 * ((1 : ℝ) / 8) ^ (n + 1))
        = (3 / 8 : ℝ) * ((1 : ℝ) / 2) ^ n := by
    rw [pow_succ]
    have hscale :
        (4 : ℝ) ^ n * ((1 : ℝ) / 8) ^ n
          = ((1 : ℝ) / 2) ^ n := by
      rw [← mul_pow]
      norm_num
    nlinarith
  nlinarith

/-- A clean second-channel separation estimate is sufficient for one more
greedy survival step.  The constant `37/56 = 2/7 + 3/8` is exactly the sum
of the scaled higher-tail and gap-error budgets. -/
theorem halfGreedy_next_survives_of_secondChannelSeparation
    {n : ℕ}
    (hsurvive :
      greedyMersenneRemainder (1 / 2 : ℝ) n ≤ mersenneTail n)
    (hseparate :
      (1 / 6 : ℝ) + (37 / 56 : ℝ) * ((1 : ℝ) / 2) ^ n
        ≤ |greedyMersenneSecondChannelPhase n - 1 / 3|) :
    greedyMersenneRemainder (1 / 2 : ℝ) (n + 1)
      ≤ mersenneTail (n + 1) := by
  let scale : ℝ := (4 : ℝ) ^ n
  have hscalePos : 0 < scale := by
    dsimp [scale]
    positivity
  have hremNonneg : 0 ≤ mersenneWeightRemainderTail n :=
    mersenneWeightRemainderTail_nonneg n
  have hdecomp :
      greedyMersenneSecondChannelPhase n - 1 / 3
        = scale * greedyMersenneSignedBalance (1 / 2 : ℝ) n
          + scale * mersenneWeightRemainderTail n := by
    have hid := four_pow_mul_signedBalance_eq_secondChannelPhase_sub n
    dsimp [scale]
    linarith
  have htriangle :
      |greedyMersenneSecondChannelPhase n - 1 / 3|
        ≤ scale * |greedyMersenneSignedBalance (1 / 2 : ℝ) n|
          + scale * mersenneWeightRemainderTail n := by
    rw [hdecomp]
    calc
      |scale * greedyMersenneSignedBalance (1 / 2 : ℝ) n
          + scale * mersenneWeightRemainderTail n|
          ≤ |scale * greedyMersenneSignedBalance (1 / 2 : ℝ) n|
              + |scale * mersenneWeightRemainderTail n| := abs_add_le _ _
      _ = scale * |greedyMersenneSignedBalance (1 / 2 : ℝ) n|
            + scale * mersenneWeightRemainderTail n := by
          rw [abs_mul, abs_mul, abs_of_pos hscalePos,
            abs_of_nonneg hremNonneg]
  have hremScaled :
      scale * mersenneWeightRemainderTail n
        ≤ (2 / 7 : ℝ) * ((1 : ℝ) / 2) ^ n := by
    simpa [scale] using four_pow_mul_mersenneWeightRemainderTail_le n
  have hgapScaled :
      scale * mersenneGap (n + 1)
        ≤ (1 / 6 : ℝ) +
            (3 / 8 : ℝ) * ((1 : ℝ) / 2) ^ n := by
    simpa [scale] using four_pow_mul_next_mersenneGap_le n
  have hscaled :
      scale * mersenneGap (n + 1)
        ≤ scale * |greedyMersenneSignedBalance (1 / 2 : ℝ) n| := by
    nlinarith
  have hgap :
      mersenneGap (n + 1)
        ≤ |greedyMersenneSignedBalance (1 / 2 : ℝ) n| :=
    le_of_mul_le_mul_left hscaled hscalePos
  exact (greedyMersenne_next_survives_iff_gap_le_abs_signedBalance
    (greedyMersenneRemainder_nonneg (x := (1 / 2 : ℝ)) (by norm_num) n)
    hsurvive).2 hgap

/-- An all-level second-channel separation theorem would decide the concrete
membership question `1/2 ∈ K`.  All analytic error accounting and the finite
base cases are discharged here; the hypothesis is precisely the remaining
shrinking-hole avoidance obligation. -/
theorem half_mem_mersenneAchievementSet_of_secondChannelSeparation
    (hseparate : ∀ n : ℕ, 0 < n →
      (1 / 6 : ℝ) + (37 / 56 : ℝ) * ((1 : ℝ) / 2) ^ n
        ≤ |greedyMersenneSecondChannelPhase n - 1 / 3|) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply mem_mersenneAchievementSet_of_greedy_survival (by norm_num)
  have hzero :
      greedyMersenneRemainder (1 / 2 : ℝ) 0 ≤ mersenneTail 0 := by
    have htail := mersenneTail_eq_weight_add 0
    have htailNonneg := mersenneTail_nonneg 1
    norm_num [mersenneWeight] at htail ⊢
    linarith
  have hone :
      greedyMersenneRemainder (1 / 2 : ℝ) 1 ≤ mersenneTail 1 := by
    have htail1 := mersenneTail_eq_weight_add 1
    have htail2 := mersenneTail_eq_weight_add 2
    have htail3 := mersenneTail_eq_weight_add 3
    have htailNonneg := mersenneTail_nonneg 4
    norm_num [greedyMersenneRemainder_succ, mersenneWeight] at htail1 htail2 htail3 ⊢
    linarith
  intro n
  cases n with
  | zero => exact hzero
  | succ n =>
      induction n with
      | zero => exact hone
      | succ n ih =>
          exact halfGreedy_next_survives_of_secondChannelSeparation ih
            (hseparate (n + 1) (by omega))

/-- Proof-search form of the half-membership consumer: all levels through six
are checked exactly, and the remaining hypothesis is a decidable statement
about the rational greedy orbit only. -/
theorem half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven
    (hseparate : ∀ n : ℕ, 7 ≤ n → HalfSecondChannelSeparatedRat n) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_secondChannelSeparation
  intro n hn
  apply secondChannelSeparation_of_rat
  by_cases h6 : n ≤ 6
  · exact halfSecondChannelSeparatedRat_of_pos_le_six hn h6
  · exact hseparate n (by omega)

/-- The selected part of the binary skeleton, indexed exactly like
`positiveMersenneSupportValue`. -/
noncomputable def positiveDyadicSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 1)

theorem summable_positiveDyadicSupportIndicator (A : Set ℕ) :
    Summable (fun k : ℕ =>
      Set.indicator A (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 1)) := by
  have hbase : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  have hindicator := hshift.indicator {k : ℕ | k + 1 ∈ A}
  refine hindicator.congr fun k => ?_
  by_cases hk : k + 1 ∈ A
  · simp [hk]
  · simp [hk]

/-- The correction side of the half fixed-point equation. -/
noncomputable def halfCorrectionValue (A : Set ℕ) : ℝ :=
  positiveMersenneSupportValue A - positiveDyadicSupportValue A

/-- The complementary binary side of the half fixed-point equation.  For a
support omitting exponent one this is the sum of the complementary digits
from exponent two onward. -/
noncomputable def halfComplementValue (A : Set ℕ) : ℝ :=
  (1 / 2 : ℝ) - positiveDyadicSupportValue A

/-- The complementary value is genuinely the binary number whose digits from
exponent two onward are the complements of the support digits. -/
theorem halfComplementValue_eq_tsum_complement
    (A : Set ℕ) (hA1 : 1 ∉ A) :
    halfComplementValue A =
      ∑' k : ℕ, Set.indicator Aᶜ
        (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 2) := by
  have hbase : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hfull : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ (k + 2)) := by
    have hshift := (summable_nat_add_iff 2).mpr hbase
    simpa [Nat.add_comm] using hshift
  have hselected : Summable (fun k : ℕ =>
      Set.indicator A (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 2)) := by
    have hshift := (summable_nat_add_iff 1).mpr
      (summable_positiveDyadicSupportIndicator A)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have hselectedShift : positiveDyadicSupportValue A =
      ∑' k : ℕ, Set.indicator A
        (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 2) := by
    unfold positiveDyadicSupportValue
    have hsplit := (summable_positiveDyadicSupportIndicator A).tsum_eq_zero_add
    simpa [Set.indicator_of_notMem hA1, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hsplit
  have hfullSum : (∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 2)) =
      (1 / 2 : ℝ) := by
    calc
      (∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 2))
          = ∑' k : ℕ, ((1 : ℝ) / 2) ^ (1 + k + 1) := by
              apply tsum_congr
              intro k
              congr 1
              omega
      _ = (1 / 2 : ℝ) := by simpa using tsum_half_nat_add_succ 1
  calc
    halfComplementValue A
        = (∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 2))
          - ∑' k : ℕ, Set.indicator A
              (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 2) := by
            rw [halfComplementValue, hselectedShift, hfullSum]
    _ = ∑' k : ℕ, (((1 : ℝ) / 2) ^ (k + 2)
          - Set.indicator A (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 2)) := by
            rw [hfull.tsum_sub hselected]
    _ = ∑' k : ℕ, Set.indicator Aᶜ
          (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 2) := by
            apply tsum_congr
            intro k
            by_cases hk : k + 2 ∈ A
            · simp [hk]
            · simp [hk]

/-- Exact correction/complement reframe of a value-`1/2` support. -/
theorem positiveMersenneSupportValue_eq_half_iff_correction_eq_complement
    (A : Set ℕ) :
    positiveMersenneSupportValue A = (1 / 2 : ℝ) ↔
      halfCorrectionValue A = halfComplementValue A := by
  unfold halfCorrectionValue halfComplementValue
  constructor <;> intro h <;> linarith

/-- An all-level prefix-forcing witness.  The interval
`[correctionLower k, correctionUpper k]` is the complete correction enclosure
at macrostep `k`; `interval_trapped` puts that whole enclosure in one dyadic
cylinder.  The complementary binary value lies in the same cylinder, and the
cylinder depths tend to infinity.

The finite-word construction that produces these data is deliberately kept
outside the structure: different evaluators may supply the same analytic
certificate without creating a second achievement-set model. -/
structure HalfPrefixForcingChain (A : Set ℕ) where
  depth : ℕ → ℕ
  cellLeft : ℕ → ℝ
  correctionLower : ℕ → ℝ
  correctionUpper : ℕ → ℝ
  correction_mem : ∀ k : ℕ,
    halfCorrectionValue A ∈ Set.Icc (correctionLower k) (correctionUpper k)
  interval_trapped : ∀ k : ℕ,
    Set.Icc (correctionLower k) (correctionUpper k) ⊆
      Set.Icc (cellLeft k) (cellLeft k + ((1 : ℝ) / 2) ^ (depth k))
  complement_mem : ∀ k : ℕ,
    halfComplementValue A ∈
      Set.Icc (cellLeft k) (cellLeft k + ((1 : ℝ) / 2) ^ (depth k))
  depth_tendsto : Tendsto depth atTop atTop

/-- Two values trapped in the same unbounded sequence of dyadic cylinders
are equal.  This is the analytic coinduction step: every finite macrostep
contributes a genuine error bound, and only unboundedness is asymptotic. -/
theorem HalfPrefixForcingChain.correction_eq_complement
    {A : Set ℕ} (chain : HalfPrefixForcingChain A) :
    halfCorrectionValue A = halfComplementValue A := by
  have hcorrectionCell : ∀ k : ℕ,
      halfCorrectionValue A ∈
        Set.Icc (chain.cellLeft k)
          (chain.cellLeft k + ((1 : ℝ) / 2) ^ (chain.depth k)) := by
    intro k
    exact chain.interval_trapped k (chain.correction_mem k)
  have hdist : ∀ k : ℕ,
      |halfCorrectionValue A - halfComplementValue A|
        ≤ ((1 : ℝ) / 2) ^ (chain.depth k) := by
    intro k
    rcases hcorrectionCell k with ⟨hBL, hBR⟩
    rcases chain.complement_mem k with ⟨hCL, hCR⟩
    have hpowNonneg : 0 ≤ ((1 : ℝ) / 2) ^ (chain.depth k) := by positivity
    rw [abs_le]
    constructor <;> linarith
  have hpow : Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ (chain.depth k))
      atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      chain.depth_tendsto
  have hconstZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hconstDist : Tendsto
      (fun _ : ℕ => |halfCorrectionValue A - halfComplementValue A|)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hconstZero hpow
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall hdist)
  have hzero : |halfCorrectionValue A - halfComplementValue A| = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconstDist
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- Unbounded prefix forcing constructs an exact value-`1/2` support.  The
normalization hypotheses make the support genuinely positive-indexed and
give the intended complementary-digit interpretation. -/
theorem half_mem_mersenneAchievementSet_of_prefixForcingChain
    (A : Set ℕ) (hA0 : 0 ∉ A) (_hA1 : 1 ∉ A)
    (chain : HalfPrefixForcingChain A) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  refine ⟨A, hA0, ?_⟩
  exact (positiveMersenneSupportValue_eq_half_iff_correction_eq_complement A).2
    chain.correction_eq_complement |>.symm

/-- An interval of width at most one crosses at most one integer.  Applied
after scaling a correction interval by `4^N`, this isolates the unique
boundary whose two-adic divisibility controls the forcing defect. -/
theorem integer_crossing_unique {x τ : ℝ} (hτ : τ ≤ 1)
    {m₁ m₂ : ℤ}
    (hm₁L : x < (m₁ : ℝ)) (hm₁R : (m₁ : ℝ) < x + τ)
    (hm₂L : x < (m₂ : ℝ)) (hm₂R : (m₂ : ℝ) < x + τ) :
    m₁ = m₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstep : m₁ + 1 ≤ m₂ := by omega
    have hstepR : (m₁ : ℝ) + 1 ≤ (m₂ : ℝ) := by exact_mod_cast hstep
    linarith
  · have hstep : m₂ + 1 ≤ m₁ := by omega
    have hstepR : (m₂ : ℝ) + 1 ≤ (m₁ : ℝ) := by exact_mod_cast hstep
    linarith

/-- Cancelling an explicit power of two from a boundary on the `4^N` grid.
When `q` is odd and `v` is the exact two-adic valuation of the numerator,
the right-hand denominator has the reduced dyadic depth `2*N-v`. -/
theorem dyadicBoundary_cancel_powTwo (N v q : ℕ) (hv : v ≤ 2 * N) :
    (((2 ^ v * q : ℕ) : ℝ) / (4 : ℝ) ^ N)
      = (q : ℝ) / (2 : ℝ) ^ (2 * N - v) := by
  have hpow : (4 : ℝ) ^ N = (2 : ℝ) ^ (2 * N) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hadd : v + (2 * N - v) = 2 * N := Nat.add_sub_of_le hv
  rw [hpow, ← hadd, pow_add]
  push_cast
  field_simp
  congr 2
  omega

/-- The exact growth criterion once a crossed boundary has forcing depth
`2*N-v-1`: strict extension beyond `N` is equivalent to excluding
`v ≥ N-1`. -/
theorem crossedBoundary_forceDepth_gt_iff
    {N v : ℕ} (hN : 1 < N) :
    N < 2 * N - v - 1 ↔ v < N - 1 := by
  omega

end Erdos257PeriodNoncollapse
