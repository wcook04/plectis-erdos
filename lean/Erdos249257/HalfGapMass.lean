import Erdos249257.GreedyAchievementSet

/-!
# Total Mersenne gap mass beyond a finite level

`GreedyAchievementSet` proves the per-level gap asymptotic
`w(n) - T(n) = (2/3)·4⁻ⁿ + O(8⁻ⁿ)` (`mersenneGap_isBigOWith`, with the
explicit bound `mersenneGap_asymptotic_bound`).  That controls each level
separately and says nothing about the levels taken together.

This file sums it.  The gap sequence is summable, and the mass strictly
beyond level `N` admits the explicit geometric bound

  `∑_{n > N} (w(n) - T(n)) ≤ (2/9)·4⁻ᴺ + (3/7)·8⁻ᴺ`.

Every step is a geometric consequence of `mersenneGap_asymptotic_bound`
together with the existing `tsum_quarter_nat_add_succ` and
`tsum_eighth_nat_add_succ`; no new arithmetic input is used.

This bounds gap mass only.  It is not a statement about which reals the
greedy run reaches, it does not certify membership or nonmembership of any
point, and in particular it says nothing about `1/2`.  Nothing here settles
Erdős problem #257.

No novelty or priority claim is made for the theorems in this file.
-/

namespace Erdos249257

open Filter Topology

-- `mersenneGap` and `mersenneGap_pos` are already declared publicly in
-- `Erdos249257.GreedyAchievementSet` (same definition, same statement); this
-- file builds on those rather than redeclaring them.

theorem mersenneGap_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ mersenneGap n :=
  (mersenneGap_pos hn).le

/-- The landed per-level asymptotic, read as a one-sided upper bound. -/
theorem mersenneGap_le {n : ℕ} (hn : 0 < n) :
    mersenneGap n ≤ (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n + 3 * ((1 : ℝ) / 8) ^ n := by
  have h := mersenneGap_asymptotic_bound hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hpow : (0 : ℝ) ≤ ((1 : ℝ) / 8) ^ n := by positivity
  rw [abs_of_nonneg hpow] at h
  have h2 := (abs_le.mp h).2
  unfold mersenneGap
  linarith

/-! ## The geometric envelope, shifted past level `N` -/

theorem summable_quarter_env (N : ℕ) :
    Summable (fun k : ℕ => (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ (N + k + 1)) := by
  have hbase := summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 : ℝ) / 4 < 1)
  have hshift := (summable_nat_add_iff (N + 1)).mpr hbase
  have hmul := hshift.mul_left (2 / 3 : ℝ)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmul

theorem summable_eighth_env (N : ℕ) :
    Summable (fun k : ℕ => (3 : ℝ) * ((1 : ℝ) / 8) ^ (N + k + 1)) := by
  have hbase := summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 : ℝ) / 8 < 1)
  have hshift := (summable_nat_add_iff (N + 1)).mpr hbase
  have hmul := hshift.mul_left (3 : ℝ)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmul

/-- **The gap sequence is summable past any level.** -/
theorem summable_mersenneGap_shift (N : ℕ) :
    Summable (fun k : ℕ => mersenneGap (N + k + 1)) :=
  Summable.of_nonneg_of_le
    (fun k => mersenneGap_nonneg (by omega))
    (fun k => mersenneGap_le (by omega))
    ((summable_quarter_env N).add (summable_eighth_env N))

/-- **The gap sequence is summable.** -/
theorem summable_mersenneGap_succ : Summable (fun k : ℕ => mersenneGap (k + 1)) := by
  simpa using summable_mersenneGap_shift 0

/-- **Total gap mass beyond level `N`.**  Summing the landed per-level bound
`mersenneGap_asymptotic_bound` geometrically: the whole remaining gap mass
after exponent `N` is `O(4⁻ᴺ)`, with explicit constants. -/
theorem mersenneGap_tail_le (N : ℕ) :
    ∑' k : ℕ, mersenneGap (N + k + 1)
      ≤ (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N + (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N := by
  have h4 := summable_quarter_env N
  have h8 := summable_eighth_env N
  calc
    ∑' k : ℕ, mersenneGap (N + k + 1)
        ≤ ∑' k : ℕ, ((2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ (N + k + 1)
            + 3 * ((1 : ℝ) / 8) ^ (N + k + 1)) :=
          (summable_mersenneGap_shift N).tsum_le_tsum
            (fun k => mersenneGap_le (by omega)) (h4.add h8)
    _ = (∑' k : ℕ, (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ (N + k + 1))
          + ∑' k : ℕ, (3 : ℝ) * ((1 : ℝ) / 8) ^ (N + k + 1) := h4.tsum_add h8
    _ = (2 / 3 : ℝ) * (∑' k : ℕ, ((1 : ℝ) / 4) ^ (N + k + 1))
          + (3 : ℝ) * ∑' k : ℕ, ((1 : ℝ) / 8) ^ (N + k + 1) := by
          rw [tsum_mul_left, tsum_mul_left]
    _ = (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N + (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N := by
          rw [tsum_quarter_nat_add_succ, tsum_eighth_nat_add_succ]
          ring

/-- The remaining gap mass tends to zero. -/
theorem tendsto_mersenneGap_tail_zero :
    Tendsto (fun N : ℕ => ∑' k : ℕ, mersenneGap (N + k + 1)) atTop (nhds 0) := by
  have hlo : ∀ N : ℕ, (0 : ℝ) ≤ ∑' k : ℕ, mersenneGap (N + k + 1) := by
    intro N
    exact tsum_nonneg fun k => mersenneGap_nonneg (by omega)
  have hq : Tendsto (fun N : ℕ => (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N) atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 : ℝ) / 4 < 1)
    simpa using this.const_mul (2 / 9 : ℝ)
  have he : Tendsto (fun N : ℕ => (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N) atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 : ℝ) / 8 < 1)
    simpa using this.const_mul (3 / 7 : ℝ)
  have hsum : Tendsto
      (fun N : ℕ => (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N + (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N)
      atTop (nhds 0) := by
    simpa using hq.add he
  exact squeeze_zero hlo mersenneGap_tail_le hsum

end Erdos249257
