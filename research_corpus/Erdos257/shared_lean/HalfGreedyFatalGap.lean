import Erdos257PeriodNoncollapse.GreedyAchievementSet

/-!
# The sharp Mersenne fatal gap: a one-third reduction of the half-greedy obstruction

Fix the Mersenne weights `x k = 1 / (2 ^ k - 1)` and the tails `T k = ∑_{j ≥ k} x j`.  The
half-greedy process for `1 / 2` skips rank `k` when the residual `ρ` satisfies `ρ < x k`, and
after a skip completion is impossible whenever `ρ > T (k + 1)` — the skipped rank is gone
forever, so the available mass is the tail *strictly after* `k`.  The reverse implication is
not asserted: `ρ ≤ T (k + 1)` clears this total-mass obstruction but does not by itself represent
`ρ` by the remaining weights.  Since `x k > T (k + 1)` for every `k`, the interval
`(T (k+1), x k)` is nevertheless a genuine **fatal gap**: a skipped residual landing strictly
inside it can never be completed.

Earlier work in this development ruled out this tail-mass obstruction through the *dyadic* bound
`ρ ≤ 2 ^ (-k)`.  That test is strictly too strong, because `T (k + 1) > 2 ^ (-k)`.  Writing a
residual in lowest terms as `ρ = u / (2 * L)` with `u`, `L` odd and setting

`a := 2 * L - (2 ^ k - 1) * u`   (so `0 < a` is exactly the skip condition),

the dyadic test is `u ≤ a`, whereas the tail-mass fatal threshold is governed by

`θ k := 1 / T (k + 1) - (2 ^ k - 1)`,

and the main theorem here is that `θ k < 2 / 3` for every `k ≥ 1`.  Consequently `2 * u ≤ 3 * a`
already certifies that the residual is below the available tail mass: this obstruction is
**one third smaller** than the dyadic test reports, and the entire content of that improvement
is the inequality `2 * 2 ^ k > 3`.

The key arithmetic identity, with `t = 2 ^ k`, is exact:

`21 * t ^ 2 * (3 * t - 1) + 7 * t * (3 * t - 1) + 3 * (3 * t - 1) = 63 * t ^ 3 + 2 * t - 3`

so the three-channel Lambert lower bound for `T (k + 1)` beats `3 / (3 * t - 1)` with margin
exactly `2 * t - 3`.  Three channels is the exact threshold: two channels fail by exactly `1`,
since `9 * 4 ^ k - 1 > 9 * 4 ^ k` is false.

## Scope

These are total-mass statements about a single skipped rank.  They do **not** assert that every
residual below the remaining tail is representable, that the actual half-greedy orbit avoids the
fatal gap, or that `1 / 2` belongs to the achievement set.  The arithmetic core keeps the
analytic input explicit as `mersenneTailLB3 k ≤ T`.  The final section discharges that input for
the actual Mersenne tail using the existing exact three-channel tail expansion; it does not
construct a completion or prove that the orbit avoids the remaining fatal region.
-/

namespace Erdos257PeriodNoncollapse
namespace HalfGreedyFatalGap

/-- The three-channel Lambert lower bound for the Mersenne tail `T (k + 1)`.

`T (k + 1) = ∑_{v ≥ 1} 2 ^ (-k * v) / (2 ^ v - 1)`; truncating that expansion after `v = 3`
gives this rational function of `t = 2 ^ k`, namely `1/t + 1/(3 * t ^ 2) + 1/(7 * t ^ 3)`
(equivalently `1 / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k)`). -/
noncomputable def mersenneTailLB3 (k : ℕ) : ℝ :=
  1 / 2 ^ k + 1 / (3 * (2 ^ k) ^ 2) + 1 / (7 * (2 ^ k) ^ 3)

private lemma two_le_two_pow {k : ℕ} (hk : 1 ≤ k) : (2 : ℝ) ≤ 2 ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  rw [pow_add, pow_one]
  linarith

/-- **The key lemma.**  The three-channel tail bound strictly exceeds `3 / (3 * 2 ^ k - 1)`, and
the entire content of the inequality is `2 * 2 ^ k > 3`.

The exact difference is `(2 * t - 3) / (21 * t ^ 3 * (3 * t - 1))` with `t = 2 ^ k`, so the
margin is exactly `2 * 2 ^ k - 3`. -/
theorem three_div_lt_mersenneTailLB3 {k : ℕ} (hk : 1 ≤ k) :
    3 / (3 * 2 ^ k - 1 : ℝ) < mersenneTailLB3 k := by
  have ht : (2 : ℝ) ≤ 2 ^ k := two_le_two_pow hk
  set t : ℝ := 2 ^ k with hts
  have ht0 : (0 : ℝ) < t := by linarith
  have ht0' : t ≠ 0 := ne_of_gt ht0
  have hden : (0 : ℝ) < 3 * t - 1 := by linarith
  -- Collapse the three channels onto the common denominator `21 * t ^ 3`.
  have hRHS : mersenneTailLB3 k = (21 * t ^ 2 + 7 * t + 3) / (21 * t ^ 3) := by
    show (1 / t + 1 / (3 * t ^ 2) + 1 / (7 * t ^ 3)) = _
    field_simp
    ring
  rw [hRHS, div_lt_div_iff₀ hden (by positivity)]
  -- Goal: `3 * (21 * t ^ 3) < (21 * t ^ 2 + 7 * t + 3) * (3 * t - 1)`, i.e.
  -- `63 * t ^ 3 < 63 * t ^ 3 + 2 * t - 3`.  The whole content is `2 * t > 3`.
  nlinarith [ht, ht0]

section SkipSafety

/-!
### The sharp skip-safety criterion

A half-greedy residual in lowest terms is `ρ = u / (2 * L)` with `u` and `L` odd.  Rank `k` is
skipped exactly when `(2 ^ k - 1) * u < 2 * L`.  We record the decomposition in the
subtraction-free form `2 ^ k * u + a = 2 * L + u`, which is equivalent to
`(2 ^ k - 1) * u + a = 2 * L` but avoids truncated natural subtraction; `0 < a` is the skip
condition.
-/

variable {k u L a : ℕ}

/-- **Sharp tail-mass safety.**  If `2 * u ≤ 3 * a` then the skipped residual `u / (2 * L)`
lies strictly below the three-channel tail bound, hence below the true tail.  This rules out the
total-mass fatality; it does not construct a representation by the remaining weights.

This is the one-third improvement.  The dyadic criterion demands `u ≤ a`; this demands only
`2 * u ≤ 3 * a`. -/
theorem skipSafe_of_two_mul_le_three_mul
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTailLB3 k := by
  have ht : (2 : ℝ) ≤ 2 ^ k := two_le_two_pow hk
  have hcast : (2 : ℝ) ^ k * u + a = 2 * L + u := by exact_mod_cast hdecomp
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hsharp0 : (2 : ℝ) * u ≤ 3 * a := by exact_mod_cast hsharp
  set t : ℝ := 2 ^ k with hts
  have ht0 : (0 : ℝ) < t := by linarith
  have hden : (0 : ℝ) < 3 * t - 1 := by linarith
  -- The skip condition `0 < a` together with `2 ≤ t` forces `2 * L > 0`.
  have hL0 : (0 : ℝ) < 2 * L := by nlinarith [hcast]
  -- `2 * u ≤ 3 * a` is *exactly* `(3 * t - 1) * u ≤ 6 * L`, after substituting `hcast`.
  have hlin : 3 * (t * u) - u ≤ 6 * L := by linarith [hcast, hsharp0]
  have hkey : (3 * t - 1) * u ≤ 6 * L := by nlinarith [hlin]
  have hrho : (u : ℝ) / (2 * L) ≤ 3 / (3 * t - 1) := by
    rw [div_le_div_iff₀ hL0 hden]
    linarith [hkey]
  exact lt_of_le_of_lt hrho (three_div_lt_mersenneTailLB3 hk)

/-- **Unit numerators are never tail-mass fatal.**  When `u = 1` the skip condition alone
forces `a ≥ 1`, hence `3 * a ≥ 3 > 2 = 2 * u`.

This replaces any bespoke unit-residual argument: the whole proof is that a positive integer is
at least `1`, and `3 > 2`. -/
theorem unitNumerator_skipSafe
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTailLB3 k := by
  have h := skipSafe_of_two_mul_le_three_mul (k := k) (u := 1) (L := L) (a := a)
    hk one_pos ha hdecomp (by omega)
  simpa using h

/-- **The fatal converse.**  A skipped residual that the remaining tail cannot cover must satisfy
`3 * a < 2 * u`.  Every fatal configuration therefore lives strictly inside the two-thirds
cell. -/
theorem three_mul_lt_two_mul_of_fatal
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    3 * a < 2 * u := by
  by_contra hcon
  push_neg at hcon
  have hsafe := skipSafe_of_two_mul_le_three_mul hk hu ha hdecomp hcon
  exact absurd (lt_of_lt_of_le hsafe hT) (not_lt.mpr hfatal.le)

/-- Fatality forces `2 ≤ u`: the residual `1 / (2 * L)` is never fatal.

This is the unconditional form.  It is genuinely all that follows from `3 * a < 2 * u` over the
integers: `u = 2`, `a = 1` satisfies `3 * a < 2 * u`, so `3 ≤ u` needs the oddness of `u`. -/
theorem two_le_of_fatal
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    2 ≤ u := by
  have h := three_mul_lt_two_mul_of_fatal hk hu ha hdecomp T hT hfatal
  omega

/-- Fatality forces `3 ≤ u` once `u` is odd — which every half-greedy residual numerator is.

The oddness hypothesis is load-bearing, not decoration: without it `u = 2` survives. -/
theorem three_le_of_fatal_of_odd
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a) (hodd : Odd u)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    3 ≤ u := by
  have h := three_mul_lt_two_mul_of_fatal hk hu ha hdecomp T hT hfatal
  obtain ⟨m, hm⟩ := hodd
  omega

end SkipSafety

section Comparison

/-!
### The sharp criterion strictly contains the dyadic one

Dyadic safety `ρ ≤ 2 ^ (-k)` is exactly `u ≤ a`.  The sharp criterion is `2 * u ≤ 3 * a`.  The
first implies the second, and the containment is strict: the cell `2 * u ≤ 3 * a < 3 * u` is
newly certified safe.  That cell is exactly the one third of the dyadic obstruction which is not
a real obstruction at all.
-/

/-- Dyadic safety implies sharp safety. -/
theorem sharp_of_dyadic {u a : ℕ} (h : u ≤ a) : 2 * u ≤ 3 * a := by omega

/-- The one-third gain is nonempty: `u = 3`, `a = 2` is sharp-safe but not dyadically safe. -/
theorem sharp_strictly_stronger : ∃ u a : ℕ, 0 < u ∧ 2 * u ≤ 3 * a ∧ ¬ u ≤ a :=
  ⟨3, 2, by norm_num, by norm_num, by norm_num⟩

end Comparison

section ActualMersenneTail

/-!
### Discharging the analytic socket for the actual tail

`GreedyAchievementSet` already expands `mersenneTail k` into its first two geometric channels
plus a positive remainder tail, and proves that the third channel is a strict lower bound for
that remainder.  The next theorem composes those declarations with the arithmetic core above.
-/

/-- The actual Mersenne tail strictly dominates the three-channel lower bound. -/
theorem mersenneTailLB3_lt_mersenneTail (k : ℕ) :
    mersenneTailLB3 k < mersenneTail k := by
  rw [mersenneTail_eq_two_channels_add_remainderTail]
  have hthird := one_seventh_eighth_pow_lt_mersenneWeightRemainderTail k
  have hfour : (4 : ℝ) ^ k = 2 ^ (k * 2) := by
    calc
      (4 : ℝ) ^ k = ((2 : ℝ) ^ 2) ^ k := by norm_num
      _ = 2 ^ (2 * k) := by rw [← pow_mul]
      _ = 2 ^ (k * 2) := by congr 1 <;> omega
  have height : (8 : ℝ) ^ k = 2 ^ (k * 3) := by
    calc
      (8 : ℝ) ^ k = ((2 : ℝ) ^ 3) ^ k := by norm_num
      _ = 2 ^ (3 * k) := by rw [← pow_mul]
      _ = 2 ^ (k * 3) := by congr 1 <;> omega
  unfold mersenneTailLB3
  norm_num [div_pow, hfour, height, ← pow_mul] at hthird ⊢
  nlinarith

/-- Sharp safety against exceeding the actual future Mersenne mass. -/
theorem skipSafe_actualTail_of_two_mul_le_three_mul
    {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTail k :=
  lt_trans
    (skipSafe_of_two_mul_le_three_mul hk hu ha hdecomp hsharp)
    (mersenneTailLB3_lt_mersenneTail k)

/-- Unit-numerator skips lie strictly below the actual future Mersenne mass. -/
theorem unitNumerator_skipSafe_actualTail
    {k L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTail k :=
  lt_trans (unitNumerator_skipSafe hk ha hdecomp)
    (mersenneTailLB3_lt_mersenneTail k)

/-- A skip whose residual exceeds the actual Mersenne tail lies in the strict region
`3a < 2u`. -/
theorem three_mul_lt_two_mul_of_actualTail_fatal
    {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hfatal : mersenneTail k < (u : ℝ) / (2 * L)) :
    3 * a < 2 * u :=
  three_mul_lt_two_mul_of_fatal hk hu ha hdecomp (mersenneTail k)
    (mersenneTailLB3_lt_mersenneTail k).le hfatal

/-- Actual-tail fatality forces an odd residual numerator to be at least three. -/
theorem three_le_of_actualTail_fatal_of_odd
    {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a) (hodd : Odd u)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hfatal : mersenneTail k < (u : ℝ) / (2 * L)) :
    3 ≤ u :=
  three_le_of_fatal_of_odd hk hu ha hodd hdecomp (mersenneTail k)
    (mersenneTailLB3_lt_mersenneTail k).le hfatal

#print axioms mersenneTailLB3_lt_mersenneTail
#print axioms skipSafe_actualTail_of_two_mul_le_three_mul
#print axioms unitNumerator_skipSafe_actualTail
#print axioms three_mul_lt_two_mul_of_actualTail_fatal
#print axioms three_le_of_actualTail_fatal_of_odd

end ActualMersenneTail

end HalfGreedyFatalGap
end Erdos257PeriodNoncollapse
