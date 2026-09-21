import Erdos249257.CertificateKernel
import Erdos249257.PrimitiveRationalGapSupply
import Erdos249257.GeometricCoprimality

/-! Paper-form restatements of four long-paper environments:

* `prop:D1D2-inv` — the two general irrationality criteria, with the two
  rational-error lower bounds that prove them, and the base-power dilation
  form as a sufficient condition;
* `prop:D7-inv` — the Lambert identities `L(μ) = 1/2`, `L(φ) = 2`, `L(1) = E`
  and `L(φ*μ) = S`, plus the index bridge;
* `prop:D9-inv` — the rational gap bound, the resulting denominator lower
  bound, the equivalence "these bounds tend to infinity iff `q_N ε_N → 0`",
  the subsequence consequence, and the vacuity of the plain dyadic instance;
* `prop:C1-inv` — the visible-pair count on the antidiagonal, the boundary
  pair at `n = 1`, and the coprime-pair expression `S - 1/2`.

Here `S = ∑_{n≥0} φ(n)/2^n` and `L(f) = ∑_{n≥1} f(n)/(2^n - 1)`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257

/-! ### `prop:D1D2-inv` — two general irrationality criteria -/

/-- The first error bound: distinct rationals are at least `1/(b q)` apart,
where `b` and `q` are their reduced denominators. -/
theorem one_div_den_mul_den_le_abs_diff {x u : ℚ} (hne : x ≠ u) :
    (1 : ℝ) / ((x.den : ℝ) * (u.den : ℝ)) ≤ |(x : ℝ) - (u : ℝ)| :=
  one_div_den_mul_den_le_abs_sub hne

/-- The second error bound: for a rational `x = a/b` in lowest terms and
integers `m, z`, a nonzero error `m x - z` is at least `1/b`. -/
theorem one_div_den_le_abs_int_combination (p : ℚ) (m z : ℤ)
    (hne : (m : ℝ) * (p : ℝ) - (z : ℝ) ≠ 0) :
    (1 : ℝ) / (p.den : ℝ) ≤ |(m : ℝ) * (p : ℝ) - (z : ℝ)| := by
  have hdenpos : (0 : ℝ) < (p.den : ℝ) := by exact_mod_cast p.den_pos
  have hden0 : (p.den : ℝ) ≠ 0 := hdenpos.ne'
  have hA : ((m * p.num - z * p.den : ℤ) : ℝ)
      = (p.den : ℝ) * ((m : ℝ) * (p : ℝ) - (z : ℝ)) := by
    rw [Rat.cast_def]
    field_simp
    push_cast
    ring
  have habs : |((m * p.num - z * p.den : ℤ) : ℝ)|
      = (p.den : ℝ) * |(m : ℝ) * (p : ℝ) - (z : ℝ)| := by
    rw [hA, abs_mul, abs_of_pos hdenpos]
  have hAne : (m * p.num - z * p.den : ℤ) ≠ 0 := by
    intro h0
    apply hne
    have h1 : ((m * p.num - z * p.den : ℤ) : ℝ) = 0 := by rw [h0]; norm_num
    rw [hA] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hden0
    · exact h2
  have hone : (1 : ℝ) ≤ |((m * p.num - z * p.den : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hAne
  rw [habs] at hone
  have hcomm : |(m : ℝ) * (p : ℝ) - (z : ℝ)| * (p.den : ℝ)
      = (p.den : ℝ) * |(m : ℝ) * (p : ℝ) - (z : ℝ)| := mul_comm _ _
  rw [div_le_iff₀ hdenpos, hcomm]
  exact hone

/-- **First criterion.**  A sequence of reduced fractions `u_j` with
`u_j ≠ x` eventually and `den(u_j)·|x - u_j| → 0` forces `x` irrational. -/
theorem irrational_of_den_mul_error_tendsto_zero {x : ℝ} {u : ℕ → ℚ}
    (hne : ∀ᶠ k in Filter.atTop, ((u k : ℚ) : ℝ) ≠ x)
    (h0 : Filter.Tendsto (fun k => ((u k).den : ℝ) * |x - ((u k : ℚ) : ℝ)|)
      Filter.atTop (nhds 0)) :
    Irrational x :=
  irrational_of_den_mul_abs_sub_tendsto_zero hne h0

/-- **Second criterion.**  If for every integer `Q ≥ 1` there are `m, z ∈ ℤ`
with `0 < |m x - z| < 1/Q`, then `x` is irrational. -/
theorem irrational_of_dirichlet_gap {x : ℝ}
    (h : ∀ Q : ℤ, 1 ≤ Q → ∃ m z : ℤ,
      0 < |(m : ℝ) * x - (z : ℝ)| ∧ |(m : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ)) :
    Irrational x := by
  rintro ⟨p, rfl⟩
  obtain ⟨m, z, hpos, hlt⟩ := h (p.den : ℤ) (by exact_mod_cast p.den_pos)
  have hne : (m : ℝ) * ((p : ℚ) : ℝ) - (z : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hge := one_div_den_le_abs_int_combination p m z hne
  have hcast : (((p.den : ℤ)) : ℝ) = (p.den : ℝ) := by push_cast; ring
  rw [hcast] at hlt
  linarith

/-- The base-power restriction `m = b₀^n` is a *sufficient* condition: it
implies the second criterion's hypothesis, hence irrationality. -/
theorem irrational_of_basePower_dilation {x : ℝ} (b₀ : ℕ)
    (h : ∀ Q : ℤ, 1 ≤ Q → ∃ n : ℕ, ∃ z : ℤ,
      0 < |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| ∧
        |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ)) :
    Irrational x := by
  refine irrational_of_dirichlet_gap ?_
  intro Q hQ
  obtain ⟨n, z, h1, h2⟩ := h Q hQ
  have hcast : (((b₀ ^ n : ℕ) : ℤ) : ℝ) = ((b₀ ^ n : ℕ) : ℝ) := by
    push_cast
    ring
  exact ⟨((b₀ ^ n : ℕ) : ℤ), z, by rw [hcast]; exact h1, by rw [hcast]; exact h2⟩

/-! ### `prop:D7-inv` — Lambert identities involving `S` -/

/-- **The four Lambert identities.**  `L(μ) = 1/2`, `L(φ) = 2`, `L(1) = E`
(the Erdős–Borwein constant in its divisor-count form) and `L(φ*μ) = S`. -/
theorem lambert_ladder_values :
    (∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
        / ((2 : ℝ) ^ (d : ℕ) - 1) = 1 / 2) ∧
      (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) = 2) ∧
      (∑' k : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (k + 1) - 1)
        = ∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (2 : ℝ) ^ (m + 1)) ∧
      (∑' d : ℕ+, ((MersenneLambertLadder.primWeight (d : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (d : ℕ) - 1)
        = ∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) :=
  ⟨tsum_moebius_div_two_pow_sub_one_eq_half,
    tsum_totient_div_two_pow_sub_one_eq_two,
    erdosBorwein_constant_lambert_identity,
    tsum_primWeight_div_two_pow_sub_one_eq_totient_series⟩

/-- The weight in the last identity is `A = φ * μ`: its divisor sum is `φ`. -/
theorem primWeight_divisor_sum (n : ℕ) :
    ∑ e ∈ n.divisors, MersenneLambertLadder.primWeight e = (Nat.totient n : ℤ) :=
  MersenneLambertLadder.sum_divisors_primWeight n

/-- The index bridge between the two conventions for `S`. -/
theorem totient_series_index_bridge :
    (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) :=
  tsum_totient_div_pow_two_eq_pnat_half_pow

/-! ### `prop:D9-inv` — a general rational gap bound -/

/-- **A general rational gap bound.**  If `a/b < c/d` are reduced, then
`1/(bd) ≤ c/d - a/b`. -/
theorem rational_gap_lower_bound {lo hi : ℚ} (hlt : lo < hi) :
    (1 : ℝ) / ((hi.den : ℝ) * (lo.den : ℝ)) ≤ (hi : ℝ) - (lo : ℝ) := by
  have h := positive_rational_difference_lower_bound hlt
  simpa using h

/-- **The denominator lower bound.**  If `S = a/b` and `u = p_N/q_N < S` is a
reduced approximation with positive error at most `ε`, then
`b ≥ 1/(q_N ε)`. -/
theorem den_lower_bound_of_positive_error {S u : ℚ} (hlt : u < S) {ε : ℝ}
    (herr : (S : ℝ) - (u : ℝ) ≤ ε) :
    (1 : ℝ) / ((u.den : ℝ) * ε) ≤ (S.den : ℝ) := by
  have hgap := rational_gap_lower_bound hlt
  have hu : (0 : ℝ) < (u.den : ℝ) := by exact_mod_cast u.den_pos
  have hSd : (0 : ℝ) < (S.den : ℝ) := by exact_mod_cast S.den_pos
  have hprod : (0 : ℝ) < (S.den : ℝ) * (u.den : ℝ) := mul_pos hSd hu
  have hεpos : (0 : ℝ) < ε := by
    have h1 : (0 : ℝ) < 1 / ((S.den : ℝ) * (u.den : ℝ)) := by positivity
    linarith
  have h2 : (1 : ℝ) / ((S.den : ℝ) * (u.den : ℝ)) ≤ ε := le_trans hgap herr
  rw [div_le_iff₀ hprod] at h2
  have heq : (S.den : ℝ) * ((u.den : ℝ) * ε) = ε * ((S.den : ℝ) * (u.den : ℝ)) := by
    ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (u.den : ℝ) * ε), heq]
  exact h2

/-- **The bounds tend to infinity precisely when `q_N ε_N → 0`.** -/
theorem denominator_bound_tendsto_atTop_iff {f : ℕ → ℝ} (hpos : ∀ N, 0 < f N) :
    Filter.Tendsto (fun N => 1 / f N) Filter.atTop Filter.atTop ↔
      Filter.Tendsto f Filter.atTop (nhds 0) := by
  constructor
  · intro hT
    have h2 := tendsto_inv_atTop_zero.comp hT
    have heq : ((fun r : ℝ => r⁻¹) ∘ fun N => 1 / f N) = f := by
      funext N
      simp
    rwa [heq] at h2
  · intro hT
    have hw : Filter.Tendsto f Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hT, ?_⟩
      filter_upwards with N
      exact Set.mem_Ioi.mpr (hpos N)
    have h2 := tendsto_inv_nhdsGT_zero.comp hw
    have heq : ((fun r : ℝ => r⁻¹) ∘ f) = fun N => 1 / f N := by
      funext N
      simp
    rwa [heq] at h2

/-- **A subsequence with that property contradicts a fixed `b`.**  If the
reduced approximations `u_j` never hit `x`, their errors are at most `ε_j`,
and `den(u_j)·ε_j → 0`, then `x` is irrational. -/
theorem irrational_of_den_mul_error_product_tendsto_zero
    {x : ℝ} {u : ℕ → ℚ} {ε : ℕ → ℝ}
    (hne : ∀ j, ((u j : ℚ) : ℝ) ≠ x)
    (herr : ∀ j, |x - ((u j : ℚ) : ℝ)| ≤ ε j)
    (h0 : Filter.Tendsto (fun j => ((u j).den : ℝ) * ε j) Filter.atTop (nhds 0)) :
    Irrational x := by
  refine irrational_of_den_mul_error_tendsto_zero (by filter_upwards with j; exact hne j) ?_
  refine squeeze_zero (fun j => by positivity) (fun j => ?_) h0
  exact mul_le_mul_of_nonneg_left (herr j) (by positivity)

/-- **The plain dyadic instance is vacuous.**  With `q_N = 2^N` and
`ε_N = (N+2)2^{-N}` the bound reads `b ≥ 1/(N+2)`, which is at most `1`. -/
theorem dyadic_prefix_denominator_bound_vacuous (N : ℕ) :
    (1 : ℝ) / ((2 : ℝ) ^ N * (((N : ℝ) + 2) / (2 : ℝ) ^ N)) = 1 / ((N : ℝ) + 2) ∧
      1 / ((N : ℝ) + 2) ≤ 1 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have h2ne : ((2 : ℝ) ^ N) ≠ 0 := h2.ne'
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  constructor
  · have hkey : (2 : ℝ) ^ N * (((N : ℝ) + 2) / (2 : ℝ) ^ N) = (N : ℝ) + 2 := by
      field_simp
    rw [hkey]
  · rw [div_le_one (by linarith)]
    linarith

/-! ### `prop:C1-inv` — a coprime-pair expression for `S` -/

/-- **The visible-pair count.**  For every `n ≥ 0` the number of pairs
`a ≥ 1`, `b ≥ 0` with `a + b = n` and `gcd(a,b) = 1` is `φ(n)`. -/
theorem card_visible_antidiagonal (n : ℕ) :
    ((Finset.antidiagonal n).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ Nat.Coprime q.1 q.2).card
      = Nat.totient n :=
  GeometricCoprimality.card_antidiagonal_filter_pos_coprime n

/-- The convention `φ(0) = 0`. -/
theorem totient_zero_eq_zero : Nat.totient 0 = 0 := Nat.totient_zero

/-- The boundary case `n = 1` contributes exactly `(a,b) = (1,0)`. -/
theorem visible_antidiagonal_one :
    ((Finset.antidiagonal 1).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ Nat.Coprime q.1 q.2)
      = {((1 : ℕ), (0 : ℕ))} := by decide

/-- It disappears when both coordinates are required to be positive. -/
theorem positive_antidiagonal_one :
    ((Finset.antidiagonal 1).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2) = ∅ := by
  decide

/-- **A coprime-pair expression for `S`.**
`∑_{a,b ≥ 1, gcd(a,b)=1} 2^{-(a+b)} = S - 1/2`. -/
theorem tsum_pos_coprime_pairs_eq_series_sub_half :
    (∑' q : ℕ × ℕ, if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then 1 / (2 : ℝ) ^ (q.1 + q.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 := by
  have h := GeometricCoprimality.tsum_pos_coprime_pair_pow
    (r := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  have hL : ∀ q : ℕ × ℕ,
      (if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then 1 / (2 : ℝ) ^ (q.1 + q.2) else 0)
      = (if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then ((1 : ℝ) / 2) ^ (q.1 + q.2) else 0) := by
    intro q
    by_cases hq : 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
    · rw [if_pos hq, if_pos hq, div_pow, one_pow]
    · rw [if_neg hq, if_neg hq]
  rw [tsum_congr hL, h]
  have hR : ∀ n : ℕ, (Nat.totient n : ℝ) * ((1 : ℝ) / 2) ^ n
      = (Nat.totient n : ℝ) / 2 ^ n := by
    intro n
    rw [div_pow, one_pow, mul_one_div]
  rw [tsum_congr hR]

/-- The same mass written as the product of the two marginals
`2^{-a}·2^{-b}`: the coprimality mass of two independent fair-coin waiting
times is `S - 1/2`. -/
theorem tsum_pos_coprime_pairs_product_form :
    (∑' q : ℕ × ℕ, if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then (1 / (2 : ℝ) ^ q.1) * (1 / (2 : ℝ) ^ q.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 := by
  rw [← tsum_pos_coprime_pairs_eq_series_sub_half]
  refine tsum_congr fun q => ?_
  by_cases hq : 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
  · rw [if_pos hq, if_pos hq, div_mul_div_comm, one_mul, ← pow_add]
  · rw [if_neg hq, if_neg hq]

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_mul_den_le_abs_diff
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_le_abs_int_combination
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_den_mul_error_tendsto_zero
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_dirichlet_gap
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_basePower_dilation
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.lambert_ladder_values
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.primWeight_divisor_sum
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_series_index_bridge
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.rational_gap_lower_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.den_lower_bound_of_positive_error
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.denominator_bound_tendsto_atTop_iff
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_den_mul_error_product_tendsto_zero
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_denominator_bound_vacuous
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.card_visible_antidiagonal
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_zero_eq_zero
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.visible_antidiagonal_one
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.positive_antidiagonal_one
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_eq_series_sub_half
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_product_form
