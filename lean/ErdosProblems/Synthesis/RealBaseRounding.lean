-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.Erdos251.SparseRationalisationCore
import ErdosProblems.Erdos1049.PaperLinearFormsR7

/-!
# Rounding shadows in a real base `x > 1`

Fix a real base `x > 1`, a digit bound `D ≥ x - 1`, a modulus `q ≥ 1` and a cutoff `M`.  Every
`y` in `[0, D r^(M+1)/(1 - r)]`, with `r = 1/x`, is `∑_{n > M} δ_n r^n` for digits
`0 ≤ δ_n ≤ D` (`exists_placed_digits_geom`); this is the greedy filling
`ErdosProblems.Erdos251.SparseRationalisationDraft.exists_digits_hasSum_of_capacity` with the
geometric capacities `D r^(k+M+1)/(1 - r)`.  Adding `q δ` to a coefficient sequence `c` moves
`∑ c(n)/x^n` onto any value in an interval of positive length, so onto a rational number, while
keeping `c` modulo `q`, keeping `c` up to `M`, and moving each coefficient by at most `qD`
(`exists_upShadow_realBase`, `up_rounding_barrier_realBase`).

At the divisor count `τ(n) = #divisors(n)` this gives a barrier for Erdős #1049 at every base
`x > 1`, including the open base `3/2`: agreement with `τ` modulo a fixed `q`, size within a
fixed bound of `τ`, and agreement with `τ` on any finite prefix do not imply irrationality of
`∑ a(n)/x^n`, whose value at `a = τ` is `∑_{n≥1} 1/(x^n - 1)`
(`paperLambert_eq_tsum_divisor_count`, `paperLambert_rounding_barrier`,
`paperLambert_threeHalves_rounding_barrier`).  Nothing here decides the irrationality of that
series at any base.
-/

noncomputable section

namespace ErdosProblems.Synthesis.RealBaseRounding

open Filter Topology

/-- **Greedy digits after a cutoff in a geometric scale.**  For `0 < r < 1` and `1 - r ≤ D r`,
every `y` with `0 ≤ y ≤ D r^(M+1)/(1 - r)` is `∑ δ_n r^n` for digits `δ_n ≤ D` that vanish up to
position `M`. -/
theorem exists_placed_digits_geom {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {D : ℕ}
    (hD : 1 - r ≤ D * r) (M : ℕ) {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y ≤ D * r ^ (M + 1) * (1 - r)⁻¹) :
    ∃ δ : ℕ → ℕ, (∀ n, δ n ≤ D) ∧ (∀ n, n ≤ M → δ n = 0) ∧
      HasSum (fun n => (δ n : ℝ) * r ^ n) y := by
  have hne : (1 - r) ≠ 0 := (sub_pos.mpr hr1).ne'
  have hinv : (1 - r) * (1 - r)⁻¹ = 1 := mul_inv_cancel₀ hne
  have hinvpos : 0 < (1 - r)⁻¹ := inv_pos.mpr (sub_pos.mpr hr1)
  have hw : ∀ k : ℕ, 0 < r ^ (k + (M + 1)) := fun k => pow_pos hr0 _
  have hstep : ∀ k : ℕ, (D : ℝ) * r ^ (k + (M + 1)) * (1 - r)⁻¹ =
      (D : ℝ) * r ^ (k + (M + 1)) + (D : ℝ) * r ^ ((k + 1) + (M + 1)) * (1 - r)⁻¹ := by
    intro k
    rw [show (k + 1) + (M + 1) = k + (M + 1) + 1 by omega, pow_succ]
    linear_combination ((D : ℝ) * r ^ (k + (M + 1))) * hinv
  have hoverlap : ∀ k : ℕ, r ^ (k + (M + 1)) ≤
      (D : ℝ) * r ^ ((k + 1) + (M + 1)) * (1 - r)⁻¹ := by
    intro k
    rw [show (k + 1) + (M + 1) = k + (M + 1) + 1 by omega, pow_succ]
    have hp := hw k
    have key : r ^ (k + (M + 1)) * (1 - r) * (1 - r)⁻¹ ≤
        r ^ (k + (M + 1)) * (D * r) * (1 - r)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hp.le) hinvpos.le
    calc r ^ (k + (M + 1)) = r ^ (k + (M + 1)) * ((1 - r) * (1 - r)⁻¹) := by
          rw [hinv, mul_one]
      _ = r ^ (k + (M + 1)) * (1 - r) * (1 - r)⁻¹ := by ring
      _ ≤ r ^ (k + (M + 1)) * (D * r) * (1 - r)⁻¹ := key
      _ = (D : ℝ) * (r ^ (k + (M + 1)) * r) * (1 - r)⁻¹ := by ring
  have hvanish : Tendsto (fun k : ℕ => (D : ℝ) * r ^ (k + (M + 1)) * (1 - r)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul
      ((D : ℝ) * r ^ (M + 1) * (1 - r)⁻¹)
    rw [mul_zero] at h
    refine h.congr fun k => ?_
    rw [pow_add]
    ring
  have hy1' : y ≤ (D : ℝ) * r ^ (0 + (M + 1)) * (1 - r)⁻¹ := by
    rw [Nat.zero_add]
    exact hy1
  obtain ⟨d, hdD, hd⟩ :=
    ErdosProblems.Erdos251.SparseRationalisationDraft.exists_digits_hasSum_of_capacity
      (w := fun k => r ^ (k + (M + 1)))
      (S := fun k => (D : ℝ) * r ^ (k + (M + 1)) * (1 - r)⁻¹)
      (D := fun _ => D) hw hstep hoverlap hvanish hy0 hy1'
  refine ⟨fun n => if M < n then d (n - (M + 1)) else 0, fun n => ?_, fun n hn => ?_, ?_⟩
  · dsimp only
    split
    · exact hdD _
    · exact Nat.zero_le _
  · dsimp only
    rw [if_neg (Nat.not_lt.mpr hn)]
  · show HasSum (fun n => ((if M < n then d (n - (M + 1)) else 0 : ℕ) : ℝ) * r ^ n) y
    refine (hasSum_nat_add_iff' (M + 1)).mp ?_
    have hzero : ∑ i ∈ Finset.range (M + 1),
        (((if M < i then d (i - (M + 1)) else 0 : ℕ) : ℝ) * r ^ i) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [if_neg (Nat.not_lt.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))]
        simp
    rw [hzero, sub_zero]
    have hfun : (fun k : ℕ =>
        ((if M < k + (M + 1) then d (k + (M + 1) - (M + 1)) else 0 : ℕ) : ℝ) *
          r ^ (k + (M + 1))) = fun k => (d k : ℝ) * r ^ (k + (M + 1)) := by
      funext k
      rw [if_pos (show M < k + (M + 1) by omega), Nat.add_sub_cancel]
    rw [hfun]
    exact hd

/-- **Rounding in a geometric scale (upward).**  For `0 < r < 1`, `1 - r ≤ D r` and a
coefficient sequence with `∑ c(n) r^n` convergent: for every modulus `q ≥ 1` and cutoff `M`
some `a` agrees with `c` up to `M`, is congruent to `c` modulo `q`, lies between `c` and
`c + qD`, and has a rational value `∑ a(n) r^n`. -/
theorem exists_upShadow_geom {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {D : ℕ}
    (hD : 1 - r ≤ D * r) (c : ℕ → ℕ) (hsum : Summable (fun n => (c n : ℝ) * r ^ n))
    {q : ℕ} (hq : 0 < q) (M : ℕ) :
    ∃ a : ℕ → ℕ, (∀ n, a n ≡ c n [MOD q]) ∧ (∀ n, c n ≤ a n ∧ a n ≤ c n + q * D) ∧
      (∀ n, n ≤ M → a n = c n) ∧ ∃ v : ℚ, HasSum (fun n => (a n : ℝ) * r ^ n) v := by
  have hDpos : (0 : ℝ) < D := by
    by_contra h
    have h0 : (D : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg D)
    rw [h0, zero_mul] at hD
    linarith
  have hinvpos : 0 < (1 - r)⁻¹ := inv_pos.mpr (sub_pos.mpr hr1)
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hcap : 0 < (q : ℝ) * (D * r ^ (M + 1) * (1 - r)⁻¹) :=
    mul_pos hqR (mul_pos (mul_pos hDpos (pow_pos hr0 _)) hinvpos)
  obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn
    (show (∑' n, (c n : ℝ) * r ^ n) <
        (∑' n, (c n : ℝ) * r ^ n) + (q : ℝ) * (D * r ^ (M + 1) * (1 - r)⁻¹) by linarith)
  have hy0 : 0 ≤ ((v : ℝ) - ∑' n, (c n : ℝ) * r ^ n) / q := div_nonneg (by linarith) hqR.le
  have hy1 : ((v : ℝ) - ∑' n, (c n : ℝ) * r ^ n) / q ≤ D * r ^ (M + 1) * (1 - r)⁻¹ := by
    rw [div_le_iff₀ hqR, mul_comm]
    linarith
  obtain ⟨δ, hδD, hδM, hδsum⟩ := exists_placed_digits_geom hr0 hr1 hD M hy0 hy1
  refine ⟨fun n => c n + q * δ n, fun n => ?_, fun n => ⟨Nat.le_add_right _ _, ?_⟩,
    fun n hn => ?_, v, ?_⟩
  · show (c n + q * δ n) % q = c n % q
    rw [Nat.add_mul_mod_self_left]
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left q (hδD n)) _
  · show c n + q * δ n = c n
    rw [hδM n hn, mul_zero, Nat.add_zero]
  · have h := hsum.hasSum.add (hδsum.mul_left (q : ℝ))
    have hval : (∑' n, (c n : ℝ) * r ^ n) +
        (q : ℝ) * (((v : ℝ) - ∑' n, (c n : ℝ) * r ^ n) / q) = v := by
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hqR.ne']
      ring
    rw [hval] at h
    convert h using 1
    funext n
    push_cast
    ring

/-- **Rounding in a real base `x > 1` (upward).**  For a digit bound `D ≥ x - 1` and a
coefficient sequence with `∑ c(n)/x^n` convergent: for every modulus `q ≥ 1` and cutoff `M` some
`a` agrees with `c` up to `M`, is congruent to `c` modulo `q`, lies between `c` and `c + qD`, and
has a rational value `∑ a(n)/x^n`. -/
theorem exists_upShadow_realBase {x : ℝ} (hx : 1 < x) {D : ℕ} (hD : x - 1 ≤ D)
    (c : ℕ → ℕ) (hsum : Summable (fun n => (c n : ℝ) / x ^ n)) {q : ℕ} (hq : 0 < q) (M : ℕ) :
    ∃ a : ℕ → ℕ, (∀ n, a n ≡ c n [MOD q]) ∧ (∀ n, c n ≤ a n ∧ a n ≤ c n + q * D) ∧
      (∀ n, n ≤ M → a n = c n) ∧ ∃ v : ℚ, HasSum (fun n => (a n : ℝ) / x ^ n) v := by
  have hx0 : 0 < x := by linarith
  have hxne : x ≠ 0 := hx0.ne'
  have hr0 : (0 : ℝ) < 1 / x := div_pos one_pos hx0
  have hr1 : 1 / x < 1 := by
    rw [div_lt_one hx0]
    exact hx
  have hDr : 1 - 1 / x ≤ D * (1 / x) := by
    rw [show (1 : ℝ) - 1 / x = (x - 1) / x by field_simp, mul_one_div]
    exact div_le_div_of_nonneg_right hD hx0.le
  have hconv : ∀ (e : ℕ → ℕ) (n : ℕ), (e n : ℝ) / x ^ n = (e n : ℝ) * (1 / x) ^ n := by
    intro e n
    rw [div_pow, one_pow, mul_one_div]
  have hsum' : Summable (fun n => (c n : ℝ) * (1 / x) ^ n) := hsum.congr (hconv c)
  obtain ⟨a, h1, h2, h3, v, hv⟩ := exists_upShadow_geom hr0 hr1 hDr c hsum' hq M
  refine ⟨a, h1, h2, h3, v, ?_⟩
  convert hv using 1
  funext n
  exact hconv a n

/-- **Real-base rounding barrier.**  For a base `x > 1`, a digit bound `D ≥ x - 1` and a
coefficient sequence with `∑ c(n)/x^n` convergent: agreement with `c` modulo `q`, lying between
`c` and `c + qD`, and agreement with `c` up to `M` do not imply irrationality of
`∑ a(n)/x^n`. -/
theorem up_rounding_barrier_realBase {x : ℝ} (hx : 1 < x) {D : ℕ} (hD : x - 1 ≤ D)
    (c : ℕ → ℕ) (hsum : Summable (fun n => (c n : ℝ) / x ^ n)) {q : ℕ} (hq : 0 < q) (M : ℕ) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≡ c n [MOD q]) → (∀ n, c n ≤ a n ∧ a n ≤ c n + q * D) →
      (∀ n, n ≤ M → a n = c n) → Irrational (∑' n, (a n : ℝ) / x ^ n) := by
  intro route
  obtain ⟨a, h1, h2, h3, v, hv⟩ := exists_upShadow_realBase hx hD c hsum hq M
  have h := route a h1 h2 h3
  rw [hv.tsum_eq] at h
  exact Rat.not_irrational v h

theorem summable_div_pow_of_le_self {x : ℝ} (hx : 1 < x) (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) :
    Summable (fun n => (c n : ℝ) / x ^ n) := by
  have hx0 : 0 < x := by linarith
  have hr : ‖(1 : ℝ) / x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one hx0.le), div_lt_one hx0]
    exact hx
  have hs : Summable (fun n : ℕ => (n : ℝ) * ((1 : ℝ) / x) ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0.le _)) (fun n => ?_) hs
  rw [div_pow, one_pow, mul_one_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc n) (pow_nonneg hx0.le _)

/-- The Lambert identity in a real base: `∑_{k≥1} 1/(x^k - 1) = ∑_{m≥1} τ(m)/x^m` for `x > 1`. -/
theorem tsum_one_div_pow_sub_one_eq_tsum_divisor_count {x : ℝ} (hx : 1 < x) :
    ∑' k : ℕ, (1 : ℝ) / (x ^ (k + 1) - 1) =
      ∑' m : ℕ, (((m + 1).divisors.card : ℕ) : ℝ) / x ^ (m + 1) := by
  have hx0 : 0 < x := by linarith
  have hr : ‖(1 : ℝ) / x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one hx0.le), div_lt_one hx0]
    exact hx
  have hterm : ∀ n : ℕ, 0 < n →
      ((1 : ℝ) / x) ^ n / (1 - ((1 : ℝ) / x) ^ n) = 1 / (x ^ n - 1) := by
    intro n hn
    have hxn : (1 : ℝ) < x ^ n := one_lt_pow₀ hx (by omega)
    have hxn0 : x ^ n ≠ 0 := pow_ne_zero n hx0.ne'
    have hxn1 : x ^ n - 1 ≠ 0 := ne_of_gt (by linarith)
    have h1X : (1 : ℝ) - 1 / x ^ n ≠ 0 := by
      have hEq : (1 : ℝ) - 1 / x ^ n = (x ^ n - 1) / x ^ n := by
        field_simp
      rw [hEq]
      exact div_ne_zero hxn1 hxn0
    rw [div_pow, one_pow]
    field_simp
  have hlam := tsum_pow_div_one_sub_eq_tsum_sigma (𝕜 := ℝ) hr 0
  calc ∑' k : ℕ, (1 : ℝ) / (x ^ (k + 1) - 1)
      = ∑' n : ℕ+, (1 : ℝ) / (x ^ (n : ℕ) - 1) :=
        (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (1 : ℝ) / (x ^ n - 1))).symm
    _ = ∑' n : ℕ+, ((n : ℝ)) ^ 0 * ((1 : ℝ) / x) ^ (n : ℕ)
          / (1 - ((1 : ℝ) / x) ^ (n : ℕ)) := by
        refine tsum_congr fun n => ?_
        rw [pow_zero, one_mul, hterm (n : ℕ) n.pos]
    _ = ∑' n : ℕ+, ((ArithmeticFunction.sigma 0 (n : ℕ) : ℝ))
          * ((1 : ℝ) / x) ^ (n : ℕ) := hlam
    _ = ∑' m : ℕ, ((ArithmeticFunction.sigma 0 (m + 1) : ℝ))
          * ((1 : ℝ) / x) ^ (m + 1) :=
        tsum_pnat_eq_tsum_succ
          (f := fun n : ℕ => ((ArithmeticFunction.sigma 0 n : ℝ)) * ((1 : ℝ) / x) ^ n)
    _ = ∑' m : ℕ, (((m + 1).divisors.card : ℕ) : ℝ) / x ^ (m + 1) := by
        refine tsum_congr fun m => ?_
        rw [ArithmeticFunction.sigma_zero_apply, div_pow, one_pow, mul_one_div]

/-- The #1049 series `paperLambert x = ∑_{n≥1} 1/(x^n - 1)` is `∑_{n ≥ 0} τ(n)/x^n`. -/
theorem paperLambert_eq_tsum_divisor_count {x : ℝ} (hx : 1 < x) :
    ErdosProblems.Erdos1049.PaperR7.paperLambert x =
      ∑' n : ℕ, ((n.divisors.card : ℕ) : ℝ) / x ^ n := by
  have hs : Summable (fun n : ℕ => ((n.divisors.card : ℕ) : ℝ) / x ^ n) :=
    summable_div_pow_of_le_self hx (fun n => n.divisors.card) Nat.card_divisors_le_self
  unfold ErdosProblems.Erdos1049.PaperR7.paperLambert
  rw [tsum_one_div_pow_sub_one_eq_tsum_divisor_count hx, hs.tsum_eq_zero_add]
  simp

/-- **The #1049 barrier at every real base `x > 1`.**  Agreement with `τ` modulo `q`, lying
between `τ` and `τ + q⌈x - 1⌉`, and agreement with `τ` up to `M` do not imply irrationality of
`∑ a(n)/x^n`; at `a = τ` that series is `paperLambert x`. -/
theorem paperLambert_rounding_barrier {x : ℝ} (hx : 1 < x) {q : ℕ} (hq : 0 < q) (M : ℕ) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≡ n.divisors.card [MOD q]) →
      (∀ n, n.divisors.card ≤ a n ∧ a n ≤ n.divisors.card + q * ⌈x - 1⌉₊) →
      (∀ n, n ≤ M → a n = n.divisors.card) → Irrational (∑' n, (a n : ℝ) / x ^ n) :=
  up_rounding_barrier_realBase hx (Nat.le_ceil _) (fun n => n.divisors.card)
    (summable_div_pow_of_le_self hx _ Nat.card_divisors_le_self) hq M

/-- **The #1049 barrier at the base `3/2`.**  Agreement with `τ` modulo `q`, lying between `τ`
and `τ + q`, and agreement with `τ` up to `M` do not imply irrationality of `∑ a(n)/(3/2)^n`;
at `a = τ` that series is `paperLambert (3/2)`. -/
theorem paperLambert_threeHalves_rounding_barrier {q : ℕ} (hq : 0 < q) (M : ℕ) :
    ¬ ∀ a : ℕ → ℕ, (∀ n, a n ≡ n.divisors.card [MOD q]) →
      (∀ n, n.divisors.card ≤ a n ∧ a n ≤ n.divisors.card + q) →
      (∀ n, n ≤ M → a n = n.divisors.card) →
      Irrational (∑' n, (a n : ℝ) / (3 / 2 : ℝ) ^ n) := by
  have h := up_rounding_barrier_realBase (x := 3 / 2) (by norm_num) (D := 1) (by norm_num)
    (fun n => n.divisors.card)
    (summable_div_pow_of_le_self (by norm_num) _ Nat.card_divisors_le_self) hq M
  simpa only [mul_one] using h

end ErdosProblems.Synthesis.RealBaseRounding

#print axioms ErdosProblems.Synthesis.RealBaseRounding.exists_placed_digits_geom
#print axioms ErdosProblems.Synthesis.RealBaseRounding.exists_upShadow_geom
#print axioms ErdosProblems.Synthesis.RealBaseRounding.exists_upShadow_realBase
#print axioms ErdosProblems.Synthesis.RealBaseRounding.up_rounding_barrier_realBase
#print axioms ErdosProblems.Synthesis.RealBaseRounding.tsum_one_div_pow_sub_one_eq_tsum_divisor_count
#print axioms ErdosProblems.Synthesis.RealBaseRounding.paperLambert_eq_tsum_divisor_count
#print axioms ErdosProblems.Synthesis.RealBaseRounding.paperLambert_rounding_barrier
#print axioms ErdosProblems.Synthesis.RealBaseRounding.paperLambert_threeHalves_rounding_barrier
