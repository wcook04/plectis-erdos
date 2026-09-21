import Erdos249257.HalfGreedyFatalGap
import Erdos249257.SublogDivisorCoverage

/-!
Paper-form restatements of two asserted environments from the long
Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`.

* `record:257hg-i4` (`a257_front.tex:4943`), "A sufficient inequality for a
  safe skip": `paper_dyadic_skip_test_iff`,
  `paper_sharp_skip_safe_lb3`, `paper_sharp_skip_safe_actual_tail`,
  `paper_three_channel_margin_identity`, `paper_sharp_weaker_than_dyadic`,
  `paper_sharp_strictly_weaker_realizable`.
* `record:257rig-i4a` (`a257_front.tex:4801`), "Bounds for intervals with zero
  divisor counts": `paper_zero_run_le_eps_logb`,
  `paper_zero_run_le_of_mem`.

The paper writes `ρ = u/(2L)` for the skipped rational remainder and
`R_k = mersenneTail k` for the remaining Mersenne tail mass; the
subtraction-free form of `a = 2L - (2^k - 1)u` is `2^k * u + a = 2L + u`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.HalfGreedyFatalGap

/-! ## `record:257hg-i4` -- a sufficient inequality for a safe skip -/

/-- "For the skipped rational remainder `ρ = u/(2L)`, `ρ ≤ 2^(-k)` is
equivalent to `u ≤ a`." -/
theorem paper_dyadic_skip_test_iff {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k) ↔ u ≤ a := by
  have h2k : (2 : ℕ) ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hmul : 2 * u ≤ 2 ^ k * u := Nat.mul_le_mul_right u h2k
  have hLpos : 0 < L := by omega
  have hLR : (0 : ℝ) < 2 * L := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
    linarith
  have hpk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hstep : ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k) ↔ ((u : ℝ) * 2 ^ k ≤ 2 * L) := by
    rw [div_le_div_iff₀ hLR hpk, one_mul]
  have hcast : ((u : ℝ) * 2 ^ k ≤ 2 * L) ↔ (2 ^ k * u ≤ 2 * L) := by
    rw [show ((u : ℝ) * 2 ^ k) = ((2 ^ k * u : ℕ) : ℝ) by push_cast; ring,
      show ((2 : ℝ) * L) = ((2 * L : ℕ) : ℝ) by push_cast; ring]
    exact Nat.cast_le
  rw [hstep, hcast]
  omega

/-- Paper display of `record:257hg-i4`: `2u ≤ 3a` forces the skipped residual
strictly below the three-channel lower bound. -/
theorem paper_sharp_skip_safe_lb3 {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTailLB3 k :=
  skipSafe_of_two_mul_le_three_mul hk hu ha hdecomp hsharp

/-- The same conclusion against the actual tail `R_k`: `2u ≤ 3a ⟹ ρ < R_k`. -/
theorem paper_sharp_skip_safe_actual_tail {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTail k :=
  skipSafe_actualTail_of_two_mul_le_three_mul hk hu ha hdecomp hsharp

/-- The explicit margin computed in the environment: with `t = 2^k ≥ 2`,
`(1/t + 1/(3t²) + 1/(7t³)) - 3/(3t-1) = (2t-3)/(21 t³ (3t-1)) > 0`. -/
theorem paper_three_channel_margin_identity {t : ℝ} (ht : 2 ≤ t) :
    (1 / t + 1 / (3 * t ^ 2) + 1 / (7 * t ^ 3)) - 3 / (3 * t - 1) =
        (2 * t - 3) / (21 * t ^ 3 * (3 * t - 1)) ∧
      0 < (2 * t - 3) / (21 * t ^ 3 * (3 * t - 1)) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hden : (0 : ℝ) < 3 * t - 1 := by linarith
  have ht0' : t ≠ 0 := ne_of_gt ht0
  have hden' : (3 * t - 1 : ℝ) ≠ 0 := ne_of_gt hden
  have hpow' : (21 * t ^ 3 : ℝ) ≠ 0 := by positivity
  constructor
  · have hchannels : (1 / t + 1 / (3 * t ^ 2) + 1 / (7 * t ^ 3)) =
        (21 * t ^ 2 + 7 * t + 3) / (21 * t ^ 3) := by
      field_simp
      ring
    rw [hchannels, div_sub_div _ _ hpow' hden']
    congr 1
    ring
  · apply div_pos (by linarith)
    positivity

/-- "The sufficient condition is weaker than `u ≤ a`." -/
theorem paper_sharp_weaker_than_dyadic {u a : ℕ} (h : u ≤ a) : 2 * u ≤ 3 * a :=
  sharp_of_dyadic h

/-- The realizable witness `(k,u,L,a) = (2,7,13,5)` of the environment: it
satisfies the skip decomposition and `2u ≤ 3a`, but not `u ≤ a`. -/
theorem paper_sharp_strictly_weaker_realizable :
    ∃ k u L a : ℕ, 1 ≤ k ∧ 0 < u ∧ 0 < a ∧
      2 ^ k * u + a = 2 * L + u ∧ 2 * u ≤ 3 * a ∧ ¬ u ≤ a :=
  ⟨2, 7, 13, 5, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- "The inequality `2u ≤ 3a` gives `rho ≤ 3/(3t-1)`", with `t = 2^k`. -/
theorem paper_sharp_gives_three_over_three_t_sub_one {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) ≤ 3 / (3 * (2 : ℝ) ^ k - 1) := by
  have h2kNat : (2 : ℕ) ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hmulNat : 2 * u ≤ 2 ^ k * u := Nat.mul_le_mul_right u h2kNat
  have hLpos : 0 < L := by omega
  have ht : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hLRpos : (0 : ℝ) < 2 * (L : ℝ) := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
    linarith
  have hden : (0 : ℝ) < 3 * (2 : ℝ) ^ k - 1 := by linarith
  have h2L : (2 : ℝ) * (L : ℝ) = ((2 : ℝ) ^ k - 1) * u + a := by
    have hcast : ((2 ^ k * u + a : ℕ) : ℝ) = ((2 * L + u : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun x : ℕ ↦ (x : ℝ)) hdecomp
    push_cast at hcast
    linarith
  have hsharpR : 2 * (u : ℝ) ≤ 3 * (a : ℝ) := by exact_mod_cast hsharp
  rw [div_le_div_iff₀ hLRpos hden]
  nlinarith [h2L, hsharpR]

/-- "The first two terms alone would not prove this comparison": already at
`t = 2` the two-channel truncation falls below `3/(3t-1)`. -/
theorem paper_two_channels_insufficient :
    1 / (2 : ℝ) + 1 / (3 * (2 : ℝ) ^ 2) < 3 / (3 * (2 : ℝ) - 1) := by
  norm_num

/-- The exact mass threshold the environment records for comparison:
`rho <= R_k` is exactly `a/u >= R_k⁻¹ - (2^k - 1)`, and that right-hand side
lies strictly between `0` and `2/3`. -/
theorem paper_exact_mass_threshold {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ mersenneTail k ↔
        (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ≤ (a : ℝ) / u) ∧
      0 < (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ∧
      (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) < 2 / 3 := by
  have h2kNat : (2 : ℕ) ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hmulNat : 2 * u ≤ 2 ^ k * u := Nat.mul_le_mul_right u h2kNat
  have hLpos : 0 < L := by omega
  have ht : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hupos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hLRpos : (0 : ℝ) < 2 * (L : ℝ) := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
    linarith
  have hLB3pos : 0 < mersenneTailLB3 k := by
    unfold mersenneTailLB3
    positivity
  have hTpos : 0 < mersenneTail k :=
    hLB3pos.trans (mersenneTailLB3_lt_mersenneTail k)
  have hTne : mersenneTail k ≠ 0 := ne_of_gt hTpos
  have hTinv : mersenneTail k * (mersenneTail k)⁻¹ = 1 := mul_inv_cancel₀ hTne
  -- lower clause: `R_k < 1/(2^k - 1)` gives positivity of the threshold
  have hdenk : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by linarith
  have hTw : mersenneTail k < mersenneWeight k := mersenneTail_lt_weight (by omega)
  have hlow : (2 : ℝ) ^ k - 1 < (mersenneTail k)⁻¹ := by
    have hprod : mersenneTail k * ((2 : ℝ) ^ k - 1) < 1 := by
      have hw : mersenneWeight k = 1 / ((2 : ℝ) ^ k - 1) := rfl
      rw [hw] at hTw
      have := mul_lt_mul_of_pos_right hTw hdenk
      rw [div_mul_cancel₀ _ (ne_of_gt hdenk)] at this
      linarith
    rw [inv_eq_one_div, lt_div_iff₀ hTpos]
    linarith
  -- upper clause: the three-channel lower bound gives `R_k⁻¹ < 2^k - 1/3`
  have hthird : (0 : ℝ) < (2 : ℝ) ^ k - 1 / 3 := by linarith
  have hupper : (mersenneTail k)⁻¹ < (2 : ℝ) ^ k - 1 / 3 := by
    have hone : 1 < mersenneTailLB3 k * ((2 : ℝ) ^ k - 1 / 3) := by
      unfold mersenneTailLB3
      have ht0 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
      field_simp
      nlinarith [ht]
    have hgrow := mul_lt_mul_of_pos_right
      (mersenneTailLB3_lt_mersenneTail k) hthird
    rw [inv_eq_one_div, div_lt_iff₀ hTpos]
    nlinarith [hone, hgrow]
  refine ⟨?_, by linarith, by linarith⟩
  -- the equivalence
  have h2L : (2 : ℝ) * (L : ℝ) = ((2 : ℝ) ^ k - 1) * u + a := by
    have hcast : ((2 ^ k * u + a : ℕ) : ℝ) = ((2 * L + u : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun x : ℕ ↦ (x : ℝ)) hdecomp
    push_cast at hcast
    linarith
  have hexpand : mersenneTail k *
      (((mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1)) * u) =
      (u : ℝ) - mersenneTail k * ((2 : ℝ) ^ k - 1) * u := by
    field_simp
  rw [div_le_iff₀ hLRpos, le_div_iff₀ hupos, h2L]
  constructor
  · intro h
    have hkey : mersenneTail k *
        (((mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1)) * u) ≤
        mersenneTail k * (a : ℝ) := by
      rw [hexpand]
      nlinarith [h]
    exact le_of_mul_le_mul_left hkey hTpos
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hTpos)
    rw [hexpand] at hmul
    nlinarith [hmul]

/-! ## `record:257rig-i4a` -- zero divisor-count runs -/

/-- Paper display of `record:257rig-i4a`: if `X_A(2) = p/(2^c v)` for an
infinite positive support `A` and an odd positive `v`, then for every `ε > 0`
there is `B` such that every run of `h` zero divisor counts starting after
`c + N` (with `N ≥ 1`) satisfies `h ≤ ε log₂ N + B`. -/
theorem paper_zero_run_le_eps_logb
    (A : Set ℕ) (hinf : A.Infinite) (hzero : 0 ∉ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v) (_hvodd : Odd v)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ, 1 ≤ N →
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N : ℝ) + B := by
  obtain ⟨a, haA⟩ := hinf.nonempty
  have hapos : 0 < a := Nat.pos_of_ne_zero fun h ↦ hzero (h ▸ haA)
  exact supportCoeffZeroWindow_length_le_eps_logb A ⟨a, hapos, haA⟩ p c v hv
    hvalue ε hε

/-- The unconditional strengthening asserted in the same environment: fix any
`a ∈ A` with `a ≥ 1`.  Every `a` consecutive positive integers contain a
multiple of `a`, where `c_A` is positive, so `h ≤ a - 1`.  No rationality and
no tail estimate is used. -/
theorem paper_zero_run_le_of_mem
    (A : Set ℕ) {a : ℕ} (hapos : 0 < a) (haA : a ∈ A) {N h : ℕ}
    (hwindow : SupportCoeffZeroWindow A N h) :
    h ≤ a - 1 := by
  by_contra hcon
  have hha : a ≤ h := by omega
  have hdivmod := Nat.div_add_mod N a
  have hmod : N % a < a := Nat.mod_lt _ hapos
  set m : ℕ := a * (N / a + 1) with hm
  have hmeq : m = a * (N / a) + a := by rw [hm]; ring
  have hlow : N < m := by omega
  have hhigh : m ≤ N + a := by omega
  refine absurd (hwindow (m - (N + 1)) (by omega)) ?_
  have hindex : N + (m - (N + 1)) + 1 = m := by omega
  rw [hindex]
  have hpos : 0 < supportCoeff A m :=
    supportCoeff_pos_of_mem_dvd A haA ⟨N / a + 1, hm⟩ (by omega)
  omega

#print axioms paper_dyadic_skip_test_iff
#print axioms paper_sharp_skip_safe_lb3
#print axioms paper_sharp_skip_safe_actual_tail
#print axioms paper_three_channel_margin_identity
#print axioms paper_sharp_weaker_than_dyadic
#print axioms paper_sharp_strictly_weaker_realizable
#print axioms paper_sharp_gives_three_over_three_t_sub_one
#print axioms paper_two_channels_insufficient
#print axioms paper_exact_mass_threshold
#print axioms paper_zero_run_le_eps_logb
#print axioms paper_zero_run_le_of_mem

end ErdosProblems.Erdos257.PaperCompleteR21
