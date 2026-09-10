import Mathlib

/-!
Gamma-free discrete regular-rate core. Verified locally by the focused
Newton-classification build on 2026-09-09.
No external theorem is asserted as a project axiom. In particular, the
analytic upper-envelope step is not a hypothesis silently discharged here.
See MATHEMATICS.md, R1--R5, for the complete ordinary proof.
-/
noncomputable section
namespace Erdos243V8
open Filter
open scoped BigOperators Topology

/-- Iterated forward difference, at the original (unshifted) index. -/
def fd {R : Type*} [Sub R] : ℕ → (ℕ → R) → ℕ → R
  | 0, f, n => f n
  | k + 1, f, n => fd k f (n + 1) - fd k f n

@[simp] theorem fd_cast_int (C : ℕ → ℤ) (k n : ℕ) :
    fd (R := ℝ) k (fun n => (C n : ℝ)) n =
      (fd (R := ℤ) k C n : ℝ) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [fd, ih, Int.cast_sub]

theorem fd_four {R : Type*} [CommRing R] (f : ℕ → R) (n : ℕ) :
    fd 4 f n = f (n + 4) - 4 * f (n + 3) + 6 * f (n + 2) -
      4 * f (n + 1) + f n := by
  simp only [fd, Nat.add_assoc]
  ring

theorem shift_one_atTop : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩

theorem integer_zero_of_tendsto_zero (z : ℕ → ℤ)
    (hz : Tendsto (fun n => (z n : ℝ)) atTop (𝓝 0)) :
    ∃ N, ∀ n, N ≤ n → z n = 0 := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hz 1 (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  have h : |(z n : ℝ)| < 1 := by
    simpa only [Real.dist_eq, sub_zero] using hN n hn
  have hi : |z n| < (1 : ℤ) := by exact_mod_cast h
  have hp := abs_lt.mp hi
  omega

/-- Bounded natural heights and a consecutive ratio tending to one lock.
This uses no monotonicity and allows arbitrarily many previous drawdowns. -/
theorem bounded_nat_ratio_locks (C : ℕ → ℕ)
    (hpos : ∀ n, 0 < C n) (B : ℕ)
    (hB : ∃ N, ∀ n, N ≤ n → C n ≤ B)
    (hr : Tendsto (fun n => (C (n + 1) : ℝ) / (C n : ℝ))
      atTop (𝓝 1)) :
    ∃ N, ∀ n, N ≤ n → C (n + 1) = C n := by
  obtain ⟨N₀, hN₀⟩ := hB
  have hBpos : 0 < B := lt_of_lt_of_le (hpos N₀) (hN₀ N₀ le_rfl)
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hr (1 / (B : ℝ))
    (one_div_pos.mpr hBR)
  refine ⟨max N₀ N₁, fun n hn => ?_⟩
  have hc : (0 : ℝ) < C n := by exact_mod_cast hpos n
  have hb : (C n : ℝ) ≤ B := by exact_mod_cast hN₀ n (le_trans (le_max_left _ _) hn)
  have he : |(C (n + 1) : ℝ) / (C n : ℝ) - 1| < 1 / (B : ℝ) := by
    simpa only [Real.dist_eq] using hN₁ n (le_trans (le_max_right _ _) hn)
  have hmul : |(C (n + 1) : ℝ) - C n| =
      |(C (n + 1) : ℝ) / C n - 1| * (C n : ℝ) := by
    calc
      _ = |((C (n + 1) : ℝ) / C n - 1) * (C n : ℝ)| := by
        congr 1
        field_simp [ne_of_gt hc]
      _ = _ := by rw [abs_mul, abs_of_pos hc]
  have hdiff : |(C (n + 1) : ℝ) - C n| < 1 := by
    rw [hmul]
    calc
      _ < (1 / (B : ℝ)) * (C n : ℝ) := mul_lt_mul_of_pos_right he hc
      _ ≤ (1 / (B : ℝ)) * (B : ℝ) :=
        mul_le_mul_of_nonneg_left hb (le_of_lt (one_div_pos.mpr hBR))
      _ = 1 := by field_simp [ne_of_gt hBR]
  have hiz : |(C (n + 1) : ℤ) - C n| < (1 : ℤ) := by exact_mod_cast hdiff
  have ha := abs_lt.mp hiz
  omega

/-- Division by a family bounded below by one preserves a zero limit. -/
theorem tendsto_div_of_eventually_one_le (e b : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, 1 ≤ b n) :
    Tendsto (fun n => e n / b n) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp he ε hε
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hb
  refine ⟨max N₀ N₁, fun n hn => ?_⟩
  have hb' := hN₁ n (le_trans (le_max_right _ _) hn)
  have he' : |e n| < ε := by
    simpa only [Real.dist_eq, sub_zero] using hN₀ n (le_trans (le_max_left _ _) hn)
  have hbpos : 0 < b n := by linarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hbpos]
  have hle : |e n| / b n ≤ |e n| := by
    apply (div_le_iff₀ hbpos).mpr
    nlinarith [abs_nonneg (e n)]
  exact hle.trans_lt he'

/-- A purely discrete approximation system.  The q-recursion is the exact
quotient identity for q_j(n)=C_n/(n(n+1)...(n+j-1)).  This abstraction isolates
an algebraic identity, not an unproved analytic/exclusion endpoint. -/
theorem forward_difference_approximation
    (C : ℕ → ℝ) (q : ℕ → ℕ → ℝ) (e : ℕ → ℝ)
    (den : ℕ → ℕ → ℝ) (lam : ℝ)
    (hq0 : ∀ n, q 0 n = C n)
    (hrec : ∀ j, ∀ᶠ n in atTop,
      q j (n + 1) - q j n = (lam - (j : ℝ)) * q (j + 1) n + e n / den j n)
    (hden : ∀ j, ∀ᶠ n in atTop, 1 ≤ den j n)
    (he : Tendsto e atTop (𝓝 0)) :
    ∀ j, Tendsto (fun n => fd j C n -
      (∏ k ∈ Finset.range j, (lam - (k : ℝ))) * q j n) atTop (𝓝 0) := by
  intro j
  induction j with
  | zero =>
      simpa [fd, hq0] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | succ j ih =>
      let F : ℝ := ∏ k ∈ Finset.range j, (lam - (k : ℝ))
      have hn := ih.comp shift_one_atTop
      have hd := tendsto_div_of_eventually_one_le e (den j) he (hden j)
      have hF : Tendsto (fun _ : ℕ => F) atTop (𝓝 F) := tendsto_const_nhds
      have hlim := (hn.sub ih).add (hF.mul hd)
      have hlim' : Tendsto (fun n =>
          ((fd j C (n + 1) - F * q j (n + 1)) -
            (fd j C n - F * q j n)) + F * (e n / den j n))
          atTop (𝓝 0) := by
        simpa only [Function.comp_apply, sub_zero, zero_sub, add_zero,
          sub_self, mul_zero, F] using hlim
      apply hlim'.congr'
      filter_upwards [hrec j] with n hn
      simp only [fd, Finset.prod_range_succ]
      dsimp only [F] at *
      nlinarith [congrArg (fun t : ℝ => (∏ k ∈ Finset.range j, (lam - (k : ℝ))) * t) hn]

/-- The falling coefficient at order four is zero at lambda=3. -/
theorem cubic_falling_factor_zero :
    (∏ k ∈ Finset.range 4, ((3 : ℝ) - (k : ℝ))) = 0 := by
  norm_num [Finset.prod_range_succ]

/-- A full integer-discreteness consumer for the cubic finite-difference
calculus.  It does not claim that arbitrary q/den data exist. -/
theorem fourth_difference_eventually_zero
    (C : ℕ → ℤ) (q : ℕ → ℕ → ℝ) (e : ℕ → ℝ)
    (den : ℕ → ℕ → ℝ)
    (hq0 : ∀ n, q 0 n = (C n : ℝ))
    (hrec : ∀ j, ∀ᶠ n in atTop,
      q j (n + 1) - q j n = ((3 : ℝ) - (j : ℝ)) * q (j + 1) n + e n / den j n)
    (hden : ∀ j, ∀ᶠ n in atTop, 1 ≤ den j n)
    (he : Tendsto e atTop (𝓝 0)) :
    ∃ N, ∀ n, N ≤ n → fd (R := ℤ) 4 C n = 0 := by
  have h := forward_difference_approximation (fun n => (C n : ℝ)) q e den 3
    hq0 hrec hden he 4
  have hz : Tendsto (fun n => (fd (R := ℤ) 4 C n : ℝ)) atTop (𝓝 0) := by
    simpa only [cubic_falling_factor_zero, zero_mul, sub_zero, fd_cast_int] using h
  exact integer_zero_of_tendsto_zero (fd (R := ℤ) 4 C) hz

end Erdos243V8
end
