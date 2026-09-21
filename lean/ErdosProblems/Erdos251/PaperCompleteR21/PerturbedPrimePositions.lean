import ErdosProblems.Erdos251.BoundedPerturbationCountermodel
import ErdosProblems.Erdos251.NonconcentrationCoreR11

/-!
# Erdős #251: the bounded perturbation at the actual prime gaps

Paper restatement of `long251:res:nonconc-primes` ("nonconcentration does not
force irrationality").  Fix `M ≥ 1` and `K ≥ 0` and let `b` be the perturbed
sequence supplied by the bounded-perturbation theorem at the actual prime
gaps.  Then

* `Σ_{n ≥ 0} b_n 2^{-(n+1)}` is rational;
* `b_n = g_n` for `n < K`;
* `b_n - g_n ∈ {0, M}` and `b_n ≡ g_n (mod M)` for every `n`;
* `b` has fixed-block nonconcentration;
* `P_n = 2 + Σ_{i < n} b_i` satisfies `p_n ≤ P_n ≤ p_n + Mn`;
* hence `P_n ∼ n log n`.

Two inputs of the paper's proof are cited literature rather than Mathlib, so
they are carried as explicit named hypotheses and never assumed silently:
`FixedBlockNonconcentration` for the actual gaps (Schlage-Puchta's Lemma 4)
and `p_n ∼ n log n` (the prime number theorem).
-/

noncomputable section

namespace ErdosProblems.Erdos251.PaperCompleteR21

open Filter Finset
open scoped Topology BigOperators
open ErdosProblems.Erdos251
open PaperR11.Nonconcentration

/-! ## Telescoping the gaps -/

theorem prime0_zero' : prime0 0 = 2 := by
  simp [prime0, Nat.nth_prime_zero_eq_two]

theorem two_le_prime0 (n : ℕ) : 2 ≤ prime0 n := by
  induction n with
  | zero => rw [prime0_zero']
  | succ n ih => exact le_trans ih (prime0_mono_step n)

/-- `Σ_{i < n} g_i = p_n - 2`. -/
theorem sum_range_primeGap0 (n : ℕ) :
    ∑ i ∈ range n, primeGap0 i = prime0 n - 2 := by
  induction n with
  | zero => simp [prime0_zero']
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 := prime0_mono_step n
    have h2 := two_le_prime0 n
    unfold primeGap0
    omega

/-! ## The perturbed cumulative positions -/

/-- `P_n = 2 + Σ_{i < n} (g_i + M δ_i)` equals `p_n + M Σ_{i<n} δ_i`. -/
theorem perturbed_position_eq (M : ℕ) (δ : ℕ → ℕ) (n : ℕ) :
    2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) =
      prime0 n + M * ∑ i ∈ range n, δ i := by
  rw [Finset.sum_add_distrib, sum_range_primeGap0, Finset.mul_sum]
  have h := two_le_prime0 n
  omega

/-- **The cumulative bound `p_n ≤ P_n ≤ p_n + Mn`.** -/
theorem perturbed_position_bounds (M : ℕ) (δ : ℕ → ℕ) (hδ : ∀ n, δ n ≤ 1) (n : ℕ) :
    prime0 n ≤ 2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) ∧
      2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) ≤ prime0 n + M * n := by
  rw [perturbed_position_eq M δ n]
  have hs : ∑ i ∈ range n, δ i ≤ n := by
    calc ∑ i ∈ range n, δ i ≤ ∑ _i ∈ range n, 1 :=
          Finset.sum_le_sum (fun i _ => hδ i)
      _ = n := by simp
  exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.mul_le_mul_left M hs) _⟩

/-! ## The asymptotic, from the prime number theorem as an explicit hypothesis -/

theorem div_le_div_same {x y c : ℝ} (hxy : x ≤ y) (hc : 0 < c) : x / c ≤ y / c := by
  have h : 0 ≤ (y - x) / c := div_nonneg (by linarith) hc.le
  rw [sub_div] at h
  linarith

theorem tendsto_const_div_log_atTop_zero (M : ℝ) :
    Tendsto (fun n : ℕ => M / Real.log n) atTop (𝓝 0) :=
  Filter.Tendsto.div_atTop tendsto_const_nhds
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- If `p_n ∼ n log n` and `p_n ≤ P_n ≤ p_n + Mn`, then `P_n ∼ n log n`. -/
theorem position_asymptotic_of_prime_asymptotic
    (P p : ℕ → ℝ) (M : ℝ)
    (hle : ∀ n, p n ≤ P n) (hge : ∀ n, P n ≤ p n + M * n)
    (hp : Tendsto (fun n : ℕ => p n / ((n : ℝ) * Real.log n)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => P n / ((n : ℝ) * Real.log n)) atTop (𝓝 1) := by
  have hupper : Tendsto
      (fun n : ℕ => p n / ((n : ℝ) * Real.log n) + M / Real.log n) atTop (𝓝 1) := by
    have h := hp.add (tendsto_const_div_log_atTop_zero M)
    simpa using h
  have hev : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) ∧ 0 < Real.log n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact ⟨by linarith, Real.log_pos (by linarith)⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hp hupper ?_ ?_
  · filter_upwards [hev] with n hn
    obtain ⟨hn0, hlog⟩ := hn
    exact div_le_div_same (hle n) (mul_pos hn0 hlog)
  · filter_upwards [hev] with n hn
    obtain ⟨hn0, hlog⟩ := hn
    have hne : (n : ℝ) ≠ 0 := hn0.ne'
    have hlne : Real.log n ≠ 0 := hlog.ne'
    have hstep : P n / ((n : ℝ) * Real.log n) ≤ (p n + M * n) / ((n : ℝ) * Real.log n) :=
      div_le_div_same (hge n) (mul_pos hn0 hlog)
    have hsplit : (p n + M * (n : ℝ)) / ((n : ℝ) * Real.log n) =
        p n / ((n : ℝ) * Real.log n) + M / Real.log n := by
      first
        | (field_simp; ring)
        | field_simp
    rwa [hsplit] at hstep

/-! ## The full corollary -/

/-- **`long251:res:nonconc-primes`.**  `hSP` is Schlage-Puchta's Lemma 4 for the
actual gaps and `hPNT` is the prime number theorem in the form `p_n ∼ n log n`;
both are external inputs of the paper's proof, so both are explicit
hypotheses. -/
theorem nonconcentration_does_not_force_irrationality
    (M : ℕ) (hM : 0 < M) (K : ℕ)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ)))
    (hPNT : Tendsto (fun n : ℕ => (prime0 n : ℝ) / ((n : ℝ) * Real.log n))
      atTop (𝓝 1)) :
    ∃ (b : ℕ → ℕ) (q : ℚ),
      HasSum (fun n => (b n : ℝ) / 2 ^ (n + 1)) (q : ℝ) ∧
      (∀ n < K, b n = primeGap0 n) ∧
      (∀ n, (b n : ℤ) - primeGap0 n = 0 ∨ (b n : ℤ) - primeGap0 n = (M : ℤ)) ∧
      (∀ n, primeGap0 n ≤ b n) ∧
      (∀ n, b n % M = primeGap0 n % M) ∧
      FixedBlockNonconcentration (fun n => (b n : ℤ)) ∧
      (∀ n, prime0 n ≤ 2 + ∑ i ∈ range n, b i) ∧
      (∀ n, 2 + ∑ i ∈ range n, b i ≤ prime0 n + M * n) ∧
      Tendsto (fun n : ℕ => ((2 + ∑ i ∈ range n, b i : ℕ) : ℝ) / ((n : ℝ) * Real.log n))
        atTop (𝓝 1) := by
  classical
  obtain ⟨δ, q, hδ1, hδK, hsum⟩ := exists_rational_bounded_perturbation_primeGap M hM K
  refine ⟨fun n => primeGap0 n + M * δ n, q, hsum, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    simp [hδK n hn]
  · intro n
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hδ1 n) with h | h <;> simp [h]
  · intro n
    exact Nat.le_add_right _ _
  · intro n
    simp [Nat.add_mul_mod_self_left]
  · refine finite_perturbation_stability (fun n => (primeGap0 n : ℤ))
      (fun n => ((primeGap0 n + M * δ n : ℕ) : ℤ)) ({0, (M : ℤ)} : Finset ℤ) hSP ?_
    intro n
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hδ1 n) with h | h <;> simp [h]
  · intro n
    exact (perturbed_position_bounds M δ hδ1 n).1
  · intro n
    exact (perturbed_position_bounds M δ hδ1 n).2
  · refine position_asymptotic_of_prime_asymptotic
      (fun n => ((2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) : ℕ) : ℝ))
      (fun n => (prime0 n : ℝ)) (M : ℝ) (fun n => ?_) (fun n => ?_) hPNT
    · show ((prime0 n : ℕ) : ℝ) ≤
        ((2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) : ℕ) : ℝ)
      exact_mod_cast (perturbed_position_bounds M δ hδ1 n).1
    · show ((2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) : ℕ) : ℝ) ≤
        ((prime0 n : ℕ) : ℝ) + (M : ℝ) * (n : ℝ)
      have h := (perturbed_position_bounds M δ hδ1 n).2
      have h2 : ((2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) : ℕ) : ℝ) ≤
          ((prime0 n + M * n : ℕ) : ℝ) := by exact_mod_cast h
      have h3 : ((prime0 n + M * n : ℕ) : ℝ) = ((prime0 n : ℕ) : ℝ) + (M : ℝ) * (n : ℝ) := by
        first
          | (push_cast; ring)
          | push_cast
      rwa [h3] at h2

end ErdosProblems.Erdos251.PaperCompleteR21

#print axioms ErdosProblems.Erdos251.PaperCompleteR21.sum_range_primeGap0
#print axioms ErdosProblems.Erdos251.PaperCompleteR21.perturbed_position_eq
#print axioms ErdosProblems.Erdos251.PaperCompleteR21.perturbed_position_bounds
#print axioms ErdosProblems.Erdos251.PaperCompleteR21.position_asymptotic_of_prime_asymptotic
#print axioms ErdosProblems.Erdos251.PaperCompleteR21.nonconcentration_does_not_force_irrationality
