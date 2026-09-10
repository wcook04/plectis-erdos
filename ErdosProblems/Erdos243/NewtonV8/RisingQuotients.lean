import ErdosProblems.Erdos243.NewtonV8.Discrete

/-! Exact quotient recurrence, verified locally by the focused
Newton-classification build on 2026-09-09. -/
noncomputable section
namespace Erdos243V8
open Filter
open scoped BigOperators Topology

def rising : ℕ → ℕ → ℝ
  | 0, _ => 1
  | j + 1, n => (n : ℝ) * rising j (n + 1)

theorem rising_last (j n : ℕ) :
    rising (j + 1) n = rising j n * ((n : ℝ) + (j : ℝ)) := by
  induction j generalizing n with
  | zero => simp [rising]
  | succ j ih =>
      change (n : ℝ) * rising (j+1) (n+1) =
        ((n : ℝ)*rising j (n+1))*((n : ℝ)+((j+1 : ℕ) : ℝ))
      rw [ih]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

theorem rising_one_le (j n : ℕ) (hn : 1 ≤ n) : 1 ≤ rising j n := by
  induction j generalizing n with
  | zero => simp [rising]
  | succ j ih =>
      have h₁ := ih (n + 1) (by omega)
      have h₂ : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [rising]
      nlinarith

def rateResidual (C : ℕ → ℝ) (lam : ℝ) (n : ℕ) : ℝ :=
  C (n + 1) - C n - lam * C n / (n : ℝ)

def risingQuotient (C : ℕ → ℝ) (j n : ℕ) : ℝ := C n / rising j n

/-- All denominators and the excluded n=0 boundary are explicit. -/
theorem rising_quotient_difference (C : ℕ → ℝ) (lam : ℝ) (j n : ℕ)
    (hn : 1 ≤ n) :
    risingQuotient C j (n + 1) - risingQuotient C j n =
      (lam - (j : ℝ)) * risingQuotient C (j + 1) n +
        rateResidual C lam n / rising j (n + 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hR : 0 < rising j n := lt_of_lt_of_le zero_lt_one (rising_one_le j n hn)
  have hS : 0 < rising j (n + 1) :=
    lt_of_lt_of_le zero_lt_one (rising_one_le j (n + 1) (by omega))
  have hnJ : (0 : ℝ) < (n : ℝ) + (j : ℝ) := by positivity
  have hrel : (n : ℝ) * rising j (n + 1) =
      rising j n * ((n : ℝ) + (j : ℝ)) := rising_last j n
  have hq : C n / rising j n =
      ((n : ℝ) + (j : ℝ)) * C n / ((n : ℝ) * rising j (n + 1)) := by
    rw [hrel]
    field_simp [ne_of_gt hR, ne_of_gt hnJ]
  simp only [risingQuotient, rateResidual, rising]
  rw [hq]
  field_simp [ne_of_gt hnpos, ne_of_gt hS]
  <;> ring

/-- A concrete, unconditional finite-difference producer from the residual
limit. No Gamma function, logarithmic product, polynomial extraction oracle,
or unproved number-field assertion occurs in this theorem. -/
theorem cubic_residual_forces_fourth_difference (C : ℕ → ℤ)
    (he : Tendsto (rateResidual (fun n => (C n : ℝ)) 3) atTop (𝓝 0)) :
    ∃ N, ∀ n, N ≤ n → fd 4 C n = 0 := by
  apply fourth_difference_eventually_zero C
    (risingQuotient (fun n => (C n : ℝ)))
    (rateResidual (fun n => (C n : ℝ)) 3)
    (fun j n => rising j (n + 1))
  · intro n
    simp [risingQuotient, rising]
  · intro j
    exact eventually_atTop.2 ⟨1, fun n hn =>
      rising_quotient_difference (fun n => (C n : ℝ)) 3 j n hn⟩
  · intro j
    exact Filter.Eventually.of_forall fun n => rising_one_le j (n + 1) (by omega)
  · exact he

end Erdos243V8
end
