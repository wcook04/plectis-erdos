import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateFiniteDifference

/-!
# Erdős 243: limit transport for the cubic finite-difference extraction

The paper's analytic comparison produces a residual whose first forward
difference tends to zero.  This file proves that this is exactly enough for
the fourth difference of the integer numerator to tend to zero, because the
rising cubic has identically zero fourth difference.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

def realForwardDiff (u : ℕ → ℝ) (n : ℕ) : ℝ := u (n + 1) - u n

def iterRealForwardDiff : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, u => u
  | k + 1, u => realForwardDiff (iterRealForwardDiff k u)

@[simp] theorem iterRealForwardDiff_zero (u : ℕ → ℝ) :
    iterRealForwardDiff 0 u = u := rfl

@[simp] theorem iterRealForwardDiff_succ (k : ℕ) (u : ℕ → ℝ) :
    iterRealForwardDiff (k + 1) u = realForwardDiff (iterRealForwardDiff k u) := rfl

theorem realForwardDiff_tendsto_zero
    {u : ℕ → ℝ} (hu : Tendsto u atTop (nhds 0)) :
    Tendsto (realForwardDiff u) atTop (nhds 0) := by
  simpa [realForwardDiff, Function.comp_def] using
    (hu.comp (tendsto_add_atTop_nat 1)).sub hu

/-- Every fixed further forward difference of a null sequence is null. -/
theorem iterRealForwardDiff_tendsto_zero
    {u : ℕ → ℝ} (hu : Tendsto u atTop (nhds 0)) :
    ∀ k : ℕ, Tendsto (iterRealForwardDiff k u) atTop (nhds 0)
  | 0 => hu
  | k + 1 => realForwardDiff_tendsto_zero (iterRealForwardDiff_tendsto_zero hu k)

theorem iterRealForwardDiff_add (k : ℕ) (u v : ℕ → ℝ) :
    iterRealForwardDiff k (fun n => u n + v n) =
      fun n => iterRealForwardDiff k u n + iterRealForwardDiff k v n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext n
      simp only [iterRealForwardDiff_succ, realForwardDiff, ih]
      ring

theorem iterRealForwardDiff_const_mul (k : ℕ) (c : ℝ) (u : ℕ → ℝ) :
    iterRealForwardDiff k (fun n => c * u n) =
      fun n => c * iterRealForwardDiff k u n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext n
      simp only [iterRealForwardDiff_succ, realForwardDiff, ih]
      ring

theorem iterIntForwardDiff_cast (k : ℕ) (u : ℕ → ℤ) (n : ℕ) :
    (iterIntForwardDiff k u n : ℝ) =
      iterRealForwardDiff k (fun j => (u j : ℝ)) n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      simp only [iterIntForwardDiff_succ, iterRealForwardDiff_succ, intForwardDiff,
        realForwardDiff, Int.cast_sub, ih]

/-- The rising cubic used in the paper. -/
def risingCubic (n : ℕ) : ℝ := (n : ℝ) * (n + 1) * (n + 2)

theorem fourth_difference_risingCubic (n : ℕ) :
    iterRealForwardDiff 4 risingCubic n = 0 := by
  norm_num [iterRealForwardDiff, realForwardDiff, risingCubic]
  ring

/-- Exact analytic-to-discrete interface for the cubic-rate argument.  If the
integer numerator is a scalar multiple of the rising cubic plus a residual
whose first difference tends to zero, then its fourth integer difference tends
to zero after casting to `ℝ`. -/
theorem fourth_int_difference_tendsto_zero_of_cubic_residual
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ)
    (hdecomp : (fun n => (C n : ℝ)) = fun n => K * risingCubic n + r n)
    (hr : Tendsto (realForwardDiff r) atTop (nhds 0)) :
    Tendsto (fun n => (iterIntForwardDiff 4 C n : ℝ)) atTop (nhds 0) := by
  have hres : Tendsto (iterRealForwardDiff 3 (realForwardDiff r)) atTop (nhds 0) :=
    iterRealForwardDiff_tendsto_zero hr 3
  have hcubic : iterRealForwardDiff 4 (fun n => K * risingCubic n) = 0 := by
    rw [iterRealForwardDiff_const_mul]
    funext n
    simp [fourth_difference_risingCubic]
  have hfour : iterRealForwardDiff 4 (fun n => (C n : ℝ)) =
      iterRealForwardDiff 4 r := by
    rw [hdecomp, iterRealForwardDiff_add, hcubic]
    funext n
    simp
  have hrfour : Tendsto (iterRealForwardDiff 4 r) atTop (nhds 0) := by
    simpa [iterRealForwardDiff] using hres
  simpa only [iterIntForwardDiff_cast, hfour] using hrfour

/-- Combined with the integer lemma, the third difference is eventually
constant. -/
theorem cubic_residual_gives_eventually_constant_third_difference
    (C : ℕ → ℤ) (K : ℝ) (r : ℕ → ℝ)
    (hdecomp : (fun n => (C n : ℝ)) = fun n => K * risingCubic n + r n)
    (hr : Tendsto (realForwardDiff r) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N :=
  third_difference_eventually_constant_of_fourth_tendsto_zero C
    (fourth_int_difference_tendsto_zero_of_cubic_residual C K r hdecomp hr)

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.fourth_int_difference_tendsto_zero_of_cubic_residual
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.cubic_residual_gives_eventually_constant_third_difference

end ErdosProblems.Erdos243.PaperCompleteR20
