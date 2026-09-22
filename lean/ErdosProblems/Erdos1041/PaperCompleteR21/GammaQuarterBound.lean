import Mathlib

/-!
# Erdős 1041, `res:one-root-gamma-false`: the bound `Γ(1/4) ≤ 3.63`

This is the numerical input `hGammaQuarter` of `Lobe.one_root_gamma_false`
(`LobeAndArity.lean`), proved from Mathlib's Bohr–Mollerup machinery.

`log ∘ Γ` is convex on `(0, ∞)` (`Real.convexOn_log_Gamma`) and satisfies
`log Γ(y + 1) = log Γ(y) + log y`.  For `0 < x ≤ 1`, convexity on the unit
interval `[n + 1, n + 2]` gives the Euler–Gauss upper bound
`Γ(x) ≤ (n + 1)^x n! / (x (x + 1) ⋯ (x + n))`
(`Real.BohrMollerup.le_logGammaSeq`).  At `x = 1/4` and `n = 77` the right side
is `3.629974…`, below `3.63`; the true value is `Γ(1/4) = 3.625609…`, and `n = 76`
would give `3.630031…`, which is too large.  After raising to the fourth power
the comparison is an inequality between explicit rationals, which `norm_num`
checks in exact rational arithmetic, with no floating point.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21.Lobe

open Finset

/-- The functional equation of `log ∘ Γ`, in the form the Bohr–Mollerup lemmas use. -/
theorem log_Gamma_add_one {y : ℝ} (hy : 0 < y) :
    (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
  simp only [Function.comp_apply]
  rw [Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]

/-- The Euler–Gauss product at `x = 1/4`, `n = 77`, raised to the fourth power, is at most
`3.63 ^ 4`.  An exact comparison of explicit rationals. -/
theorem gauss_product_quarter_77_le :
    (78 : ℝ) * ((Nat.factorial 77 : ℕ) : ℝ) ^ 4
      ≤ (3.63 : ℝ) ^ 4 * (∏ m ∈ range 78, ((1 : ℝ) / 4 + (m : ℝ))) ^ 4 := by
  norm_num [Finset.prod_range_succ, Nat.factorial]

/-- The Euler–Gauss upper bound for `log Γ(1/4)` at `n = 77`, from log-convexity. -/
theorem log_Gamma_quarter_le :
    Real.log (Real.Gamma (1 / 4))
      ≤ (1 / 4) * Real.log 78 + Real.log ((Nat.factorial 77 : ℕ) : ℝ)
        - Real.log (∏ m ∈ range 78, ((1 : ℝ) / 4 + (m : ℝ))) := by
  have h := Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma (@log_Gamma_add_one)
    (x := 1 / 4) (by norm_num) (by norm_num) 77
  rw [Real.BohrMollerup.logGammaSeq] at h
  have e1 : (Real.log ∘ Real.Gamma) 1 = 0 := by
    simp [Real.Gamma_one]
  have e2 : Real.log (((77 : ℕ) : ℝ) + 1) = Real.log 78 := by
    norm_num
  have e3 : ∑ m ∈ range (77 + 1), Real.log (1 / 4 + ((m : ℕ) : ℝ))
      = Real.log (∏ m ∈ range 78, ((1 : ℝ) / 4 + (m : ℝ))) := by
    rw [Real.log_prod]
    intro m _
    positivity
  have e4 : (Real.log ∘ Real.Gamma) (1 / 4) = Real.log (Real.Gamma (1 / 4)) := rfl
  rw [e1, e2, e3, e4] at h
  linarith

/-- **`Γ(1/4) ≤ 3.63`**: the second named input of `Lobe.one_root_gamma_false`. -/
theorem gamma_quarter_le_363 : Real.Gamma (1 / 4) ≤ 3.63 := by
  have hG : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hF : (0 : ℝ) < ((Nat.factorial 77 : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos 77
  have hP : (0 : ℝ) < ∏ m ∈ range 78, ((1 : ℝ) / 4 + (m : ℝ)) :=
    Finset.prod_pos fun m _ => by positivity
  have hnum := Real.log_le_log (by positivity) gauss_product_quarter_77_le
  rw [Real.log_mul (by norm_num) (pow_pos hF 4).ne', Real.log_mul (by norm_num) (pow_pos hP 4).ne',
    Real.log_pow, Real.log_pow, Real.log_pow] at hnum
  push_cast at hnum
  have hle := log_Gamma_quarter_le
  have hlog : Real.log (Real.Gamma (1 / 4)) ≤ Real.log 3.63 := by
    linarith
  exact (Real.log_le_log_iff hG (by norm_num)).1 hlog

end ErdosProblems.Erdos1041.PaperCompleteR21.Lobe
