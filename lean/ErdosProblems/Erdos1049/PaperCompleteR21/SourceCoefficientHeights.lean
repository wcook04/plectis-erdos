import ErdosProblems.Erdos1049.SourceHeightRateR14

/-!
# Erdős #1049: quadratic logarithmic coefficient heights of the constructed pair

Paper restatement of `long1049:res:sourceheight`:

> There is a constant `h` with `log max(H(U_n), H(V_n)) ≤ h n²` for every
> `n ≥ 1`, where `U_n` and `V_n` are the polynomials of
> `long1049:eq:integer-polynomial-pair`.

Correspondence of the objects.

* `U_n` is `PaperR11.sourceU n`.  The paper's `U_n = X^{-M_n}(D_N/Ω_n)A_n` is the
  tree's `PaperR11.actual_A_polynomial_inclusion`, which proves
  `D_N · A_n = Ω_n · X^{M_n} · sourceU n`.
* `V_n` is `PaperR13.sourceV n`.  The paper's `V_n = X^{-M_n}(D_N/Ω_n)B_n` is the
  tree's `PaperR13.actual_Omega_remainder_zero` together with
  `sourceBWithoutMonomial n = Ω_n · sourceV n`; the divisibility is proved in the
  tree, not assumed from Zudilin's Lemma 7.
* `H(P)` is `PaperR9.maxCoeffNat P = sup_i |[X^i]P|`, the naive height, and
  `max(H(U_n), H(V_n))` is `PaperR9.maxPairHeight sourceU sourceV n`.

The tree already proves the eventual form `log H_n ≤ ε n²` for every `ε > 0`
(`PaperR14.actual_maxPairHeight_log_upper_zero`).  What is added here is the
paper's uniform statement: one constant, valid at *every* `n ≥ 1`.

The sentence following the environment in the paper — "Lemma
`long1049:res:sourceheight` is an ordinary proof and is not kernel-checked" — is a
status remark about the manuscript, not a mathematical clause, so it is not
formalised.
-/

namespace ErdosProblems.Erdos1049.PaperCompleteR21

open ErdosProblems.Erdos1049
open Filter

/-- `max(H(U_n), H(V_n))` in the tree's packaged form. -/
theorem maxPairHeight_source_eq (n : ℕ) :
    PaperR9.maxPairHeight PaperR11.sourceU PaperR13.sourceV n =
      ((max (PaperR9.maxCoeffNat (PaperR11.sourceU n))
        (PaperR9.maxCoeffNat (PaperR13.sourceV n)) : ℕ) : ℝ) := rfl

/-- **`long1049:res:sourceheight`.**  There is a constant `h` with
`log max(H(U_n), H(V_n)) ≤ h n²` for every `n ≥ 1`, where `U_n` and `V_n` are the
polynomials of `long1049:eq:integer-polynomial-pair` and `H` is the naive
(maximum-coefficient) height. -/
theorem exists_quadratic_source_height_bound :
    ∃ h : ℝ, ∀ n : ℕ, 1 ≤ n →
      Real.log
          ((max (PaperR9.maxCoeffNat (PaperR11.sourceU n))
            (PaperR9.maxCoeffNat (PaperR13.sourceV n)) : ℕ) : ℝ) ≤
        h * (n : ℝ) ^ 2 := by
  classical
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp
      (PaperR14.actual_maxPairHeight_log_upper_zero 1 one_pos)
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  set f : ℕ → ℝ := fun n =>
    Real.log (PaperR9.maxPairHeight PaperR11.sourceU PaperR13.sourceV n) with hf
  set C : ℝ := (Finset.range (N + 1)).sup' hne f with hC
  refine ⟨max 1 C, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hc1 : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  have hc0 : (0 : ℝ) ≤ max 1 C := le_trans zero_le_one hc1
  have hgoal :
      Real.log
          ((max (PaperR9.maxCoeffNat (PaperR11.sourceU n))
            (PaperR9.maxCoeffNat (PaperR13.sourceV n)) : ℕ) : ℝ) = f n := rfl
  rw [hgoal]
  by_cases hle : n ≤ N
  · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have h1 : f n ≤ C := by rw [hC]; exact Finset.le_sup' f hmem
    have h2 : f n ≤ max 1 C := h1.trans (le_max_right _ _)
    calc f n ≤ max 1 C := h2
      _ ≤ max 1 C * (n : ℝ) ^ 2 := le_mul_of_one_le_right hc0 hsq
  · have hlt : N < n := by omega
    have h3 := hN n (le_of_lt hlt)
    have h4 : f n ≤ (n : ℝ) ^ 2 := by
      simpa only [PaperR9.sqScale, zero_add, one_mul] using h3
    calc f n ≤ (n : ℝ) ^ 2 := h4
      _ ≤ max 1 C * (n : ℝ) ^ 2 := by nlinarith

end ErdosProblems.Erdos1049.PaperCompleteR21

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.maxPairHeight_source_eq
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.exists_quadratic_source_height_bound
