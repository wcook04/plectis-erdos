import ErdosProblems.Erdos243.NewtonV8.SharpRegularRateGrowth
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Eventual Newton interpolation for the retained general-rate argument

Status: verified locally by the focused Newton-classification build on
2026-09-09. No project axiom or placeholder is
introduced.

The principal theorem is purely discrete: if the `j`-th integer forward
difference of a sequence vanishes from `N` onward and `0 < j`, then the
sequence agrees from `N` onward with a rational polynomial of degree `< j`.
The last theorem composes this result with the exact regular-rate producer.
It does not yet identify `lambda` with the polynomial degree or prove the
final rising-factorial classification.
-/

noncomputable section

open Finset Function Polynomial

namespace Erdos243V8

/-- The project-local recursive forward difference is the iterate of
Mathlib's additive forward-difference operator with step one. -/
theorem fd_eq_fwdDiff_iter {R : Type*} [AddCommGroup R]
    (k : ℕ) (f : ℕ → R) (n : ℕ) :
    fd k f n = (fwdDiff 1)^[k] f n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [fd, fwdDiff, ih]

/-- Translation commutes with every order of the project-local forward
difference. -/
theorem fd_comp_add {R : Type*} [AddCommGroup R]
    (f : ℕ → R) (N k n : ℕ) :
    fd k (fun t ↦ f (t + N)) n = fd k f (n + N) := by
  calc
    fd k (fun t ↦ f (t + N)) n =
        (fwdDiff 1)^[k] (fun t ↦ f (t + N)) n :=
          fd_eq_fwdDiff_iter k _ n
    _ = (fwdDiff 1)^[k] f (n + N) :=
      fwdDiff_iter_comp_add (h := (1 : ℕ)) f N k n
    _ = fd k f (n + N) := (fd_eq_fwdDiff_iter k f (n + N)).symm

/-- The Newton polynomial with coefficients given by the forward differences
of an integer-valued sequence at zero. -/
def newtonPolynomialInt (g : ℕ → ℤ) (j : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range j,
    ((((fwdDiff 1)^[k] g 0 : ℤ) : ℚ) / (k.factorial : ℚ)) •
      descPochhammer ℚ k

/-- Evaluation of one falling-factorial Newton term. -/
theorem eval_newtonTermInt (a : ℤ) (k t : ℕ) :
    (((a : ℚ) / (k.factorial : ℚ)) •
      descPochhammer ℚ k).eval (t : ℚ) =
      (t.choose k : ℚ) * (a : ℚ) := by
  rw [Polynomial.eval_smul]
  simp only [smul_eq_mul]
  rw [Nat.cast_choose_eq_descPochhammer_div (K := ℚ)]
  have hk : (k.factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp [hk]

/-- Once the `j`-th forward difference is identically zero, all higher
forward differences are identically zero as well. -/
theorem fwdDiff_iter_eq_zero_of_ge
    (g : ℕ → ℤ) (j : ℕ)
    (hzero : (fwdDiff 1)^[j] g = 0) :
    ∀ k, j ≤ k → (fwdDiff 1)^[k] g = 0 := by
  intro k hjk
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  rw [Nat.add_comm, Function.iterate_add_apply, hzero]
  have hz : fwdDiff (1 : ℕ) (0 : ℕ → ℤ) = 0 := by
    funext n
    simp [fwdDiff]
  exact Function.iterate_fixed hz r

/-- Gregory--Newton interpolation, truncated using the vanishing tail of
forward differences. -/
theorem newtonPolynomialInt_eval
    (g : ℕ → ℤ) (j : ℕ)
    (hzero : (fwdDiff 1)^[j] g = 0) (t : ℕ) :
    (newtonPolynomialInt g j).eval (t : ℚ) = (g t : ℚ) := by
  let s : ℕ → ℚ := fun k ↦
    (t.choose k : ℚ) * (((fwdDiff 1)^[k] g 0 : ℤ) : ℚ)
  have htail := fwdDiff_iter_eq_zero_of_ge g j hzero
  have hsums :
      (∑ k ∈ Finset.range (t + 1), s k) =
        ∑ k ∈ Finset.range j, s k := by
    rcases le_total j (t + 1) with hjt | htj
    · have hIco : ∑ k ∈ Finset.Ico j (t + 1), s k = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hk0 := congrFun (htail k (Finset.mem_Ico.mp hk).1) 0
        simp [s, hk0]
      have hsplit := Finset.sum_range_add_sum_Ico s hjt
      rw [hIco, add_zero] at hsplit
      exact hsplit.symm
    · have hIco : ∑ k ∈ Finset.Ico (t + 1) j, s k = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have htk : t < k := by
          have := (Finset.mem_Ico.mp hk).1
          omega
        simp [s, Nat.choose_eq_zero_of_lt htk]
      have hsplit := Finset.sum_range_add_sum_Ico s htj
      rw [hIco, add_zero] at hsplit
      exact hsplit
  have hnewtonZ :=
    shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) g t 0
  have hnewtonQ : (g t : ℚ) =
      ∑ k ∈ Finset.range (t + 1), s k := by
    have hcast := congrArg (fun z : ℤ ↦ (z : ℚ)) hnewtonZ
    simpa [s, nsmul_eq_mul] using hcast
  calc
    (newtonPolynomialInt g j).eval (t : ℚ) =
        ∑ k ∈ Finset.range j, s k := by
          simp only [newtonPolynomialInt, Polynomial.eval_finset_sum,
            eval_newtonTermInt, s]
    _ = ∑ k ∈ Finset.range (t + 1), s k := hsums.symm
    _ = (g t : ℚ) := hnewtonQ.symm

/-- For positive truncation order, the Newton polynomial has degree strictly
less than that order. -/
theorem newtonPolynomialInt_natDegree_lt
    (g : ℕ → ℤ) (j : ℕ) (hj : 0 < j) :
    (newtonPolynomialInt g j).natDegree < j := by
  have hdeg : (newtonPolynomialInt g j).natDegree ≤ j - 1 := by
    rw [newtonPolynomialInt]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    have hkj : k < j := Finset.mem_range.mp hk
    exact (Polynomial.natDegree_smul_le _ _).trans <| by
      rw [descPochhammer_natDegree]
      omega
  omega

/-- Eventual vanishing of an integer `j`-th difference gives an eventual
rational polynomial in the original index, with the exact degree bound
`degree < j`. -/
theorem exists_eventual_polynomial_of_fd_zero
    (f : ℕ → ℤ) (j N : ℕ) (hj : 0 < j)
    (hzero : ∀ n, N ≤ n → fd j f n = 0) :
    ∃ Q : ℚ[X], Q.natDegree < j ∧
      ∀ n, N ≤ n → Q.eval (n : ℚ) = (f n : ℚ) := by
  let g : ℕ → ℤ := fun t ↦ f (t + N)
  have hgj : (fwdDiff 1)^[j] g = 0 := by
    funext t
    rw [← fd_eq_fwdDiff_iter]
    change fd j (fun u ↦ f (u + N)) t = 0
    rw [fd_comp_add]
    exact hzero (t + N) (by omega)
  let P : ℚ[X] := newtonPolynomialInt g j
  let Q : ℚ[X] := P.comp (Polynomial.X - Polynomial.C (N : ℚ))
  have hPdeg : P.natDegree < j :=
    newtonPolynomialInt_natDegree_lt g j hj
  have hQle : Q.natDegree ≤ P.natDegree := by
    have hc := Polynomial.natDegree_comp_le
      (p := P) (q := Polynomial.X - Polynomial.C (N : ℚ))
    simpa only [Q, Polynomial.natDegree_X_sub_C, Nat.mul_one] using hc
  refine ⟨Q, hQle.trans_lt hPdeg, ?_⟩
  intro n hn
  have hcast : (n : ℚ) - (N : ℚ) = ((n - N : ℕ) : ℚ) := by
    rw [Nat.cast_sub hn]
  simp only [Q, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [hcast]
  have hP := newtonPolynomialInt_eval g j hgj (n - N)
  simpa [P, g, Nat.sub_add_cancel hn] using hP

/-- Exact C010 composition through the polynomial-extraction stage. The
retained ratio hypothesis supplies eventual difference vanishing at every
natural order strictly above `lambda`; Newton interpolation then supplies the
eventual rational polynomial of degree below that order. -/
theorem regularRate_exists_eventual_rational_polynomial
    (C : ℕ → ℕ) (lam : ℝ)
    (hreg : Erdos243V6.RegularRateHypothesis C lam)
    (j : ℕ) (hj : lam < j) :
    ∃ Q : ℚ[X], Q.natDegree < j ∧
      ∃ N, ∀ n : ℕ, N ≤ n → Q.eval (n : ℚ) = (C n : ℚ) := by
  obtain ⟨N, hzero⟩ := general_rate_difference_eventually_zero C lam hreg j hj
  have hjposR : (0 : ℝ) < (j : ℝ) := by
    linarith [hreg.2.1]
  have hjpos : 0 < j := by exact_mod_cast hjposR
  obtain ⟨Q, hQdeg, hQ⟩ :=
    exists_eventual_polynomial_of_fd_zero
      (fun n ↦ (C n : ℤ)) j N hjpos hzero
  exact ⟨Q, hQdeg, N, fun (n : ℕ) hn ↦ by simpa using hQ n hn⟩

end Erdos243V8
end
