import ErdosProblems.Erdos257.WitnessBlockArithmetic
import ErdosProblems.Erdos257.WitnessBlockHarmonic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Reciprocal divergence of the actual clause support

Each coprime layer has a uniformly positive reciprocal mass on a progression
congruent to one. Unique layer indices make these contributions disjoint.
-/

noncomputable section
namespace ErdosProblems.Erdos257

def clauseProgressionIndex (D Q : ℕ) :=
  Σ k : ℕ, Fin ((2 ^ (D ^ (k + 1)) - 1) / Q + 1)

def clauseProgressionPoint (D Q : ℕ) (x : clauseProgressionIndex D Q) : ℕ :=
  D ^ (x.1 + 1) * (1 + x.2.val * Q)

theorem clauseProgression_cofactor_le (D Q : ℕ) (hQ : 0 < Q)
    (x : clauseProgressionIndex D Q) :
    1 + x.2.val * Q ≤ 2 ^ (D ^ (x.1 + 1)) := by
  have hj : x.2.val ≤ (2 ^ (D ^ (x.1 + 1)) - 1) / Q := Nat.le_of_lt_succ x.2.is_lt
  have hm := (Nat.le_div_iff_mul_le hQ).mp hj
  have hp : 0 < 2 ^ (D ^ (x.1 + 1)) := by positivity
  omega

theorem clauseProgression_mem (C : Finset ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hDQ : C.prod id ∣ Q) (x : clauseProgressionIndex (C.prod id) Q) :
    clauseProgressionPoint (C.prod id) Q x ∈ witnessClauseSupport C := by
  have hcop : Nat.Coprime (1 + x.2.val * Q) Q := by simp
  exact ⟨x.1 + 1, by omega, 1 + x.2.val * Q, by omega,
    clauseProgression_cofactor_le _ Q hQ x, hcop.of_dvd_right hDQ, rfl⟩

theorem clauseProgressionPoint_injective (C : Finset ℕ) (hCn : C.Nonempty)
    (hC : ∀ p ∈ C, Nat.Prime p) (Q : ℕ) (hQ : 0 < Q)
    (hDQ : C.prod id ∣ Q) :
    Function.Injective (clauseProgressionPoint (C.prod id) Q) := by
  rintro ⟨k, j⟩ ⟨l, t⟩ heq
  have hjcop : Nat.Coprime (1 + j.val * Q) Q := by simp
  have htcop : Nat.Coprime (1 + t.val * Q) Q := by simp
  have hpair := clause_layer_pair_unique C hCn hC (k + 1) (l + 1)
    (1 + j.val * Q) (1 + t.val * Q) (by omega) (by omega)
    (hjcop.of_dvd_right hDQ) (htcop.of_dvd_right hDQ) heq
  have hkl : k = l := by omega
  subst l
  have hjt : j = t := by
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hQ (Nat.add_left_cancel hpair.2)
  subst t
  rfl

theorem clauseProgression_row_reciprocal (D Q k : ℕ) :
    (∑ j : Fin ((2 ^ (D ^ (k + 1)) - 1) / Q + 1),
      (1 : ℝ) / (clauseProgressionPoint D Q ⟨k, j⟩ : ℝ)) =
      (1 / ((D ^ (k + 1) : ℕ) : ℝ)) *
        progressionHarmonicMass Q (2 ^ (D ^ (k + 1))) := by
  simp only [clauseProgressionPoint]
  refine (Fin.sum_univ_eq_sum_range
    (fun j => (1 : ℝ) / ((D ^ (k + 1) * (1 + j * Q) : ℕ) : ℝ)) _).trans ?_
  rw [progressionHarmonicMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.cast_mul, ← one_div_mul_one_div]
  congr 1
  push_cast
  ring

/-- The progression within every layer has reciprocal mass at least
`1/(2Q)`, independently of the layer index. -/
theorem clauseProgression_row_reciprocal_lower (D Q k : ℕ)
    (hD : 0 < D) (hQ : 0 < Q) :
    (1 : ℝ) / (2 * Q) ≤
      ∑ j : Fin ((2 ^ (D ^ (k + 1)) - 1) / Q + 1),
        (1 : ℝ) / (clauseProgressionPoint D Q ⟨k, j⟩ : ℝ) := by
  rw [clauseProgression_row_reciprocal]
  have hr : (0 : ℝ) < ((D ^ (k + 1) : ℕ) : ℝ) := by positivity
  have hl := dyadic_progressionHarmonicMass_half_lower Q (D ^ (k + 1)) hQ
  have hh := mul_le_mul_of_nonneg_left hl (le_of_lt (one_div_pos.mpr hr))
  convert hh using 1 <;> field_simp [hr.ne'] <;> ring

/-- The disjointly indexed progression layers have divergent reciprocal sum. -/
theorem not_summable_clauseProgression_reciprocal (D Q : ℕ)
    (hD : 0 < D) (hQ : 0 < Q) :
    ¬ Summable (fun x : clauseProgressionIndex D Q =>
      (1 : ℝ) / (clauseProgressionPoint D Q x : ℝ)) := by
  intro hs
  have hrows : Summable (fun k : ℕ =>
      ∑ j : Fin ((2 ^ (D ^ (k + 1)) - 1) / Q + 1),
        (1 : ℝ) / (clauseProgressionPoint D Q ⟨k, j⟩ : ℝ)) :=
    (hs.hasSum.sigma (fun k => hasSum_fintype _)).summable
  have hconst : Summable (fun _ : ℕ => (1 : ℝ) / (2 * Q)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun k => clauseProgression_row_reciprocal_lower D Q k hD hQ) hrows
  have hz := (summable_const_iff ((1 : ℝ) / (2 * Q))).mp hconst
  have hp : (0 : ℝ) < 1 / (2 * Q) := by positivity
  linarith

/-- Every nonempty finite prime clause produces an actual arithmetic host
whose ordinary reciprocal sum diverges. -/
theorem not_summable_reciprocal_witnessClauseSupport (C : Finset ℕ)
    (hCn : C.Nonempty) (hC : ∀ p ∈ C, Nat.Prime p) :
    ¬ Summable (Set.indicator (witnessClauseSupport C) (fun a : ℕ => (1 : ℝ) / a)) := by
  intro hs
  have hD := clause_product_pos C hC
  have hi := clauseProgressionPoint_injective C hCn hC (C.prod id) hD (dvd_refl _)
  have hsub := hs.comp_injective hi
  apply not_summable_clauseProgression_reciprocal (C.prod id) (C.prod id) hD hD
  apply hsub.congr
  intro x
  exact Set.indicator_of_mem (clauseProgression_mem C (C.prod id) hD (dvd_refl _) x) _

#print axioms not_summable_reciprocal_witnessClauseSupport

end ErdosProblems.Erdos257
end
