import ErdosProblems.Erdos257.WitnessBlockWeighted
import ErdosProblems.Erdos257.WitnessBlockWeightBound
import ErdosProblems.Erdos257.WitnessLogicSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Summability of an arithmetic clause met by a prime witness

The finite cofactor rows are dominated by the checked scalar clause series.
A chosen representation of each support element transfers that summability
to the actual set without requiring disjointness of the enlarged rows.
-/

noncomputable section
namespace ErdosProblems.Erdos257
open PaperCompleteR7

theorem clause_primeSetPart_pos (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (a : ℕ) :
    0 < primeSetPart P a := by
  exact Finset.prod_pos (fun p hp => Nat.pow_pos (hP p hp).pos)

theorem clause_primeWeightedTerm_nonneg (b : ℕ) (hb : 2 ≤ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (a : ℕ) :
    0 ≤ primeWeightedTerm b P a := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hden : 0 < (b : ℝ) ^ primeSetPart P a - 1 :=
    sub_pos.mpr (one_lt_pow₀ hbR (clause_primeSetPart_pos P hP a).ne')
  exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hden.le)

theorem primeWeightedTerm_clause_layer_le (b : ℕ) (hb : 2 ≤ b) (C P : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (hP : ∀ p ∈ P, Nat.Prime p)
    (k m : ℕ) (hm : 1 ≤ m) :
    primeWeightedTerm b P (C.prod id ^ k * m) ≤
      (((P ∩ C).prod id ^ k : ℕ) : ℝ) /
        ((((C.prod id ^ k : ℕ) : ℝ)) * ((b : ℝ) ^ ((P ∩ C).prod id ^ k) - 1)) *
          (1 / (m : ℝ)) := by
  have hg : 0 < (P ∩ C).prod id :=
    clause_product_pos (P ∩ C) (fun p hp => hC p (Finset.mem_inter.mp hp).2)
  have hx : 1 ≤ (P ∩ C).prod id ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hg.ne')
  have hu : 1 ≤ primeSetPart P m := clause_primeSetPart_pos P hP m
  have hbound := nat_mul_div_pow_mul_sub_one_le b ((P ∩ C).prod id ^ k)
    (primeSetPart P m) hb hx hu
  calc
    primeWeightedTerm b P (C.prod id ^ k * m) =
        (((((P ∩ C).prod id ^ k * primeSetPart P m : ℕ) : ℝ)) /
          ((b : ℝ) ^ ((P ∩ C).prod id ^ k * primeSetPart P m) - 1)) /
            ((C.prod id ^ k * m : ℕ) : ℝ) := by
      rw [primeWeightedTerm, primeSetPart_clause_layer C P hC k m (by omega)]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ ≤ ((((P ∩ C).prod id ^ k : ℕ) : ℝ) /
        ((b : ℝ) ^ ((P ∩ C).prod id ^ k) - 1)) /
          ((C.prod id ^ k * m : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hbound (Nat.cast_nonneg _)
    _ = _ := by
      push_cast
      simp only [div_eq_mul_inv, mul_inv]
      ring

theorem dyadic_harmonic_le_two_mul (r : ℕ) (hr : 1 ≤ r) :
    (∑ n ∈ Finset.range (2 ^ r), (1 : ℝ) / (n + 1)) ≤ 2 * r := by
  have h := harmonic_le_one_add_log (2 ^ r)
  have hlog : Real.log 2 ≤ (1 : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  calc
    (∑ n ∈ Finset.range (2 ^ r), (1 : ℝ) / (n + 1)) ≤
        1 + (r : ℝ) * Real.log 2 := by
      simpa [harmonic, Rat.cast_sum, one_div, Real.log_pow] using h
    _ ≤ 2 * r := by nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg r)]

def clauseFullIndex (D : ℕ) := Σ k : ℕ, Fin (2 ^ (D ^ (k + 1)))

def clauseFullPoint (D : ℕ) (x : clauseFullIndex D) : ℕ :=
  D ^ (x.1 + 1) * (x.2.val + 1)

theorem witnessClauseSupport_covered (C : Finset ℕ) :
    witnessClauseSupport C ⊆ Set.range (clauseFullPoint (C.prod id)) := by
  rintro a ⟨k, hk, m, hm, hcut, hcop, ha⟩
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hj : m - 1 < 2 ^ (C.prod id ^ (k - 1 + 1)) := by rw [hk']; omega
  refine ⟨⟨k - 1, ⟨m - 1, hj⟩⟩, ?_⟩
  simpa [clauseFullPoint, hk', hm'] using ha.symm

theorem summable_indicator_of_cover {ι : Type*} (f : ℕ → ℝ) (A : Set ℕ)
    (g : ι → ℕ) (hcover : A ⊆ Set.range g) (hs : Summable (fun x => f (g x))) :
    Summable (Set.indicator A f) := by
  classical
  have hrep : ∀ a : A, ∃ x : ι, g x = (a : ℕ) := fun a => hcover a.property
  choose rep hrep using hrep
  have hi : Function.Injective rep := by
    intro a b hab
    apply Subtype.ext
    exact (hrep a).symm.trans ((congrArg g hab).trans (hrep b))
  apply summable_subtype_iff_indicator.mp
  apply (hs.comp_injective hi).congr
  intro a
  exact congrArg f (hrep a)

theorem clauseFull_weighted_row_le (b : ℕ) (hb : 2 ≤ b) (C P : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (hP : ∀ p ∈ P, Nat.Prime p) (k : ℕ) :
    (∑ j : Fin (2 ^ (C.prod id ^ (k + 1))),
      primeWeightedTerm b P (clauseFullPoint (C.prod id) ⟨k, j⟩)) ≤
        2 * (((P ∩ C).prod id ^ (k + 1) : ℕ) : ℝ) /
          ((b : ℝ) ^ ((P ∩ C).prod id ^ (k + 1)) - 1) := by
  let r := C.prod id ^ (k + 1)
  let x := (P ∩ C).prod id ^ (k + 1)
  have hr : 0 < r := Nat.pow_pos (clause_product_pos C hC)
  have hx : 0 < x := Nat.pow_pos
    (clause_product_pos (P ∩ C) (fun p hp => hC p (Finset.mem_inter.mp hp).2))
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hden : 0 < (b : ℝ) ^ x - 1 := sub_pos.mpr (one_lt_pow₀ hbR hx.ne')
  have hcoef : 0 ≤ (x : ℝ) / ((r : ℝ) * ((b : ℝ) ^ x - 1)) := by positivity
  change (∑ j : Fin (2 ^ r), primeWeightedTerm b P (r * (j.val + 1))) ≤ _
  refine (Fin.sum_univ_eq_sum_range
    (fun j => primeWeightedTerm b P (r * (j + 1))) (2 ^ r)).trans_le ?_
  calc
    (∑ j ∈ Finset.range (2 ^ r), primeWeightedTerm b P (r * (j + 1))) ≤
        ∑ j ∈ Finset.range (2 ^ r),
          (x : ℝ) / ((r : ℝ) * ((b : ℝ) ^ x - 1)) * (1 / ((j + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact primeWeightedTerm_clause_layer_le b hb C P hC hP (k + 1) (j + 1) (by omega)
    _ = (x : ℝ) / ((r : ℝ) * ((b : ℝ) ^ x - 1)) *
        (∑ j ∈ Finset.range (2 ^ r), (1 : ℝ) / (j + 1)) := by
      rw [Finset.mul_sum]
      simp
    _ ≤ (x : ℝ) / ((r : ℝ) * ((b : ℝ) ^ x - 1)) * (2 * r) :=
      mul_le_mul_of_nonneg_left (dyadic_harmonic_le_two_mul r hr) hcoef
    _ = _ := by
      change (x : ℝ) / ((r : ℝ) * ((b : ℝ) ^ x - 1)) * (2 * r) =
        2 * x / ((b : ℝ) ^ x - 1)
      have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp [hrR, hden.ne']

/-- A witness meeting the clause has finite canonical weighted mass on the
actual constructed set, even with arbitrary additional witness primes. -/
theorem summable_primeWeightedTerm_witnessClauseSupport_of_inter_nonempty
    (b : ℕ) (hb : 2 ≤ b) (C P : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (hP : ∀ p ∈ P, Nat.Prime p)
    (hPC : (P ∩ C).Nonempty) :
    Summable (Set.indicator (witnessClauseSupport C) (primeWeightedTerm b P)) := by
  have hgpos : 0 < (P ∩ C).prod id :=
    clause_product_pos (P ∩ C) (fun p hp => hC p (Finset.mem_inter.mp hp).2)
  obtain ⟨p, hp⟩ := hPC
  have hgp : p ∣ (P ∩ C).prod id := Finset.dvd_prod_of_mem id hp
  have hg : 2 ≤ (P ∩ C).prod id :=
    (hP p (Finset.mem_inter.mp hp).1).two_le.trans (Nat.le_of_dvd hgpos hgp)
  have hscalar : Summable (fun k : ℕ =>
      2 * (((P ∩ C).prod id ^ (k + 1) : ℕ) : ℝ) /
        ((b : ℝ) ^ ((P ∩ C).prod id ^ (k + 1)) - 1)) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one, mul_div_assoc] using
      ((summable_clause_series b ((P ∩ C).prod id) hb hg).comp_injective
        Nat.succ_injective).mul_left 2
  have hrows : Summable (fun k : ℕ => ∑ j : Fin (2 ^ (C.prod id ^ (k + 1))),
      primeWeightedTerm b P (clauseFullPoint (C.prod id) ⟨k, j⟩)) :=
    Summable.of_nonneg_of_le
      (fun k => Finset.sum_nonneg (fun j _ => clause_primeWeightedTerm_nonneg b hb P hP _))
      (clauseFull_weighted_row_le b hb C P hC hP) hscalar
  have hs : Summable (fun x : clauseFullIndex (C.prod id) =>
      primeWeightedTerm b P (clauseFullPoint (C.prod id) x)) := by
    apply (summable_sigma_of_nonneg (fun x => clause_primeWeightedTerm_nonneg b hb P hP _)).mpr
    exact ⟨fun k => (hasSum_fintype _).summable, by simpa only [tsum_fintype] using hrows⟩
  exact summable_indicator_of_cover (primeWeightedTerm b P) (witnessClauseSupport C)
    (clauseFullPoint (C.prod id)) (witnessClauseSupport_covered C) hs

/-- Exact one-clause criterion for the constructed arithmetic support. -/
theorem summable_primeWeightedTerm_witnessClauseSupport_iff
    (b : ℕ) (hb : 2 ≤ b) (C P : Finset ℕ) (hCn : C.Nonempty)
    (hC : ∀ p ∈ C, Nat.Prime p) (hP : ∀ p ∈ P, Nat.Prime p) :
    Summable (Set.indicator (witnessClauseSupport C) (primeWeightedTerm b P)) ↔
      (P ∩ C).Nonempty := by
  constructor
  · intro hs
    by_contra hn
    have hdis : Disjoint P C := Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hn)
    exact not_summable_primeWeightedTerm_witnessClauseSupport_of_disjoint
      b hb C P hCn hC hP hdis hs
  · exact summable_primeWeightedTerm_witnessClauseSupport_of_inter_nonempty b hb C P hC hP

#print axioms summable_primeWeightedTerm_witnessClauseSupport_iff

end ErdosProblems.Erdos257
end
