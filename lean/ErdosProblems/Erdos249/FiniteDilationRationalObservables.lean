import ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables

/-!
# Rational observables across finitely many dilations

The integer mixed-word theorem applies after subtracting each observable's
value at residue zero and clearing denominators once for the entire finite
family.  This file isolates that simultaneous clearing step.
-/

namespace ErdosProblems.Erdos249.FiniteDilationRationalObservables

open scoped BigOperators
open ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables
open ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables

/-- One positive multiplier clears all centred rational residue values in a
finite family of dilations. -/
theorem finite_family_common_denominator
    (D : Finset ℕ) (f : ℕ → ℕ → ℚ) (m : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ d ∈ D, ∀ r < m, ∃ z : ℤ,
      (M : ℝ) * ((f d r : ℝ) - (f d 0 : ℝ)) = (z : ℝ) := by
  classical
  induction D using Finset.induction_on with
  | empty =>
      refine ⟨1, one_pos, ?_⟩
      intro d hd
      simp at hd
  | @insert d D hnot ih =>
      obtain ⟨M, hM, hclear⟩ := ih
      obtain ⟨K, hK, hkclear⟩ :=
        finite_common_denominator (fun r => f d r - f d 0) m
      refine ⟨M * K, Nat.mul_pos hM hK, ?_⟩
      intro e he r hr
      rcases Finset.mem_insert.mp he with heq | heD
      · subst e
        obtain ⟨z, hz⟩ := hkclear r hr
        have hz' : (K : ℝ) * ((f d r : ℝ) - (f d 0 : ℝ)) = (z : ℝ) := by
          simpa only [Rat.cast_sub] using hz
        refine ⟨(M : ℤ) * z, ?_⟩
        calc
          ((M * K : ℕ) : ℝ) * ((f d r : ℝ) - (f d 0 : ℝ)) =
              (M : ℝ) * ((K : ℝ) * ((f d r : ℝ) - (f d 0 : ℝ))) := by
                push_cast; ring
          _ = (M : ℝ) * (z : ℝ) := by rw [hz']
          _ = (((M : ℤ) * z : ℤ) : ℝ) := by push_cast; ring
      · obtain ⟨z, hz⟩ := hclear e heD r hr
        refine ⟨(K : ℤ) * z, ?_⟩
        calc
          ((M * K : ℕ) : ℝ) * ((f e r : ℝ) - (f e 0 : ℝ)) =
              (K : ℝ) * ((M : ℝ) * ((f e r : ℝ) - (f e 0 : ℝ))) := by
                push_cast; ring
          _ = (K : ℝ) * (z : ℝ) := by rw [hz]
          _ = (((K : ℤ) * z : ℤ) : ℝ) := by push_cast; ring

/-- A single centred integer family with the same multiplier at every active
dilation.  This is the data format consumed by the finite mixed-word proof. -/
theorem exists_centred_integer_family
    (D : Finset ℕ) (f : ℕ → ℕ → ℚ) (m : ℕ) (hm : 0 < m) :
    ∃ M : ℕ, 0 < M ∧ ∃ g : ℕ → ℕ → ℤ,
      (∀ d ∈ D, ∀ r < m,
        (g d r : ℝ) = (M : ℝ) * ((f d r : ℝ) - (f d 0 : ℝ))) ∧
      (∀ d ∈ D, g d 0 = 0) := by
  classical
  obtain ⟨M, hM, hclear⟩ := finite_family_common_denominator D f m
  let g : ℕ → ℕ → ℤ := fun d r =>
    if hd : d ∈ D then
      if hr : r < m then Classical.choose (hclear d hd r hr) else 0
    else 0
  have hg : ∀ d ∈ D, ∀ r < m,
      (g d r : ℝ) = (M : ℝ) * ((f d r : ℝ) - (f d 0 : ℝ)) := by
    intro d hd r hr
    dsimp [g]
    rw [dif_pos hd, dif_pos hr]
    exact (Classical.choose_spec (hclear d hd r hr)).symm
  refine ⟨M, hM, g, hg, ?_⟩
  intro d hd
  apply Int.cast_injective (α := ℝ)
  simpa only [sub_self, mul_zero, Int.cast_zero] using hg d hd 0 hm

/-- Clearing a positive common denominator preserves a difference from the
centering value. -/
theorem centred_integer_nonzero_of_rational_difference
    (M : ℕ) (hM : 0 < M) (f : ℕ → ℚ) (g : ℕ → ℤ)
    (r : ℕ)
    (hg : (g r : ℝ) = (M : ℝ) * ((f r : ℝ) - (f 0 : ℝ)))
    (hfr : f r ≠ f 0) : g r ≠ 0 := by
  intro hz
  rw [hz, Int.cast_zero] at hg
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hdiff : (f r : ℝ) - (f 0 : ℝ) = 0 :=
    (mul_eq_zero.mp hg.symm).resolve_left hMR
  exact hfr (Rat.cast_injective (sub_eq_zero.mp hdiff))

/-- Every finite family of finite residue words has a common real bound. -/
theorem exists_finite_family_bound
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d ∈ D, ∀ s < m, |(g d s : ℝ)| ≤ C := by
  let C : ℝ := ∑ d ∈ D, ∑ s ∈ Finset.range m, |(g d s : ℝ)|
  have hnonneg (d : ℕ) : 0 ≤ ∑ s ∈ Finset.range m, |(g d s : ℝ)| :=
    Finset.sum_nonneg (by intro s hs; exact abs_nonneg _)
  refine ⟨C, Finset.sum_nonneg (by intro d hd; exact hnonneg d), ?_⟩
  intro d hd s hs
  have hsingle : |(g d s : ℝ)| ≤ ∑ t ∈ Finset.range m, |(g d t : ℝ)| :=
    Finset.single_le_sum (s := Finset.range m) (a := s)
      (f := fun t : ℕ => |(g d t : ℝ)|)
      (by intro t ht; exact abs_nonneg _)
      (Finset.mem_range.mpr hs)
  exact hsingle.trans (Finset.single_le_sum
    (by intro e he; exact hnonneg e) hd)

/-- Centering and clearing denominators commutes with the positive-index
series at each dilation. -/
theorem centred_positiveRadixValue_eq
    (B d m M : ℕ) (hB : 2 ≤ B) (hd : 0 < d) (hm : 0 < m)
    (f : ℕ → ℚ) (g : ℕ → ℤ)
    (hg : ∀ r < m,
      (g r : ℝ) = (M : ℝ) * ((f r : ℝ) - (f 0 : ℝ))) :
    (∑' n : ℕ, (g (Nat.totient (n + 1) % m) : ℝ) /
      ((B : ℝ) ^ d) ^ (n + 1)) =
      (M : ℝ) * (positiveRadixValue (B ^ d) f m -
        (f 0 : ℝ) / ((B : ℝ) ^ d - 1)) := by
  have hBd : 2 ≤ B ^ d := by
    calc
      2 ≤ B := hB
      _ = B ^ 1 := by simp
      _ ≤ B ^ d := pow_le_pow_right₀ (by omega : 1 ≤ B) hd
  have hsf := summable_positive_terms (B ^ d) hBd m hm f
  have hsc := summable_const_div_radix_pow_succ (B ^ d) hBd (f 0 : ℝ)
  calc
    (∑' n : ℕ, (g (Nat.totient (n + 1) % m) : ℝ) /
      ((B : ℝ) ^ d) ^ (n + 1)) =
        ∑' n : ℕ, (M : ℝ) *
          ((f (Nat.totient (n + 1) % m) : ℝ) /
            ((B : ℝ) ^ d) ^ (n + 1) -
            (f 0 : ℝ) / ((B : ℝ) ^ d) ^ (n + 1)) := by
          apply tsum_congr
          intro n
          rw [hg _ (Nat.mod_lt _ hm)]
          ring
    _ = (M : ℝ) * (∑' n : ℕ,
          ((f (Nat.totient (n + 1) % m) : ℝ) /
            ((B : ℝ) ^ d) ^ (n + 1) -
            (f 0 : ℝ) / ((B : ℝ) ^ d) ^ (n + 1))) := tsum_mul_left
    _ = (M : ℝ) * (positiveRadixValue (B ^ d) f m -
          (f 0 : ℝ) / ((B : ℝ) ^ d - 1)) := by
          rw [← Nat.cast_pow, hsf.tsum_sub hsc,
            tsum_const_div_radix_pow_succ (B ^ d) hBd]
          rfl

#print axioms finite_family_common_denominator
#print axioms exists_centred_integer_family
#print axioms centred_integer_nonzero_of_rational_difference
#print axioms exists_finite_family_bound
#print axioms centred_positiveRadixValue_eq

end ErdosProblems.Erdos249.FiniteDilationRationalObservables
