import ErdosProblems.Erdos249.FiniteDilationJointValue

/-!
# Rational coefficients in finite least-residue relations

The joint integer-coefficient theorem already isolates a nonzero least
dilation.  One common denominator converts a finite rational relation to that
integer theorem while preserving the actual positive-index series value.
-/

namespace ErdosProblems.Erdos249.FiniteDilationLeastResidueRational

open scoped BigOperators
open ErdosProblems.Erdos249.FiniteDilationJointValue
open ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables
open ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables

/-- A finite rational combination of least-residue values is irrational when
its least represented dilation has a nonzero coefficient. -/
theorem irrational_finset_rational_least_residue_values
    (D : Finset ℕ) (c : ℕ → ℚ) (m B δ H : ℕ)
    (hm : 3 ≤ m) (hB : 2 ≤ B)
    (hδD : δ ∈ D) (hδ : 0 < δ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hmin : ∀ d ∈ D, δ ≤ d)
    (hH : ∀ d ∈ D, d ≤ H)
    (hcδ : c δ ≠ 0) :
    Irrational (∑ d ∈ D,
      positiveRadixValue (B ^ d) (fun r : ℕ => c d * (r : ℚ)) m) := by
  classical
  obtain ⟨M, hM, hclear⟩ := finite_common_denominator c (H + 1)
  let g : ℕ → ℤ := fun d =>
    if hd : d < H + 1 then Classical.choose (hclear d hd) else 0
  have hg (d : ℕ) (hd : d ∈ D) :
      (g d : ℝ) = (M : ℝ) * (c d : ℝ) := by
    have hdlt : d < H + 1 := by have := hH d hd; omega
    dsimp [g]
    rw [dif_pos hdlt]
    exact (Classical.choose_spec (hclear d hdlt)).symm
  have hgδ : g δ ≠ 0 := by
    intro hz
    have hδeq := hg δ hδD
    rw [hz, Int.cast_zero] at hδeq
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have hcδR : (c δ : ℝ) = 0 :=
      (mul_eq_zero.mp hδeq.symm).resolve_left hMR
    exact hcδ (Rat.cast_injective (by simpa using hcδR))
  have hI := irrational_finset_least_residue_positive_values
    D g m B δ H hm hB hδD hδ hpos hmin hH hgδ
  have hres (n : ℕ) :
      (((Nat.totient (n + 1) % m : ℤ) : ℝ)) =
        ((Nat.totient (n + 1) % m : ℕ) : ℝ) := by
    norm_cast
  have hseries (d : ℕ) (hd : d ∈ D) :
      (∑' n : ℕ,
        ((g d * (Nat.totient (n + 1) % m : ℤ) : ℤ) : ℝ) /
          ((B : ℝ) ^ d) ^ (n + 1)) =
      (M : ℝ) * positiveRadixValue (B ^ d)
        (fun r : ℕ => c d * (r : ℚ)) m := by
    calc
      (∑' n : ℕ,
        ((g d * (Nat.totient (n + 1) % m : ℤ) : ℤ) : ℝ) /
          ((B : ℝ) ^ d) ^ (n + 1)) =
        ∑' n : ℕ, (M : ℝ) *
          ((c d : ℝ) * ((Nat.totient (n + 1) % m : ℕ) : ℝ) /
            ((B : ℝ) ^ d) ^ (n + 1)) := by
          apply tsum_congr
          intro n
          rw [Int.cast_mul, hg d hd, hres n]
          ring
      _ = (M : ℝ) * (∑' n : ℕ,
          (c d : ℝ) * ((Nat.totient (n + 1) % m : ℕ) : ℝ) /
            ((B : ℝ) ^ d) ^ (n + 1)) := tsum_mul_left
      _ = (M : ℝ) * positiveRadixValue (B ^ d)
          (fun r : ℕ => c d * (r : ℚ)) m := by
          simp only [positiveRadixValue, Rat.cast_mul, Rat.cast_natCast,
            Nat.cast_pow]
  have hEq :
      (∑ d ∈ D, ∑' n : ℕ,
        ((g d * (Nat.totient (n + 1) % m : ℤ) : ℤ) : ℝ) /
          ((B : ℝ) ^ d) ^ (n + 1)) =
      (M : ℝ) * (∑ d ∈ D,
        positiveRadixValue (B ^ d) (fun r : ℕ => c d * (r : ℚ)) m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact hseries d hd
  intro hrat
  obtain ⟨q, hq⟩ := hrat
  apply hI
  refine ⟨(M : ℚ) * q, ?_⟩
  rw [hEq, ← hq]
  push_cast
  rfl

/-- Any nonzero finite rational coefficient family, with zero coefficients
allowed at smaller dilations, has an irrational least-residue value. -/
theorem irrational_finset_rational_least_residue_of_nonzero
    (D : Finset ℕ) (c : ℕ → ℚ) (m B : ℕ)
    (hm : 3 ≤ m) (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (hnonzero : ∃ d ∈ D, c d ≠ 0) :
    Irrational (∑ d ∈ D,
      positiveRadixValue (B ^ d) (fun r : ℕ => c d * (r : ℚ)) m) := by
  classical
  let P : ℕ → Prop := fun d => c d ≠ 0
  let E := D.filter P
  let F := D.filter (fun d => ¬P d)
  let v : ℕ → ℝ := fun d =>
    positiveRadixValue (B ^ d) (fun r : ℕ => c d * (r : ℚ)) m
  obtain ⟨d, hd, hcd⟩ := hnonzero
  have hE : E.Nonempty := ⟨d, Finset.mem_filter.mpr ⟨hd, hcd⟩⟩
  let δ := E.min' hE
  have hδE : δ ∈ E := Finset.min'_mem E hE
  have hδD : δ ∈ D := (Finset.mem_filter.mp hδE).1
  have hcδ : c δ ≠ 0 := (Finset.mem_filter.mp hδE).2
  have hposE : ∀ e ∈ E, 0 < e := by
    intro e he
    exact hpos e (Finset.mem_filter.mp he).1
  have hmin : ∀ e ∈ E, δ ≤ e := by
    intro e he
    exact Finset.min'_le E e he
  let H : ℕ := ∑ e ∈ E, e
  have hH : ∀ e ∈ E, e ≤ H := by
    intro e he
    exact Finset.single_le_sum (s := E) (a := e) (f := fun a : ℕ => a)
      (by intro a ha; exact Nat.zero_le a) he
  have hI : Irrational (∑ e ∈ E, v e) :=
    irrational_finset_rational_least_residue_values E c m B δ H
      hm hB hδE (hpos δ hδD) hposE hmin hH hcδ
  have hzeroF : (∑ e ∈ F, v e) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hce : c e = 0 := by
      by_contra hne
      exact (Finset.mem_filter.mp he).2 hne
    simp [v, hce, positiveRadixValue]
  have hsplit : (∑ e ∈ E, v e) + (∑ e ∈ F, v e) =
      ∑ e ∈ D, v e := by
    simpa only [E, F] using Finset.sum_filter_add_sum_filter_not D P v
  rw [hzeroF, add_zero] at hsplit
  simpa only [← hsplit, v] using hI

/-- The finite nonzero relation cannot be cancelled by a rational constant. -/
theorem no_rational_affine_least_residue_relation
    (D : Finset ℕ) (c : ℕ → ℚ) (q : ℚ) (m B : ℕ)
    (hm : 3 ≤ m) (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (hnonzero : ∃ d ∈ D, c d ≠ 0) :
    (q : ℝ) + (∑ d ∈ D,
      positiveRadixValue (B ^ d) (fun r : ℕ => c d * (r : ℚ)) m) ≠ 0 := by
  intro hzero
  have hI := irrational_finset_rational_least_residue_of_nonzero
    D c m B hm hB hpos hnonzero
  apply hI.ne_rat (-q)
  have hval : (∑ d ∈ D,
      positiveRadixValue (B ^ d) (fun r : ℕ => c d * (r : ℚ)) m) =
      -(q : ℝ) := by linarith
  simpa using hval

#print axioms irrational_finset_rational_least_residue_values
#print axioms irrational_finset_rational_least_residue_of_nonzero
#print axioms no_rational_affine_least_residue_relation

end ErdosProblems.Erdos249.FiniteDilationLeastResidueRational
