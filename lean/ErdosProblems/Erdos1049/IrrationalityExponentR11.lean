import ErdosProblems.Erdos1049.QuadraticMeasureR10
import Mathlib

/-!
# The supremum definition of the irrationality exponent

Bounds the supremum exponent, real and extended, from quadratic linear forms.
Denominators are positive naturals and numerators are arbitrary integers.
Finiteness of the numerators at bounded denominators is proved, not assumed.
The extended-real definition also covers an unbounded exponent set.
-/
namespace ErdosProblems.Erdos1049.PaperR11
open Filter Set
open scoped BigOperators Topology
open PaperR9 PaperR10

/-- Reduced rational pairs satisfying the paper's strict inequality. -/
def reducedApproximationPairs (ξ ν : ℝ) : Set (ℤ × ℕ) :=
  {r | 0 < r.2 ∧ Nat.Coprime r.1.natAbs r.2 ∧
    |ξ - (r.1 : ℝ) / (r.2 : ℝ)| < (r.2 : ℝ) ^ (-ν)}

def approximationExponents (ξ : ℝ) : Set ℝ :=
  {ν | (reducedApproximationPairs ξ ν).Infinite}

/-- Used with a proved upper bound; the extended definition is used otherwise. -/
noncomputable def irrationalityExponent (ξ : ℝ) : ℝ :=
  sSup (approximationExponents ξ)

noncomputable def extendedIrrationalityExponent (ξ : ℝ) : EReal :=
  sSup ((fun ν : ℝ => (ν : EReal)) '' approximationExponents ξ)

lemma approximation_numerator_bound {ξ ν : ℝ} {p : ℤ} {q : ℕ}
    (hq : 0 < q)
    (h : |ξ - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν)) :
    |(p : ℝ)| < (q : ℝ) * (|ξ| + (q : ℝ) ^ (-ν)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hp : |(p : ℝ) / (q : ℝ)| < |ξ| + (q : ℝ) ^ (-ν) := by
    calc
      |(p : ℝ) / (q : ℝ)| = |ξ - (ξ - (p : ℝ) / (q : ℝ))| := by
        congr 1
        ring
      _ ≤ |ξ| + |ξ - (p : ℝ) / (q : ℝ)| := abs_sub _ _
      _ < |ξ| + (q : ℝ) ^ (-ν) := by linarith
  rw [abs_div, abs_of_pos hqR] at hp
  simpa [mul_comm] using (div_lt_iff₀ hqR).mp hp

/-- Every bounded-denominator part is finite, for every real ν and Q=0 too. -/
theorem finite_bounded_denominator_approximations (ξ ν : ℝ) (Q : ℕ) :
    {r : ℤ × ℕ | r ∈ reducedApproximationPairs ξ ν ∧ r.2 < Q}.Finite := by
  classical
  let B : ℝ := ∑ q ∈ Finset.range Q,
    (q : ℝ) * (|ξ| + (q : ℝ) ^ (-ν))
  obtain ⟨N, hN⟩ := exists_nat_gt B
  let box : Finset (ℤ × ℕ) :=
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).product (Finset.range Q)
  refine box.finite_toSet.subset ?_
  rintro ⟨p, q⟩ ⟨⟨hq, _, happ⟩, hqQ⟩
  have hs : (q : ℝ) * (|ξ| + (q : ℝ) ^ (-ν)) ≤ B := by
    apply Finset.single_le_sum (f := fun j : ℕ => (j : ℝ) * (|ξ| + (j : ℝ) ^ (-ν)))
    · intro j hj
      exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    · exact Finset.mem_range.mpr hqQ
  have hpN : |(p : ℝ)| < (N : ℝ) :=
    ((approximation_numerator_bound hq happ).trans_le hs).trans hN
  have hpLo : -(N : ℤ) ≤ p := by
    have h : -(N : ℝ) ≤ (p : ℝ) := (abs_lt.mp hpN).1.le
    exact_mod_cast h
  have hpHi : p ≤ (N : ℤ) := by
    have h : (p : ℝ) ≤ (N : ℝ) := (abs_lt.mp hpN).2.le
    exact_mod_cast h
  change (p, q) ∈ box
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hpLo, hpHi⟩, Finset.mem_range.mpr hqQ⟩

/-- Denominator escape follows from infinitude; it is not in the definition. -/
theorem approximations_escape_denominators {ξ ν : ℝ}
    (h : (reducedApproximationPairs ξ ν).Infinite) (Q : ℕ) :
    ∃ r ∈ reducedApproximationPairs ξ ν, Q ≤ r.2 := by
  by_contra hn
  push_neg at hn
  have hs : reducedApproximationPairs ξ ν ⊆
      {r : ℤ × ℕ | r ∈ reducedApproximationPairs ξ ν ∧ r.2 < Q} := by
    intro r hr
    exact ⟨hr, hn r hr⟩
  exact h ((finite_bounded_denominator_approximations ξ ν Q).subset hs)

/-- Exponent -1 supplies infinitely many reduced pairs (1,q), even for rational ξ. -/
theorem neg_one_mem_approximationExponents (ξ : ℝ) :
    (-1 : ℝ) ∈ approximationExponents ξ := by
  classical
  change (reducedApproximationPairs ξ (-1)).Infinite
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (|ξ| + 1)
  let q : ℕ := max (B + 1) (N + 1)
  have hqB : B < q := (Nat.lt_succ_self B).trans_le (le_max_left _ _)
  have hqN : N < q := (Nat.lt_succ_self N).trans_le (le_max_right _ _)
  have hq : 0 < q := (Nat.zero_le B).trans_lt hqB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.succ_le_iff.mpr hq : 1 ≤ q)
  have hinv : |(1 : ℝ) / (q : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (q : ℝ))]
    exact (div_le_iff₀ hqR).mpr (by simpa using hq1)
  have happ : |ξ - (1 : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-(-1 : ℝ)) := by
    calc
      |ξ - (1 : ℝ) / (q : ℝ)| ≤ |ξ| + |(1 : ℝ) / (q : ℝ)| := abs_sub _ _
      _ ≤ |ξ| + 1 := by linarith
      _ < (N : ℝ) := hN
      _ < (q : ℝ) := by exact_mod_cast hqN
      _ = (q : ℝ) ^ (-(-1 : ℝ)) := by norm_num
  have hmem : ((1 : ℤ), q) ∈ reducedApproximationPairs ξ (-1) := by
    exact ⟨hq, by simp, by simpa using happ⟩
  have hqle : q ≤ B := hB ⟨((1 : ℤ), q), hmem, rfl⟩
  exact (not_lt_of_ge hqle) hqB

lemma approximationExponents_nonempty (ξ : ℝ) :
    (approximationExponents ξ).Nonempty :=
  ⟨-1, neg_one_mem_approximationExponents ξ⟩

/-- The R10 eventual bound rules out infinitely many reduced rational pairs. -/
theorem finite_approximations_of_exponentUpper {ξ μ ν : ℝ}
    (h : ApproximationExponentUpper ξ μ) (hν : μ < ν) :
    (reducedApproximationPairs ξ ν).Finite := by
  obtain ⟨Q, _, hQ⟩ := h ν hν
  refine (finite_bounded_denominator_approximations ξ ν Q).subset ?_
  intro r hr
  refine ⟨hr, ?_⟩
  by_contra hnot
  have hQr : Q ≤ r.2 := Nat.le_of_not_gt hnot
  exact (not_lt_of_ge (hQ r.2 hQr r.1)) hr.2.2

/-- Supremum bridge, including nonemptiness and finite-numerator arguments. -/
theorem irrationalityExponent_le_of_exponentUpper {ξ μ : ℝ}
    (h : ApproximationExponentUpper ξ μ) :
    irrationalityExponent ξ ≤ μ := by
  apply csSup_le (approximationExponents_nonempty ξ)
  intro ν hν
  apply le_of_not_gt
  intro hgt
  exact hν (finite_approximations_of_exponentUpper h hgt)

/-- The same upper bound in the complete extended-real lattice. -/
theorem extendedIrrationalityExponent_le_of_exponentUpper {ξ μ : ℝ}
    (h : ApproximationExponentUpper ξ μ) :
    extendedIrrationalityExponent ξ ≤ (μ : EReal) := by
  apply sSup_le
  rintro _ ⟨ν, hν, rfl⟩
  have hle : ν ≤ μ := by
    apply le_of_not_gt
    intro hgt
    exact hν (finite_approximations_of_exponentUpper h hgt)
  show (ν : EReal) ≤ (μ : EReal)
  exact_mod_cast hle

/-- Composition with the unchanged, checked quadratic-mesh theorem. -/
theorem irrationalityExponent_le_of_quadratic_forms
    (A B : ℕ → ℤ) (ξ α τ : ℝ) (hα : 0 ≤ α) (hτ : 0 < τ)
    (hne : ∀ᶠ n in atTop, (A n : ℝ) * ξ - B n ≠ 0)
    (hA : QuadExpUpper (fun n => (A n : ℝ)) α)
    (hL : QuadLogRate (fun n => (A n : ℝ) * ξ - B n) (-τ)) :
    irrationalityExponent ξ ≤ 1 + α / τ := by
  exact irrationalityExponent_le_of_exponentUpper
    (approximationExponentUpper_of_quadratic_forms A B ξ α τ hα hτ hne hA hL)

theorem irrational_and_supremum_bound_of_quadratic_forms
    (A B : ℕ → ℤ) (ξ α τ : ℝ) (hα : 0 ≤ α) (hτ : 0 < τ)
    (hne : ∀ᶠ n in atTop, (A n : ℝ) * ξ - B n ≠ 0)
    (hA : QuadExpUpper (fun n => (A n : ℝ)) α)
    (hL : QuadLogRate (fun n => (A n : ℝ) * ξ - B n) (-τ)) :
    Irrational ξ ∧ irrationalityExponent ξ ≤ 1 + α / τ := by
  obtain ⟨hirr, hu⟩ :=
    irrational_and_measure_of_quadratic_forms A B ξ α τ hα hτ hne hA hL
  exact ⟨hirr, irrationalityExponent_le_of_exponentUpper hu⟩

end ErdosProblems.Erdos1049.PaperR11
