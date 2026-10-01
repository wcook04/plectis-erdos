import Mathlib

/-!
# Reindexing one dilated series

The arithmetic pulse proof uses coefficients indexed by `d * n`.  This file
isolates the infinite-sum change of variables needed before finite dilation
mixing can be identified with one integer-radix series.
-/

namespace ErdosProblems.Erdos249.FiniteDilationSeriesTransport

/-- Multiplication by a positive dilation is a bijection onto its multiples. -/
def multiplesEquiv (d : ℕ) (hd : 0 < d) : ℕ ≃ {N : ℕ // d ∣ N} where
  toFun n := ⟨d * n, dvd_mul_right d n⟩
  invFun N := N.val / d
  left_inv n := by
    exact Nat.mul_div_cancel_left n hd
  right_inv N := by
    apply Subtype.ext
    exact Nat.mul_div_cancel' N.property

/-- Reindexing an infinite sum along the multiples of one positive dilation.
The identity is unconditional because both `tsum`s use the same summation
convention; summability is proved separately for the value theorem. -/
theorem tsum_dilated (d : ℕ) (hd : 0 < d) (f : ℕ → ℝ) :
    (∑' N : ℕ, if d ∣ N then f (N / d) else 0) = ∑' n : ℕ, f n := by
  classical
  let e := multiplesEquiv d hd
  calc
    (∑' N : ℕ, if d ∣ N then f (N / d) else 0) =
        ∑' N : {N : ℕ // d ∣ N}, f (N.val / d) := by
          simpa only [Set.indicator, Set.mem_setOf_eq] using
            (tsum_subtype {N : ℕ | d ∣ N} (fun N => f (N / d))).symm
    _ = ∑' n : ℕ, f ((e n).val / d) := by
          exact (e.tsum_eq (fun N : {N : ℕ // d ∣ N} => f (N.val / d))).symm
    _ = ∑' n : ℕ, f n := by
          apply tsum_congr
          intro n
          simp [e, multiplesEquiv, hd]

/-- Exchange a finite family of summable dilated series with one coefficient
word.  Each padded series is required to be summable; the geometric bound for
totient observables supplies that premise in the value theorem. -/
theorem tsum_finset_dilated
    (D : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hsum : ∀ d ∈ D,
      Summable (fun N : ℕ => if d ∣ N then f d (N / d) else 0)) :
    (∑' N : ℕ, ∑ d ∈ D, if d ∣ N then f d (N / d) else 0) =
      ∑ d ∈ D, ∑' n : ℕ, f d n := by
  rw [Summable.tsum_finsetSum hsum]
  apply Finset.sum_congr rfl
  intro d hd
  exact tsum_dilated d (hpos d hd) (f d)

/-- The exact series identity behind joint values at commensurate bases.
`hsum` isolates the analytic convergence obligation from the reindexing. -/
theorem mixed_radix_series_eq_finset_values
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m B : ℕ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hsum : ∀ d ∈ D, Summable (fun N : ℕ =>
      if d ∣ N then
        (g d (Nat.totient (N / d) % m) : ℝ) / (B : ℝ) ^ N else 0)) :
    (∑' N : ℕ, ∑ d ∈ D,
      if d ∣ N then
        (g d (Nat.totient (N / d) % m) : ℝ) / (B : ℝ) ^ N else 0) =
      ∑ d ∈ D, ∑' n : ℕ,
        (g d (Nat.totient n % m) : ℝ) / ((B : ℝ) ^ d) ^ n := by
  classical
  let f : ℕ → ℕ → ℝ := fun d n =>
    (g d (Nat.totient n % m) : ℝ) / ((B : ℝ) ^ d) ^ n
  have hterm (d N : ℕ) :
      (if d ∣ N then f d (N / d) else 0) =
        (if d ∣ N then
          (g d (Nat.totient (N / d) % m) : ℝ) / (B : ℝ) ^ N else 0) := by
    by_cases hdN : d ∣ N
    · simp [f, hdN, ← pow_mul, Nat.mul_div_cancel' hdN]
    · simp [hdN]
  have hsumf : ∀ d ∈ D,
      Summable (fun N : ℕ => if d ∣ N then f d (N / d) else 0) := by
    intro d hd
    exact (hsum d hd).congr (fun N => (hterm d N).symm)
  calc
    (∑' N : ℕ, ∑ d ∈ D,
        if d ∣ N then
          (g d (Nat.totient (N / d) % m) : ℝ) / (B : ℝ) ^ N else 0) =
        (∑' N : ℕ, ∑ d ∈ D, if d ∣ N then f d (N / d) else 0) := by
          apply tsum_congr
          intro N
          apply Finset.sum_congr rfl
          intro d _
          exact (hterm d N).symm
    _ = ∑ d ∈ D, ∑' n : ℕ, f d n := tsum_finset_dilated D f hpos hsumf
    _ = ∑ d ∈ D, ∑' n : ℕ,
        (g d (Nat.totient n % m) : ℝ) / ((B : ℝ) ^ d) ^ n := rfl

private theorem summable_bounded_radix_terms
    (B : ℕ) (hB : 2 ≤ B) (a : ℕ → ℤ) (C : ℝ)
    (hC : ∀ n, |(a n : ℝ)| ≤ C) :
    Summable (fun n : ℕ => (a n : ℝ) / (B : ℝ) ^ n) := by
  have hBreal : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hgeom : Summable (fun n : ℕ => (1 / (B : ℝ)) ^ n) :=
    summable_geometric_of_lt_one (by positivity)
      (by rw [div_lt_one (by linarith : (0 : ℝ) < B)]; linarith)
  have hmajor : Summable (fun n : ℕ => C * (1 / (B : ℝ)) ^ n) :=
    hgeom.mul_left C
  apply Summable.of_norm_bounded (g := fun n : ℕ => C * (1 / (B : ℝ)) ^ n)
    hmajor
  intro n
  rw [Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (B : ℝ) ^ n)]
  rw [div_pow]
  simp only [one_pow, mul_one_div]
  exact div_le_div_of_nonneg_right (hC n) (by positivity)

/-- A centred totient observable vanishes at index zero, so the natural-number
series is exactly the positive-index series used in the mathematical statement. -/
theorem tsum_totient_observable_eq_positive
    (g : ℕ → ℤ) (m B : ℕ) (hm : 0 < m) (hB : 2 ≤ B)
    (hg0 : g 0 = 0) (C : ℝ)
    (hg : ∀ s < m, |(g s : ℝ)| ≤ C) :
    (∑' n : ℕ, (g (Nat.totient n % m) : ℝ) / (B : ℝ) ^ n) =
      ∑' n : ℕ, (g (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1) := by
  have hs : Summable (fun n : ℕ =>
      (g (Nat.totient n % m) : ℝ) / (B : ℝ) ^ n) :=
    summable_bounded_radix_terms B hB
      (fun n => g (Nat.totient n % m)) C
      (fun n => hg _ (Nat.mod_lt _ hm))
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => (g (Nat.totient n % m) : ℝ) / (B : ℝ) ^ n) 1 hs
  simpa only [Finset.sum_range_one, Nat.totient_zero, Nat.zero_mod,
    hg0, Int.cast_zero, pow_zero, div_one, zero_add] using hsplit.symm

/-- Finite dilation transport with all convergence hypotheses discharged by
one uniform bound on the residue observables. -/
theorem mixed_radix_series_eq_finset_values_of_bounded
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m B : ℕ)
    (hm : 0 < m) (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ d ∈ D, ∀ r < m, |(g d r : ℝ)| ≤ C) :
    (∑' N : ℕ, ∑ d ∈ D,
      if d ∣ N then
        (g d (Nat.totient (N / d) % m) : ℝ) / (B : ℝ) ^ N else 0) =
      ∑ d ∈ D, ∑' n : ℕ,
        (g d (Nat.totient n % m) : ℝ) / ((B : ℝ) ^ d) ^ n := by
  apply mixed_radix_series_eq_finset_values D g m B hpos
  intro d hd
  let a : ℕ → ℤ := fun N =>
    if d ∣ N then g d (Nat.totient (N / d) % m) else 0
  have ha (N : ℕ) : |(a N : ℝ)| ≤ C := by
    by_cases hdN : d ∣ N
    · simpa [a, hdN] using hg d hd _ (Nat.mod_lt _ hm)
    · simpa [a, hdN] using hC
  have hs := summable_bounded_radix_terms B hB a C ha
  refine hs.congr ?_
  intro N
  by_cases hdN : d ∣ N
  · simp [a, hdN]
  · simp [a, hdN]

/-- The finite integer coefficient sum has exactly the value of the original
finite family of base-power series.  This is the expression obtained by
unfolding `mixedCoefficient` in the arithmetic module. -/
theorem integer_mixed_radixValue_eq_finset_values
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m B : ℕ)
    (hm : 0 < m) (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ d ∈ D, ∀ r < m, |(g d r : ℝ)| ≤ C) :
    (∑' N : ℕ,
      ((∑ d ∈ D,
        if d ∣ N then g d (Nat.totient (N / d) % m) else 0 : ℤ) : ℝ) /
        (B : ℝ) ^ N) =
      ∑ d ∈ D, ∑' n : ℕ,
        (g d (Nat.totient n % m) : ℝ) / ((B : ℝ) ^ d) ^ n := by
  calc
    (∑' N : ℕ,
        ((∑ d ∈ D,
          if d ∣ N then g d (Nat.totient (N / d) % m) else 0 : ℤ) : ℝ) /
          (B : ℝ) ^ N) =
        (∑' N : ℕ, ∑ d ∈ D,
          if d ∣ N then
            (g d (Nat.totient (N / d) % m) : ℝ) / (B : ℝ) ^ N else 0) := by
          apply tsum_congr
          intro N
          push_cast
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro d _
          by_cases hdN : d ∣ N <;> simp [hdN]
    _ = ∑ d ∈ D, ∑' n : ℕ,
        (g d (Nat.totient n % m) : ℝ) / ((B : ℝ) ^ d) ^ n :=
      mixed_radix_series_eq_finset_values_of_bounded D g m B hm hB hpos C hC hg

#print axioms tsum_dilated
#print axioms tsum_finset_dilated
#print axioms mixed_radix_series_eq_finset_values
#print axioms mixed_radix_series_eq_finset_values_of_bounded
#print axioms tsum_totient_observable_eq_positive
#print axioms integer_mixed_radixValue_eq_finset_values

end ErdosProblems.Erdos249.FiniteDilationSeriesTransport
