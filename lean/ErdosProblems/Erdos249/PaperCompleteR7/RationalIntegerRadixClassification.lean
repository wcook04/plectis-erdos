import ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables

/-!
# Rational totient observables in an integer radix

The classification shares the existing prime-isolation source with the binary
theorem. The analytic pulse obstruction is the integer-radix companion.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix

open scoped BigOperators
open ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables
open ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables

/-- Clearing rational residue data commutes with the positive-index radix
value, including the constant tail's exact geometric correction. -/
theorem centred_integer_radix_value_eq
    (B : ℕ) (hB : 2 ≤ B) (f : ℕ → ℚ) {m D : ℕ} (hm : 0 < m)
    (g : ℕ → ℤ)
    (hg : ∀ r, r < m →
      (g r : ℝ) = (D : ℝ) * ((f r : ℝ) - (f 0 : ℝ))) :
    radixValue B (ErdosProblems.Erdos249.totientObservableCoeff g m) =
      (D : ℝ) * (positiveRadixValue B f m - (f 0 : ℝ) / ((B : ℝ) - 1)) := by
  let a := ErdosProblems.Erdos249.totientObservableCoeff g m
  let C : ℝ := ∑ i ∈ Finset.range m, |(g i : ℝ)|
  have hbound (n : ℕ) : |(a n : ℝ)| ≤ C :=
    Finset.single_le_sum (fun i _ => abs_nonneg (g i : ℝ))
      (Finset.mem_range.mpr (Nat.mod_lt _ hm))
  have hs := summable_radix_terms B hB a C hbound
  have hg0 : g 0 = 0 := by
    apply Int.cast_injective (α := ℝ)
    simpa only [sub_self, mul_zero, Int.cast_zero] using hg 0 hm
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => (a n : ℝ) / (B : ℝ) ^ n) 1 hs
  simp only [Finset.sum_range_one, Nat.totient_zero, Nat.zero_mod,
    pow_zero, div_one, a, ErdosProblems.Erdos249.totientObservableCoeff,
    hg0, Int.cast_zero, zero_add] at hsplit
  have hfull : radixValue B a =
      ∑' n : ℕ, (g (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1) := by
    simpa only [radixValue, a, ErdosProblems.Erdos249.totientObservableCoeff]
      using hsplit.symm
  have hsf := summable_positive_terms B hB m hm f
  have hsc := summable_const_div_radix_pow_succ B hB (f 0 : ℝ)
  calc
    radixValue B a =
        ∑' n : ℕ, (g (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1) := hfull
    _ = ∑' n : ℕ, (D : ℝ) *
          ((f (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1) -
            (f 0 : ℝ) / (B : ℝ) ^ (n + 1)) := by
          apply tsum_congr
          intro n
          rw [hg _ (Nat.mod_lt _ hm)]
          ring
    _ = (D : ℝ) * (∑' n : ℕ,
          ((f (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1) -
            (f 0 : ℝ) / (B : ℝ) ^ (n + 1))) := tsum_mul_left
    _ = (D : ℝ) * (positiveRadixValue B f m -
          (f 0 : ℝ) / ((B : ℝ) - 1)) := by
          rw [hsf.tsum_sub hsc, tsum_const_div_radix_pow_succ B hB]
          rfl

/-- A nonzero unit residue obstructs rationality in every integer radix. -/
theorem irrational_positiveRadixValue_of_unit
    (B : ℕ) (hB : 2 ≤ B) {m : ℕ} (hm : 2 ≤ m) (f : ℕ → ℚ)
    {r : ℕ} (hr : r < m) (hcop : Nat.Coprime (r + 1) m)
    (hfr : f r ≠ f 0) : Irrational (positiveRadixValue B f m) := by
  classical
  obtain ⟨D, hD, hclear⟩ := finite_common_denominator (fun i => f i - f 0) m
  let g : ℕ → ℤ := fun i =>
    if hi : i < m then Classical.choose (hclear i hi) else 0
  have hg (i : ℕ) (hi : i < m) :
      (g i : ℝ) = (D : ℝ) * ((f i : ℝ) - (f 0 : ℝ)) := by
    dsimp [g]
    rw [dif_pos hi]
    simpa only [Rat.cast_sub] using
      (Classical.choose_spec (hclear i hi)).symm
  have hg0 : g 0 = 0 := by
    apply Int.cast_injective (α := ℝ)
    simpa only [sub_self, mul_zero, Int.cast_zero] using hg 0 (by omega)
  have hgr : g r ≠ 0 := by
    intro hzero
    have hz := hg r hr
    rw [hzero, Int.cast_zero] at hz
    have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have heq : (f r : ℝ) = (f 0 : ℝ) := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz.symm).resolve_left hDR)
    exact hfr (Rat.cast_injective heq)
  have hirr := irrational_radix_totientObservable B hB hm g hg0 hr hcop hgr
  have hvalue := centred_integer_radix_value_eq B hB f (by omega : 0 < m) g hg
  intro hrational
  obtain ⟨q, hq⟩ := hrational
  apply hirr
  refine ⟨(D : ℚ) * (q - f 0 / ((B : ℚ) - 1)), ?_⟩
  rw [hvalue, ← hq]
  push_cast
  rfl

/-- At a dyadic resolution, every even residue satisfies the unit condition. -/
theorem irrational_positiveRadixValue_of_even
    (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : 1 ≤ k)
    (f : ℕ → ℚ) {r : ℕ} (hr : r < 2 ^ k) (heven : r % 2 = 0)
    (hfr : f r ≠ f 0) : Irrational (positiveRadixValue B f (2 ^ k)) := by
  have h2 : Nat.Coprime 2 (r + 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  exact irrational_positiveRadixValue_of_unit B hB (two_le_two_pow hk)
    f hr (Nat.Coprime.pow_right k h2.symm) hfr

/-- Exact all-integer-radix rationality classification for finite dyadic
totient-residue observables. -/
theorem rational_positiveRadixValue_iff_even_constant
    (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℚ) :
    (∃ q : ℚ, positiveRadixValue B f (2 ^ k) = (q : ℝ)) ↔
      ∀ r, r < 2 ^ k → r % 2 = 0 → f r = f 0 := by
  constructor
  · rintro ⟨q, hq⟩ r hr heven
    by_contra hne
    exact (irrational_positiveRadixValue_of_even B hB hk f hr heven hne).ne_rat q hq
  · intro hc
    refine ⟨((B : ℚ) + 1) / (B : ℚ) ^ 2 * f 1 +
      f 0 / ((B : ℚ) ^ 2 * ((B : ℚ) - 1)), ?_⟩
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_one, Rat.cast_sub] using
      positiveRadixValue_eq_of_even_constant B hB hk f (f 0) hc

/-- The least-residue totient series is irrational for every integer radix
at least two and every modulus at least three. -/
theorem radix_residue_series_irrational
    (B : ℕ) (hB : 2 ≤ B) {m : ℕ} (hm : 3 ≤ m) :
    Irrational (radixValue B (fun n => (Nat.totient n % m : ℤ))) := by
  have hcop : Nat.Coprime (m - 2 + 1) m := by
    have h : Nat.Coprime (m - 1) (m - 1 + 1) := by simp
    rw [show m - 1 + 1 = m from by omega] at h
    rw [show m - 2 + 1 = m - 1 from by omega]
    exact h
  have hirr := irrational_radix_totientObservable B hB (by omega : 2 ≤ m)
    (fun x => (x : ℤ)) (by simp) (by omega : m - 2 < m) hcop (by
      simp only [ne_eq, Int.natCast_eq_zero]
      omega)
  simpa only [radixValue, ErdosProblems.Erdos249.totientObservableCoeff]
    using hirr

/-- The same classification in the finite residue domain used by the public
binary theorem. -/
theorem rational_zmod_radix_observable_iff
    (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : 1 ≤ k)
    (f : ZMod (2 ^ k) → ℚ) :
    (∃ q : ℚ,
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        (B : ℝ) ^ (n + 1)) = (q : ℝ)) ↔
      ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0 := by
  have h := rational_positiveRadixValue_iff_even_constant B hB hk
    (fun r : ℕ => f (r : ZMod (2 ^ k)))
  simpa only [positiveRadixValue, ZMod.natCast_mod, Nat.cast_zero]
    using h

#print axioms irrational_positiveRadixValue_of_unit
#print axioms rational_positiveRadixValue_iff_even_constant
#print axioms radix_residue_series_irrational
#print axioms rational_zmod_radix_observable_iff

end ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix
