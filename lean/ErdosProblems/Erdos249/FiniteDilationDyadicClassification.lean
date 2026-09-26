import ErdosProblems.Erdos249.FiniteDilationJointValue
import ErdosProblems.Erdos249.FiniteDilationRationalObservables

/-!
# Finite dyadic observables across commensurate integer bases

The first theorem applies the joint integer pulse result after simultaneous
rational centering.  Its first-active-dilation hypothesis is later discharged
by separating the finitely many even-constant observables.
-/

namespace ErdosProblems.Erdos249.FiniteDilationDyadicClassification

open scoped BigOperators
open ErdosProblems.Erdos249.FiniteDilationJointValue
open ErdosProblems.Erdos249.FiniteDilationRationalObservables
open ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables
open ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables

/-- If the first dilation in a finite family has a nonconstant even residue,
then no choices at higher dilations can cancel its irrational contribution. -/
theorem irrational_finite_family_of_first_variation
    (D : Finset ℕ) (f : ℕ → ℕ → ℚ) (k B δ r H : ℕ)
    (hk : 0 < k) (hB : 2 ≤ B)
    (hδD : δ ∈ D) (hδ : 0 < δ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hmin : ∀ d ∈ D, δ ≤ d)
    (hH : ∀ d ∈ D, d ≤ H)
    (hrlt : r < 2 ^ k) (hre : Even r)
    (hfr : f δ r ≠ f δ 0) :
    Irrational (∑ d ∈ D, positiveRadixValue (B ^ d) (f d) (2 ^ k)) := by
  classical
  have hm : 0 < 2 ^ k := pow_pos (by decide) _
  obtain ⟨M, hM, g, hg, hg0⟩ :=
    exists_centred_integer_family D f (2 ^ k) hm
  have hgr : g δ r ≠ 0 :=
    centred_integer_nonzero_of_rational_difference M hM (f δ)
      (g δ) r (hg δ hδD r hrlt) hfr
  obtain ⟨C, hC, hbound⟩ := exists_finite_family_bound D g (2 ^ k)
  have hI := irrational_finset_dyadic_positive_values
    D g k B δ r H hk hB hδD hδ hpos hmin hH hrlt hre
      hg0 hgr C hC hbound
  let q0 : ℚ := ∑ d ∈ D, f d 0 / ((B : ℚ) ^ d - 1)
  have hq0 : (q0 : ℝ) =
      ∑ d ∈ D, (f d 0 : ℝ) / ((B : ℝ) ^ d - 1) := by
    simp only [q0, Rat.cast_sum, Rat.cast_div, Rat.cast_sub,
      Rat.cast_pow, Rat.cast_natCast, Rat.cast_one]
  have hEq :
      (∑ d ∈ D, ∑' n : ℕ,
        (g d (Nat.totient (n + 1) % (2 ^ k)) : ℝ) /
          ((B : ℝ) ^ d) ^ (n + 1)) =
      (M : ℝ) * ((∑ d ∈ D, positiveRadixValue (B ^ d) (f d) (2 ^ k)) -
        (q0 : ℝ)) := by
    rw [hq0, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact centred_positiveRadixValue_eq B d (2 ^ k) M hB
      (hpos d hd) hm (f d) (g d) (hg d hd)
  intro hrat
  obtain ⟨q, hq⟩ := hrat
  apply hI
  refine ⟨(M : ℚ) * (q - q0), ?_⟩
  rw [hEq, ← hq]
  push_cast
  rfl

/-- The public exact value formula gives a rational value at each dilation
whose observable is constant on the even residue classes. -/
theorem rational_positiveRadixValue_of_even_constant
    (B d k : ℕ) (hB : 2 ≤ B) (hd : 0 < d) (hk : 0 < k)
    (f : ℕ → ℚ)
    (hc : ∀ r < 2 ^ k, Even r → f r = f 0) :
    ∃ q : ℚ, positiveRadixValue (B ^ d) f (2 ^ k) = (q : ℝ) := by
  have hBd : 2 ≤ B ^ d := by
    calc
      2 ≤ B := hB
      _ = B ^ 1 := by simp
      _ ≤ B ^ d := pow_le_pow_right₀ (by omega : 1 ≤ B) hd
  refine ⟨(((B : ℚ) ^ d + 1) / ((B : ℚ) ^ d) ^ 2) * f 1 +
      f 0 / (((B : ℚ) ^ d) ^ 2 * ((B : ℚ) ^ d - 1)), ?_⟩
  have hformula := positiveRadixValue_eq_of_even_constant
    (B ^ d) hBd hk (f := f) (c := f 0) (by
      intro r hr hre
      exact hc r hr (Nat.even_iff.mpr hre))
  simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_one, Rat.cast_sub, Nat.cast_pow] using hformula

/-- Exact rationality classification for a finite family of dyadic residue
observables at distinct positive powers of a common integer base. -/
theorem rational_finite_family_iff_even_constant
    (D : Finset ℕ) (f : ℕ → ℕ → ℚ) (k B : ℕ)
    (hk : 0 < k) (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d) :
    (∃ q : ℚ, (∑ d ∈ D,
      positiveRadixValue (B ^ d) (f d) (2 ^ k)) = (q : ℝ)) ↔
      ∀ d ∈ D, ∀ r < 2 ^ k, Even r → f d r = f d 0 := by
  classical
  let P : ℕ → Prop := fun d =>
    ∃ r, r < 2 ^ k ∧ Even r ∧ f d r ≠ f d 0
  let E := D.filter P
  let F := D.filter (fun d => ¬P d)
  let v : ℕ → ℝ := fun d => positiveRadixValue (B ^ d) (f d) (2 ^ k)
  have hsplit : (∑ d ∈ E, v d) + (∑ d ∈ F, v d) = ∑ d ∈ D, v d := by
    simpa only [E, F] using Finset.sum_filter_add_sum_filter_not D P v
  have hratF : ∃ q : ℚ, (∑ d ∈ F, v d) = (q : ℝ) := by
    have hterm : ∀ d ∈ F, ∃ q : ℚ, v d = (q : ℝ) := by
      intro d hd
      obtain ⟨hdD, hdP⟩ := Finset.mem_filter.mp hd
      exact rational_positiveRadixValue_of_even_constant B d k hB
        (hpos d hdD) hk (f d) (by
          intro r hr hre
          by_contra hne
          exact hdP ⟨r, hr, hre, hne⟩)
    let q : ℕ → ℚ := fun d =>
      if hd : d ∈ F then Classical.choose (hterm d hd) else 0
    refine ⟨∑ d ∈ F, q d, ?_⟩
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro d hd
    simpa only [q, dif_pos hd] using Classical.choose_spec (hterm d hd)
  constructor
  · rintro ⟨q, hq⟩ d hd r hr hre
    by_contra hne
    have hE : E.Nonempty := ⟨d, Finset.mem_filter.mpr ⟨hd, ⟨r, hr, hre, hne⟩⟩⟩
    let δ := E.min' hE
    have hδE : δ ∈ E := Finset.min'_mem E hE
    obtain ⟨hδD, rδ, hrδ, hreδ, hfrδ⟩ :=
      (Finset.mem_filter.mp hδE)
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
      irrational_finite_family_of_first_variation E f k B δ rδ H
        hk hB hδE (hpos δ hδD) hposE hmin hH hrδ hreδ hfrδ
    obtain ⟨qF, hqF⟩ := hratF
    apply hI.ne_rat (q - qF)
    have hsplit' : (∑ e ∈ E, v e) + (qF : ℝ) = (q : ℝ) := by
      simpa only [hqF, hq, v] using hsplit
    push_cast
    linarith
  · intro hc
    have hE : E = ∅ := by
      ext d
      constructor
      · intro hd
        obtain ⟨hdD, r, hr, hre, hne⟩ := Finset.mem_filter.mp hd
        exact False.elim (hne (hc d hdD r hr hre))
      · intro hd
        simp at hd
    obtain ⟨q, hq⟩ := hratF
    refine ⟨q, ?_⟩
    have hsplit' := hsplit
    rw [hE, Finset.sum_empty, zero_add, hq] at hsplit'
    simpa only [v] using hsplit'.symm

/-- Exact rational value in the constant-even branch, retaining the two
exceptional totient-one terms at n=1 and n=2. -/
theorem finite_family_value_eq_of_even_constant
    (D : Finset ℕ) (f : ℕ → ℕ → ℚ) (k B : ℕ)
    (hk : 0 < k) (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (hc : ∀ d ∈ D, ∀ r < 2 ^ k, Even r → f d r = f d 0) :
    (∑ d ∈ D, positiveRadixValue (B ^ d) (f d) (2 ^ k)) =
      ∑ d ∈ D, ((((B : ℝ) ^ d + 1) / ((B : ℝ) ^ d) ^ 2) *
        (f d 1 : ℝ) + (f d 0 : ℝ) /
          (((B : ℝ) ^ d) ^ 2 * ((B : ℝ) ^ d - 1))) := by
  apply Finset.sum_congr rfl
  intro d hd
  have hBd : 2 ≤ B ^ d := by
    calc
      2 ≤ B := hB
      _ = B ^ 1 := by simp
      _ ≤ B ^ d := pow_le_pow_right₀ (by omega : 1 ≤ B) (hpos d hd)
  simpa only [Nat.cast_pow] using
    (positiveRadixValue_eq_of_even_constant (B ^ d) hBd hk
      (f d) (f d 0) (by
        intro r hr hre
        exact hc d hd r hr (Nat.even_iff.mpr hre)))

/-- Finite-family classification in the residue domain of the ordinary
statement, where each observable is a function on ZMod (2^k). -/
theorem rational_zmod_finite_family_iff_even_constant
    (D : Finset ℕ) (k B : ℕ) (f : ℕ → ZMod (2 ^ k) → ℚ)
    (hk : 0 < k) (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d) :
    (∃ q : ℚ, (∑ d ∈ D, ∑' n : ℕ,
      (f d (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        ((B : ℝ) ^ d) ^ (n + 1)) = (q : ℝ)) ↔
      ∀ d ∈ D, ∀ r : ℕ, r < 2 ^ k → Even r →
        f d (r : ZMod (2 ^ k)) = f d 0 := by
  have h := rational_finite_family_iff_even_constant D
    (fun d r => f d (r : ZMod (2 ^ k))) k B hk hB hpos
  simpa only [positiveRadixValue, ZMod.natCast_mod, Nat.cast_zero,
    Nat.cast_pow] using h

/-- No nonzero finite rational combination of dyadic least-residue series at
distinct powers of one base can have a rational value. -/
theorem rational_finset_dyadic_least_residue_iff_zero
    (D : Finset ℕ) (c : ℕ → ℚ) (k B : ℕ)
    (hk : 2 ≤ k) (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d) :
    (∃ q : ℚ, (∑ d ∈ D, positiveRadixValue (B ^ d)
      (fun r : ℕ => c d * (r : ℚ)) (2 ^ k)) = (q : ℝ)) ↔
      ∀ d ∈ D, c d = 0 := by
  have hclass := rational_finite_family_iff_even_constant D
    (fun d r => c d * (r : ℚ)) k B (by omega) hB hpos
  constructor
  · intro hrat d hd
    have hc := hclass.mp hrat
    have hpow : (2 : ℕ) ^ 2 ≤ 2 ^ k :=
      pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ)) hk
    have h2k : 2 < 2 ^ k := by omega
    have hval := hc d hd 2 h2k (by decide : Even (2 : ℕ))
    have htwo : c d * (2 : ℚ) = 0 := by simpa using hval
    exact (mul_eq_zero.mp htwo).resolve_right (by norm_num)
  · intro hzero
    apply hclass.mpr
    intro d hd r hr hre
    simp [hzero d hd]

#print axioms irrational_finite_family_of_first_variation
#print axioms rational_finite_family_iff_even_constant
#print axioms finite_family_value_eq_of_even_constant
#print axioms rational_zmod_finite_family_iff_even_constant
#print axioms rational_finset_dyadic_least_residue_iff_zero

end ErdosProblems.Erdos249.FiniteDilationDyadicClassification
