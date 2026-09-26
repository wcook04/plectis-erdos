import ErdosProblems.Erdos249.FiniteDilationDyadicClassification

/-!
# Joint rationality with a different dyadic modulus at each dilation

The common-modulus theorem is applied after lifting each finite residue table
to one dyadic level. The positive-index series is retained throughout.
-/

namespace ErdosProblems.Erdos249.FiniteDilationMixedModuli

open scoped BigOperators
open ErdosProblems.Erdos249.FiniteDilationDyadicClassification
open ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables
open ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables

private theorem natCast_mod_two_pow_of_le (a k K : ℕ) (h : k ≤ K) :
    ((a % 2 ^ K : ℕ) : ZMod (2 ^ k)) = (a : ZMod (2 ^ k)) := by
  have hdvd : 2 ^ k ∣ 2 ^ K := pow_dvd_pow 2 h
  apply ZMod.val_injective
  simpa only [ZMod.val_natCast] using (Nat.mod_mod_of_dvd a hdvd)

private theorem even_mod_two_pow (r k : ℕ) (hk : 0 < k) (hr : Even r) :
    Even (r % 2 ^ k) := by
  have hdvd : 2 ∣ 2 ^ k := by
    simpa using (pow_dvd_pow 2 (by omega : 1 ≤ k) : 2 ^ 1 ∣ 2 ^ k)
  apply (even_iff_two_dvd).mpr
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.mod_mod_of_dvd _ hdvd]
  exact Nat.mod_eq_zero_of_dvd ((even_iff_two_dvd).mp hr)

/-- For a finite family of positive dilations, the rationality criterion is
unchanged when every dilation has its own dyadic resolution. -/
theorem rational_mixed_moduli_iff_even_constant
    (D : Finset ℕ) (k : ℕ → ℕ)
    (f : (d : ℕ) → ZMod (2 ^ (k d)) → ℚ) (B : ℕ)
    (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (hk : ∀ d ∈ D, 0 < k d) :
    (∃ q : ℚ, (∑ d ∈ D, ∑' n : ℕ,
      (f d (Nat.totient (n + 1) : ZMod (2 ^ (k d))) : ℝ) /
        ((B : ℝ) ^ d) ^ (n + 1)) = (q : ℝ)) ↔
      ∀ d ∈ D, ∀ r : ℕ, r < 2 ^ (k d) → Even r →
        f d (r : ZMod (2 ^ (k d))) = f d 0 := by
  classical
  let K : ℕ := 1 + ∑ d ∈ D, k d
  have hK : 0 < K := by simp [K]
  have hle : ∀ d ∈ D, k d ≤ K := by
    intro d hd
    have hsum : k d ≤ ∑ e ∈ D, k e :=
      Finset.single_le_sum (s := D) (a := d) (f := k)
        (by intro e he; exact Nat.zero_le _) hd
    omega
  let F : ℕ → ℕ → ℚ := fun d r => f d (r : ZMod (2 ^ (k d)))
  have hterm (d : ℕ) (hd : d ∈ D) :
      positiveRadixValue (B ^ d) (F d) (2 ^ K) =
        ∑' n : ℕ,
          (f d (Nat.totient (n + 1) : ZMod (2 ^ (k d))) : ℝ) /
            ((B : ℝ) ^ d) ^ (n + 1) := by
    unfold positiveRadixValue
    apply tsum_congr
    intro n
    have hcast := natCast_mod_two_pow_of_le (Nat.totient (n + 1))
      (k d) K (hle d hd)
    simpa only [F, Nat.cast_pow] using congrArg
      (fun z : ZMod (2 ^ (k d)) =>
        (f d z : ℝ) / ((B : ℝ) ^ d) ^ (n + 1)) hcast
  have hsum :
      (∑ d ∈ D, positiveRadixValue (B ^ d) (F d) (2 ^ K)) =
      ∑ d ∈ D, ∑' n : ℕ,
        (f d (Nat.totient (n + 1) : ZMod (2 ^ (k d))) : ℝ) /
          ((B : ℝ) ^ d) ^ (n + 1) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact hterm d hd
  have hclass := rational_finite_family_iff_even_constant D F K B hK hB hpos
  constructor
  · rintro ⟨q, hq⟩ d hd r hr hre
    have hc := hclass.mp ⟨q, hsum.trans hq⟩
    have hpowle : 2 ^ (k d) ≤ 2 ^ K :=
      Nat.pow_le_pow_right (by omega) (hle d hd)
    simpa only [F, Nat.cast_zero] using
      hc d hd r (lt_of_lt_of_le hr hpowle) hre
  · intro hc
    obtain ⟨q, hq⟩ := hclass.mpr (by
      intro d hd r hr hre
      have hmod : r % 2 ^ (k d) < 2 ^ (k d) :=
        Nat.mod_lt _ (pow_pos (by omega : 0 < (2 : ℕ)) _)
      have hlocal := hc d hd (r % 2 ^ (k d)) hmod
        (even_mod_two_pow r (k d) (hk d hd) hre)
      simpa only [F, ZMod.natCast_mod, Nat.cast_zero] using hlocal)
    exact ⟨q, hsum.symm.trans hq⟩

/-- A rational constant cannot cancel a nonconstant even-residue component. -/
theorem rational_mixed_moduli_with_constant_iff
    (D : Finset ℕ) (k : ℕ → ℕ)
    (f : (d : ℕ) → ZMod (2 ^ (k d)) → ℚ) (B : ℕ) (q₀ : ℚ)
    (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (hk : ∀ d ∈ D, 0 < k d) :
    (∃ q : ℚ, (q₀ : ℝ) + (∑ d ∈ D, ∑' n : ℕ,
      (f d (Nat.totient (n + 1) : ZMod (2 ^ (k d))) : ℝ) /
        ((B : ℝ) ^ d) ^ (n + 1)) = (q : ℝ)) ↔
      ∀ d ∈ D, ∀ r : ℕ, r < 2 ^ (k d) → Even r →
        f d (r : ZMod (2 ^ (k d))) = f d 0 := by
  have hclass := rational_mixed_moduli_iff_even_constant D k f B hB hpos hk
  constructor
  · rintro ⟨q, hq⟩
    apply hclass.mp
    refine ⟨q - q₀, ?_⟩
    push_cast
    linarith
  · intro hc
    obtain ⟨q, hq⟩ := hclass.mpr hc
    refine ⟨q₀ + q, ?_⟩
    rw [hq]
    push_cast
    ring

/-- The exact rational value retains both exceptional totient-one terms. -/
theorem mixed_value_eq_of_even_constant
    (D : Finset ℕ) (k : ℕ → ℕ)
    (f : (d : ℕ) → ZMod (2 ^ (k d)) → ℚ) (B : ℕ)
    (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (hk : ∀ d ∈ D, 0 < k d)
    (hc : ∀ d ∈ D, ∀ r : ℕ, r < 2 ^ (k d) → Even r →
      f d (r : ZMod (2 ^ (k d))) = f d 0) :
    (∑ d ∈ D, ∑' n : ℕ,
      (f d (Nat.totient (n + 1) : ZMod (2 ^ (k d))) : ℝ) /
        ((B : ℝ) ^ d) ^ (n + 1)) =
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
  simpa only [positiveRadixValue, ZMod.natCast_mod, Nat.cast_zero, Nat.cast_one,
    Nat.cast_pow] using
    (positiveRadixValue_eq_of_even_constant (B ^ d) hBd (hk d hd)
      (fun r : ℕ => f d (r : ZMod (2 ^ (k d)))) (f d 0) (by
        intro r hr hre
        exact hc d hd r hr (Nat.even_iff.mpr hre)))

#print axioms rational_mixed_moduli_iff_even_constant
#print axioms rational_mixed_moduli_with_constant_iff
#print axioms mixed_value_eq_of_even_constant

end ErdosProblems.Erdos249.FiniteDilationMixedModuli
