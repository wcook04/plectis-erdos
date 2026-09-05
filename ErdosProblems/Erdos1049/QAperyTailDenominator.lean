import ErdosProblems.Erdos1049.TwoSelectorRemainderEscape
import Mathlib.Data.Nat.Prime.Int

/-!
# Erdős #1049: q-Apéry tail-denominator nonvanishing

The primitive q-Apéry rows found in the exact moving-tail computation have a
new arithmetic feature: odd primes can divide every denominator coordinate in
a long tail.  This file isolates the source-independent consumer of that
feature.  At a rational target `a / q`, such a prime certifies nonvanishing as
soon as it divides the denominator coordinate but divides neither the
numerator coordinate nor `q`.

For two rows there is an automatic version.  If the prime divides both
denominator coordinates but its square does not divide their exterior
determinant, at least one numerator coordinate is a unit modulo the prime.
Thus at least one rational linear form has the exact `1 / q` gap.
-/

namespace ErdosProblems.Erdos1049

/-! ## A finite-window selector consumer -/

/-- If every denominator coordinate vanishes modulo `N`, only the numerator
coordinate has to be pigeonholed.  Thus `N < 2^k`, rather than `N^2 < 2^k`,
already gives a nontrivial binary selector collision in both coordinates.

This is the exact finite-window consumer of a q-Apéry tail-denominator
divisor.  It requires no claim that a fixed divisor persists on the infinite
tail. -/
theorem zmod_binary_collision_of_zero_denominator_coordinates
    {N k : ℕ} [NeZero N]
    (w : Fin k → ZMod N × ZMod N)
    (hzero : ∀ i, (w i).2 = 0)
    (hcard : N < 2 ^ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  classical
  let f : (Fin k → Bool) → ZMod N :=
    fun s ↦ ∑ i, if s i then (w i).1 else 0
  have hcard' : Fintype.card (ZMod N) < 2 ^ Fintype.card (Fin k) := by
    simpa using hcard
  obtain ⟨s, t, hne, hst⟩ :=
    BezoutPluckerJets.exists_binary_collision_of_card_lt f hcard'
  refine ⟨s, t, hne, ?_⟩
  apply Prod.ext
  · simpa [Prod.fst_sum, apply_ite, f] using hst
  · simp [Prod.snd_sum, apply_ite, hzero]

/-- A prime supported in the coefficient `B`, but absent from both `A` and the
rational denominator `q`, prevents the cleared numerator `B*a-A*q` from
vanishing. -/
theorem integerLinearFormNumerator_ne_zero_of_prime_support
    {ell : ℕ} (hell : ell.Prime)
    (a q A B : ℤ)
    (hellB : (ell : ℤ) ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    B * a - A * q ≠ 0 := by
  intro hzero
  have heq : B * a = A * q := sub_eq_zero.mp hzero
  have hellProduct : (ell : ℤ) ∣ A * q := by
    rw [← heq]
    exact dvd_mul_of_dvd_left hellB a
  have hellInt : Prime (ell : ℤ) := Nat.prime_iff_prime_int.mp hell
  rcases hellInt.dvd_mul.mp hellProduct with hellA' | hellq'
  · exact hellA hellA'
  · exact hellq hellq'

/-- The prime-support certificate transported to the real linear form at a
positive rational target. -/
theorem rational_integerLinearForm_ne_zero_of_prime_support
    {ell : ℕ} (hell : ell.Prime)
    (a q A B : ℤ) (hq : 0 < q)
    (hellB : (ell : ℤ) ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) ≠ 0 := by
  have hnum := integerLinearFormNumerator_ne_zero_of_prime_support
    hell a q A B hellB hellA hellq
  have hqR : (q : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hq)
  have hnumR : ((B * a - A * q : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast hnum
  have hform :
      (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) =
        ((B * a - A * q : ℤ) : ℝ) / (q : ℝ) := by
    rw [show ((B * a - A * q : ℤ) : ℝ) =
      (B : ℝ) * (a : ℝ) - (A : ℝ) * (q : ℝ) by push_cast; ring]
    field_simp
  rw [hform]
  exact div_ne_zero hnumR hqR

/-- A tail-denominator prime gives the full rational `1/q` gap, not merely
qualitative nonvanishing. -/
theorem rational_integerLinearForm_gap_of_prime_support
    {ell : ℕ} (hell : ell.Prime)
    (a q A B : ℤ) (hq : 0 < q)
    (hellB : (ell : ℤ) ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  apply rational_integerLinearForm_gap a q A B hq
  exact rational_integerLinearForm_ne_zero_of_prime_support
    hell a q A B hq hellB hellA hellq

/-- A prime-power tail support gives the same rational gap.  The source
consumer only needs one copy of the prime, so the higher exponent is retained
as an explicit interface for denominator data without changing the
nonvanishing boundary. -/
theorem rational_integerLinearForm_gap_of_prime_power_support
    {ell r : ℕ} (hell : ell.Prime) (hr : r ≠ 0)
    (a q A B : ℤ) (hq : 0 < q)
    (hellPowB : (ell : ℤ) ^ r ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  have hellB : (ell : ℤ) ∣ B :=
    (dvd_pow_self (ell : ℤ) hr).trans hellPowB
  apply rational_integerLinearForm_gap_of_prime_support
    hell a q A B hq hellB hellA hellq

/-- If `ell` divides both denominator coordinates while `ell^2` does not
divide the exterior determinant, then at least one numerator coordinate is a
unit modulo `ell`. -/
theorem twoSelector_one_numerator_not_dvd_of_prime_tail_support
    {ell : ℕ}
    (A₁ B₁ A₂ B₂ : ℤ)
    (hellB₁ : (ell : ℤ) ∣ B₁)
    (hellB₂ : (ell : ℤ) ∣ B₂)
    (hdet : ¬ (ell : ℤ) ^ 2 ∣ A₁ * B₂ - A₂ * B₁) :
    ¬ (ell : ℤ) ∣ A₁ ∨ ¬ (ell : ℤ) ∣ A₂ := by
  by_contra hboth
  simp only [not_or, not_not] at hboth
  rcases hboth with ⟨hellA₁, hellA₂⟩
  apply hdet
  have hleft : (ell : ℤ) * ell ∣ A₁ * B₂ :=
    mul_dvd_mul hellA₁ hellB₂
  have hright : (ell : ℤ) * ell ∣ A₂ * B₁ :=
    mul_dvd_mul hellA₂ hellB₁
  simpa [pow_two] using dvd_sub hleft hright

/-- Two rows with a common tail-denominator prime and only one determinant
power cannot both have a sub-`1/q` remainder at a rational target whose
denominator is prime to `ell`. -/
theorem rational_twoSelector_gap_of_prime_tail_support
    {ell : ℕ} (hell : ell.Prime)
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hellq : ¬ (ell : ℤ) ∣ q)
    (hellB₁ : (ell : ℤ) ∣ B₁)
    (hellB₂ : (ell : ℤ) ∣ B₂)
    (hdet : ¬ (ell : ℤ) ^ 2 ∣ A₁ * B₂ - A₂ * B₁) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by
  rcases twoSelector_one_numerator_not_dvd_of_prime_tail_support
      A₁ B₁ A₂ B₂ hellB₁ hellB₂ hdet with hellA₁ | hellA₂
  · exact Or.inl <| rational_integerLinearForm_gap_of_prime_support
      hell a q A₁ B₁ hq hellB₁ hellA₁ hellq
  · exact Or.inr <| rational_integerLinearForm_gap_of_prime_support
      hell a q A₂ B₂ hq hellB₂ hellA₂ hellq

end ErdosProblems.Erdos1049
