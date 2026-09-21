import ErdosProblems.Erdos257.PaperCompleteR8.KernelRecurrence

/-!
# A logarithm-free prime-power sampling modulus

The actual weighted prime part is retained. For
Q = L (prod P)^H, either the complete P-part of a divides gcd(Q,a), or
that gcd is at least 2^H. This replaces floor-logarithm bookkeeping with
one uniform exponent, and is sufficient for the weighted analytic proof.

Pinned arithmetic APIs opened at the specified commit:
Mathlib/Data/Nat/Factorization/Basic.lean and Defs.lean;
Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean and Defs.lean.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

/-- The restricted prime product divides the full exponent, even if the
finite index set contains numbers outside the factorisation support. -/
theorem primeSetPart_dvd (P : Finset ℕ) {a : ℕ} (ha : 0 < a) :
    primeSetPart P a ∣ a := by
  classical
  let S := a.factorization.support
  have heq : (∏ p ∈ P ∪ S, p ^ a.factorization p) = a := by
    have hprod : (∏ p ∈ S, p ^ a.factorization p) =
        ∏ p ∈ P ∪ S, p ^ a.factorization p := by
      apply Finset.prod_subset Finset.subset_union_right
      intro p _hp hpS
      -- Mathlib/Data/Finsupp/Defs.lean: Finsupp.notMem_support_iff.
      have hz : a.factorization p = 0 := Finsupp.notMem_support_iff.mp hpS
      rw [hz, pow_zero]
    rw [← hprod]
    exact Nat.prod_factorization_pow_eq_self ha.ne'
  have hh := Finset.prod_dvd_prod_of_subset P (P ∪ S)
    (fun p => p ^ a.factorization p) Finset.subset_union_left
  rw [heq] at hh
  exact hh

theorem primeSetPart_pos (P : Finset ℕ) {a : ℕ} (ha : 0 < a) :
    0 < primeSetPart P a := Nat.pos_of_dvd_of_pos (primeSetPart_dvd P ha) ha

theorem primeWeightedTerm_nonneg (b : ℕ) (hb : 2 ≤ b)
    (P : Finset ℕ) (a : ℕ) : 0 ≤ primeWeightedTerm b P a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [primeWeightedTerm, Nat.cast_zero, zero_mul, div_zero, le_refl]
  · have hh := primeSetPart_pos P ha
    have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
      (kernel_den_pos hbR hh).le)

/-- Fixed-prefix factor L and a single common prime-power exponent H. -/
def primeSamplingModulus (L : ℕ) (P : Finset ℕ) (H : ℕ) : ℕ :=
  L * P.prod id ^ H

theorem primeSamplingModulus_pos {L : ℕ} (hL : 0 < L)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (H : ℕ) :
    0 < primeSamplingModulus L P H := by
  have hprod : 0 < P.prod id := Finset.prod_pos (fun p hp => (hP p hp).pos)
  exact Nat.mul_pos hL (Nat.pow_pos hprod)

theorem left_dvd_primeSamplingModulus (L : ℕ) (P : Finset ℕ) (H : ℕ) :
    L ∣ primeSamplingModulus L P H := dvd_mul_right _ _

/-- Restricted powers divide a common power of the product if their
exponents are bounded by that common exponent. -/
theorem primeSetPart_dvd_product_pow (P : Finset ℕ) (a H : ℕ)
    (h : ∀ p ∈ P, a.factorization p ≤ H) :
    primeSetPart P a ∣ P.prod id ^ H := by
  classical
  unfold primeSetPart
  revert h
  induction P using Finset.induction_on with
  | empty => intro h; simp only [Finset.prod_empty, one_pow, dvd_refl]
  | @insert p S hpS ih =>
    intro h
    have hhead : a.factorization p ≤ H := h p (Finset.mem_insert_self p S)
    have htail : ∀ q ∈ S, a.factorization q ≤ H :=
      fun q hq => h q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hpS, Finset.prod_insert hpS, mul_pow]
    exact Nat.mul_dvd_mul (pow_dvd_pow p hhead) (ih htail)

/-- Every selected prime's H-th power divides the sampling modulus. -/
theorem prime_pow_dvd_sampling (L : ℕ) (P : Finset ℕ) (H p : ℕ) (hp : p ∈ P) :
    p ^ H ∣ primeSamplingModulus L P H := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem id hp
  have hd : p ^ H ∣ P.prod id ^ H := by
    rw [hc, mul_pow]
    exact dvd_mul_right _ _
  exact dvd_mul_of_dvd_right hd L

/-- A conductor either has its full prime part represented in the modulus,
or belongs to the exponentially large-GCD branch. -/
theorem primeSamplingModulus_gcd_dichotomy {L : ℕ} (hL : 0 < L)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (H a : ℕ) (ha : 0 < a) :
    primeSetPart P a ∣ Nat.gcd (primeSamplingModulus L P H) a ∨
      2 ^ H ≤ Nat.gcd (primeSamplingModulus L P H) a := by
  classical
  by_cases hsmall : ∀ p ∈ P, a.factorization p ≤ H
  · apply Or.inl
    exact Nat.dvd_gcd
      (dvd_mul_of_dvd_right (primeSetPart_dvd_product_pow P a H hsmall) L)
      (primeSetPart_dvd P ha)
  · push_neg at hsmall
    obtain ⟨p, hp, hlarge⟩ := hsmall
    have hpa : p ^ H ∣ a :=
      ((hP p hp).pow_dvd_iff_le_factorization ha.ne').mpr hlarge.le
    have hpg : p ^ H ∣ Nat.gcd (primeSamplingModulus L P H) a :=
      Nat.dvd_gcd (prime_pow_dvd_sampling L P H p hp) hpa
    have hQ : 0 < primeSamplingModulus L P H := primeSamplingModulus_pos hL P hP H
    have hg : 0 < Nat.gcd (primeSamplingModulus L P H) a :=
      Nat.gcd_pos_of_pos_left a hQ
    exact Or.inr ((Nat.pow_le_pow_left (hP p hp).two_le H).trans
      (Nat.le_of_dvd hg hpg))

/-- The period length n/(B^n-1) decreases when n increases. -/
theorem geom_ratio_antitone (B : ℝ) (hB : 1 < B) (u v : ℕ)
    (hu : 0 < u) (huv : u ≤ v) :
    (v : ℝ) / (B ^ v - 1) ≤ (u : ℝ) / (B ^ u - 1) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hr := pow_sub_one_ratio_le hB u v hv huv
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have huDen : 0 < B ^ u - 1 := kernel_den_pos hB hu
  have hvDen : 0 < B ^ v - 1 := kernel_den_pos hB hv
  have hc := (div_le_div_iff₀ hvDen hvR).mp hr
  apply (div_le_div_iff₀ hvDen huDen).mpr
  simpa only [mul_comm] using hc

/-- Convenient large-GCD profile abstracted from the actual prime modulus. -/
def GcdProfile (Q G : ℕ) (h : ℕ → ℕ) : Prop :=
  ∀ a : ℕ, 0 < a → 0 < h a ∧
    (h a ∣ Nat.gcd Q a ∨ G ≤ Nat.gcd Q a)

theorem primeSamplingModulus_profile {L : ℕ} (hL : 0 < L)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (H : ℕ) :
    GcdProfile (primeSamplingModulus L P H) (2 ^ H) (primeSetPart P) :=
  fun a ha => ⟨primeSetPart_pos P ha,
    primeSamplingModulus_gcd_dichotomy hL P hP H a ha⟩

end ErdosProblems.Erdos257.PaperCompleteR8
end
