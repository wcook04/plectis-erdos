import ErdosProblems.Erdos1049.SourcePolynomialR11
import Mathlib

/-!
# Literal B coefficient and its first polynomial clearing


This constructs the finite source expression itself, including its negative
powers, and proves D*B is an integral polynomial. It does NOT claim the
additional X^M or Omega cancellation. No polynomial-inclusion hypothesis is
used in the construction or the clearing theorem.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open scoped BigOperators
open PaperR11

/-- The explicit complement to the divisors of j inside [1,15*n]. -/
noncomputable def sourceDQuotient (n j : ℕ) : ℤ[X] :=
  ∏ l ∈ (Finset.Icc 1 (15 * n) \ j.divisors), cyclotomic l ℤ

lemma source_divisors_subset (n j : ℕ) (hj0 : 0 < j) (hj : j ≤ 15 * n) :
    j.divisors ⊆ Finset.Icc 1 (15 * n) := by
  intro l hl
  apply Finset.mem_Icc.mpr
  exact ⟨Nat.pos_of_mem_divisors hl,
    (Nat.le_of_dvd hj0 (Nat.mem_divisors.mp hl).1).trans hj⟩

/-- All j <= 15*n denominators divide D, with a displayed integral quotient. -/
theorem sourceDQuotient_factor (n j : ℕ) (hj0 : 0 < j) (hj : j ≤ 15 * n) :
    (X ^ j - 1 : ℤ[X]) * sourceDQuotient n j = sourceD n := by
  classical
  have hs := source_divisors_subset n j hj0 hj
  rw [sourceDQuotient, sourceD, ← prod_cyclotomic_eq_X_pow_sub_one hj0 ℤ]
  rw [mul_comm, ← Finset.prod_union Finset.sdiff_disjoint,
    Finset.sdiff_union_of_subset hs]

/-- This arithmetic check prevents natural subtraction from hiding a negative
raw exponent in the second channel of B. -/
lemma source_shift_exponent_le (n s j : ℕ) (hs : s ≤ 13 * n)
    (hj : j ≤ 14 * n) :
    j * (2 * n + s) ≤ sourceM n + sourceAExponent n s := by
  have hprod : j * (2 * n + s) ≤ (14 * n) * (15 * n) :=
    Nat.mul_le_mul hj (by omega)
  unfold sourceM sourceAExponent
  nlinarith [Nat.zero_le (s.choose 2), Nat.zero_le ((n + 1) * s)]

noncomputable def sourceShiftedASummand (n s j : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) *
    X ^ (sourceM n + sourceAExponent n s - j * (2 * n + s)) *
    sourceGaussianProduct n s

/-- Multiplication, not rational-function cancellation, identifies the shift. -/
theorem sourceShiftedASummand_factor (n s j : ℕ) (hs : s ≤ 13 * n)
    (hj : j ≤ 14 * n) :
    X ^ (j * (2 * n + s)) * sourceShiftedASummand n s j =
      sourceASummand n s := by
  have hb := source_shift_exponent_le n s j hs hj
  have he : j * (2 * n + s) +
      (sourceM n + sourceAExponent n s - j * (2 * n + s)) =
      sourceM n + sourceAExponent n s := by omega
  unfold sourceShiftedASummand sourceASummand
  calc
    _ = C ((-1 : ℤ) ^ s) *
        (X ^ (j * (2 * n + s)) *
          X ^ (sourceM n + sourceAExponent n s - j * (2 * n + s))) *
          sourceGaussianProduct n s := by ring
    _ = _ := by rw [← pow_add, he]

/-- The explicit integral numerator after D clearing, before either improvement. -/
noncomputable def sourceClearedB (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1),
    ((∑ l ∈ Finset.Icc 1 (2 * n + s),
        sourceASummand n s * sourceDQuotient n l) +
      (∑ j ∈ Finset.Icc 1 (14 * n),
        sourceShiftedASummand n s j * sourceDQuotient n j))

/-- Literal finite B expression for any scalar realisation of Z[X].
For the rational function use the canonical fraction-field map; for a real
base use Polynomial.eval₂RingHom (Int.castRingHom R) x. -/
noncomputable def sourceBValue {K : Type*} [Field K]
    (f : ℤ[X] →+* K) (n : ℕ) : K :=
  ∑ s ∈ Finset.range (13 * n + 1), f (sourceASummand n s) *
    ((∑ l ∈ Finset.Icc 1 (2 * n + s), ((f X) ^ l - 1)⁻¹) +
      ∑ j ∈ Finset.Icc 1 (14 * n),
        (f X) ^ (-((j * (2 * n + s) : ℕ) : ℤ)) * ((f X) ^ j - 1)⁻¹)

lemma sourceDQuotient_map {K : Type*} [Field K]
    (f : ℤ[X] →+* K) (n j : ℕ) (hj0 : 0 < j) (hj : j ≤ 15 * n)
    (hden : (f X) ^ j - 1 ≠ 0) :
    f (sourceDQuotient n j) = f (sourceD n) * ((f X) ^ j - 1)⁻¹ := by
  have h := congrArg f (sourceDQuotient_factor n j hj0 hj)
  simp only [map_mul, map_sub, map_pow, map_one] at h
  apply mul_right_cancel₀ hden
  calc
    f (sourceDQuotient n j) * ((f X) ^ j - 1) = f (sourceD n) := by
      simpa only [mul_comm] using h
    _ = (f (sourceD n) * ((f X) ^ j - 1)⁻¹) * ((f X) ^ j - 1) := by
      rw [mul_assoc, inv_mul_cancel₀ hden, mul_one]

lemma sourceShiftedASummand_map {K : Type*} [Field K]
    (f : ℤ[X] →+* K) (n s j : ℕ) (hs : s ≤ 13 * n) (hj : j ≤ 14 * n)
    (hx : f X ≠ 0) :
    f (sourceShiftedASummand n s j) =
      f (sourceASummand n s) * (f X) ^ (-((j * (2 * n + s) : ℕ) : ℤ)) := by
  have h := congrArg f (sourceShiftedASummand_factor n s j hs hj)
  simp only [map_mul, map_pow] at h
  rw [zpow_neg, zpow_natCast]
  have hp : (f X) ^ (j * (2 * n + s)) ≠ 0 := pow_ne_zero _ hx
  apply mul_right_cancel₀ hp
  calc
    f (sourceShiftedASummand n s j) * (f X) ^ (j * (2 * n + s)) =
        f (sourceASummand n s) := by simpa only [mul_comm] using h
    _ = _ := by rw [mul_assoc, inv_mul_cancel₀ hp, mul_one]

/-- The literal expression, not an abstract source package, has D-clearing.
The premises are only avoidance of the explicitly displayed finite poles. -/
theorem actual_B_first_clearing {K : Type*} [Field K]
    (f : ℤ[X] →+* K) (n : ℕ) (hx : f X ≠ 0)
    (hden : ∀ j ∈ Finset.Icc 1 (15 * n), (f X) ^ j - 1 ≠ 0) :
    f (sourceClearedB n) = f (sourceD n) * sourceBValue f n := by
  classical
  unfold sourceClearedB sourceBValue
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ 13 * n := by have h := Finset.mem_range.mp hs; omega
  have hfirst :
      f (∑ l ∈ Finset.Icc 1 (2 * n + s),
        sourceASummand n s * sourceDQuotient n l) =
      f (sourceD n) * (f (sourceASummand n s) *
        ∑ l ∈ Finset.Icc 1 (2 * n + s), ((f X) ^ l - 1)⁻¹) := by
    simp only [map_sum, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    obtain ⟨hl0, hl1⟩ := Finset.mem_Icc.mp hl
    have hlN : l ≤ 15 * n := by omega
    rw [sourceDQuotient_map f n l hl0 hlN (hden l (Finset.mem_Icc.mpr ⟨hl0, hlN⟩))]
    ring
  have hsecond :
      f (∑ j ∈ Finset.Icc 1 (14 * n),
        sourceShiftedASummand n s j * sourceDQuotient n j) =
      f (sourceD n) * (f (sourceASummand n s) *
        ∑ j ∈ Finset.Icc 1 (14 * n),
          (f X) ^ (-((j * (2 * n + s) : ℕ) : ℤ)) * ((f X) ^ j - 1)⁻¹) := by
    simp only [map_sum, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj0, hj1⟩ := Finset.mem_Icc.mp hj
    have hjN : j ≤ 15 * n := by omega
    rw [sourceShiftedASummand_map f n s j hs' hj1 hx,
      sourceDQuotient_map f n j hj0 hjN (hden j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩))]
    ring
  rw [map_add, hfirst, hsecond]
  ring

/-- No positive real source base is one of the finite poles. -/
lemma source_real_denominator_ne_zero (x : ℝ) (hx : 1 < x) (j : ℕ) (hj : 0 < j) :
    x ^ j - 1 ≠ 0 := by
  have hp : 1 < x ^ j := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hk : 1 ≤ x ^ k := one_le_pow₀ hx.le
    rw [pow_succ]
    nlinarith
  exact ne_of_gt (sub_pos.mpr hp)

noncomputable def sourceBReal (n : ℕ) (x : ℝ) : ℝ :=
  sourceBValue (Polynomial.eval₂RingHom (Int.castRingHom ℝ) x) n

/-- Unconditional specialisation at every x>1, including the degenerate n=0. -/
theorem actual_B_first_clearing_real (n : ℕ) (x : ℝ) (hx : 1 < x) :
    (sourceClearedB n).eval₂ (Int.castRingHom ℝ) x =
      (sourceD n).eval₂ (Int.castRingHom ℝ) x * sourceBReal n x := by
  unfold sourceBReal
  change (Polynomial.eval₂RingHom (Int.castRingHom ℝ) x) (sourceClearedB n) =
    (Polynomial.eval₂RingHom (Int.castRingHom ℝ) x) (sourceD n) *
      sourceBValue (Polynomial.eval₂RingHom (Int.castRingHom ℝ) x) n
  apply actual_B_first_clearing
  · simpa using (ne_of_gt (lt_trans zero_lt_one hx) : x ≠ 0)
  · intro j hj
    simpa using source_real_denominator_ne_zero x hx j (Finset.mem_Icc.mp hj).1

/-- The literal B as a rational function over Z, not just a real evaluation. -/
noncomputable def sourceBRational (n : ℕ) : RatFunc ℤ :=
  sourceBValue (algebraMap ℤ[X] (RatFunc ℤ)) n

lemma rationalPolynomial_X_ne_zero :
    algebraMap ℤ[X] (RatFunc ℤ) X ≠ 0 := by
  simpa only [Ne, IsFractionRing.to_map_eq_zero_iff] using
    (X_ne_zero : (X : ℤ[X]) ≠ 0)

lemma rationalPolynomial_pole_ne_zero (j : ℕ) (hj : 0 < j) :
    (algebraMap ℤ[X] (RatFunc ℤ) X) ^ j - 1 ≠ 0 := by
  have hp : (X ^ j - 1 : ℤ[X]) ≠ 0 := by
    simpa only [map_one] using
      (monic_X_pow_sub_C (1 : ℤ) (ne_of_gt hj)).ne_zero
  have hm : algebraMap ℤ[X] (RatFunc ℤ) (X ^ j - 1) ≠ 0 := by
    simpa only [Ne, IsFractionRing.to_map_eq_zero_iff] using hp
  simpa only [map_sub, map_pow, map_one] using hm

/-- The first clearing is an unconditional rational-function identity. -/
theorem actual_B_first_clearing_rational (n : ℕ) :
    algebraMap ℤ[X] (RatFunc ℤ) (sourceClearedB n) =
      algebraMap ℤ[X] (RatFunc ℤ) (sourceD n) * sourceBRational n := by
  apply actual_B_first_clearing _ n rationalPolynomial_X_ne_zero
  intro j hj
  exact rationalPolynomial_pole_ne_zero j (Finset.mem_Icc.mp hj).1

end ErdosProblems.Erdos1049.PaperR12
