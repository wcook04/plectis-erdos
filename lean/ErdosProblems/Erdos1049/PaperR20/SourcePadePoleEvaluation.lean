import ErdosProblems.Erdos1049.PaperR20.SourcePadeQuotient
import ErdosProblems.Erdos1049.PaperR20.FiniteRemainderCertificateConsumer

/-!
# Exact pole evaluation for the all-index Padé remainder

This file evaluates the cleared numerator at each literal denominator root.
The calculation is entirely in `ℤ[p]`: powers and signs are separated from
three consecutive Delta products, and the latter are identified with the
already constructed source residue.  This is the root input for the final
finite interpolation argument.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Finset Polynomial
open scoped BigOperators

noncomputable section

private def sourceTriangle (m : ℕ) : ℕ :=
  ∑ j ∈ range m, (j + 1)

private def sourcePoleDenominatorPower (m k : ℕ) : ℕ :=
  (∑ j ∈ range k, (m + 1 + j)) + (m - k) * (m + 1 + k)

/-- `n(n+1)/2 = n(n-1)/2 + n`, the step between consecutive triangular numbers. -/
private theorem triangle_succ_div (n : ℕ) :
    n * (n + 1) / 2 = n * (n - 1) / 2 + n := by
  have hm : n * (n + 1) = n * (n - 1) + 2 * n := by
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel]
      ring
  rw [hm, Nat.add_mul_div_left _ _ (by norm_num : (0 : ℕ) < 2)]

/-- `n(n-1)` is even, so twice its half plus `n` is `n²`. -/
private theorem two_mul_triangle_pred_add (n : ℕ) :
    2 * (n * (n - 1) / 2) + n = n * n := by
  have hev : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
  rw [Nat.mul_div_cancel' hev]
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel]
    ring

private theorem sourceTriangle_eq (m : ℕ) :
    sourceTriangle m = m * (m + 1) / 2 := by
  unfold sourceTriangle
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_range_id, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one, Nat.choose_two_right]
  rw [triangle_succ_div]

private theorem sourcePoleDenominatorPower_eq (m k : ℕ) (hk : k ≤ m) :
    sourcePoleDenominatorPower m k =
      m * (m + 1) + k * m - k * (k + 1) / 2 := by
  unfold sourcePoleDenominatorPower
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_range_id, Finset.sum_const, Finset.card_range,
    smul_eq_mul, Nat.choose_two_right]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, triangle_succ_div]
  have h2T := two_mul_triangle_pred_add k
  symm
  apply Nat.sub_eq_of_eq_add
  nlinarith [h2T]

private theorem pow_sub_pow_factor (a b : ℕ) (hab : a ≤ b) :
    (X : ℤ[X]) ^ a - X ^ b =
      -(X ^ a * (X ^ (b - a) - 1)) := by
  have hb : (X : ℤ[X]) ^ b = X ^ a * X ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_of_le hab]
  rw [hb]
  ring

/-- Product in the cleared numerator after substituting the pole
`x=p^(m+1+k)`. -/
private theorem sourceNumeratorPoleProduct (m k : ℕ) :
    (∏ j ∈ range m,
        ((X : ℤ[X]) ^ (j + 1) - X ^ (m + 1 + k))) =
      (-1 : ℤ[X]) ^ m * X ^ sourceTriangle m *
        sourceDeltaSegmentPoly k m := by
  calc
    _ = ∏ j ∈ range m,
        (-(X : ℤ[X]) ^ (j + 1) *
          (X ^ (m + k - j) - 1)) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      rw [pow_sub_pow_factor (j + 1) (m + 1 + k) (by omega)]
      have hexp : m + 1 + k - (j + 1) = m + k - j := by omega
      rw [hexp]
      ring
    _ = (∏ j ∈ range m, (-1 : ℤ[X]) * X ^ (j + 1)) *
        ∏ j ∈ range m, (X ^ (m + k - j) - 1) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      ring
    _ = ((-1 : ℤ[X]) ^ m * X ^ sourceTriangle m) *
        ∏ j ∈ range m, (X ^ (m + k - j) - 1) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Finset.prod_pow_eq_pow_sum]
      rfl
    _ = _ := by
      unfold sourceDeltaSegmentPoly
      rw [← Finset.prod_range_reflect
        (fun j => (X : ℤ[X]) ^ (k + j + 1) - 1) m]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      have hexp : m + k - j = k + (m - 1 - j) + 1 := by omega
      rw [hexp]

private theorem erase_range_pole_split (m k : ℕ) (hk : k ≤ m) :
    (range (m + 1)).erase k =
      range k ∪ (range (m - k)).image (fun r => k + 1 + r) := by
  ext j
  simp only [mem_erase, mem_range, mem_union, mem_image]
  constructor
  · rintro ⟨hne, hj⟩
    by_cases hjk : j < k
    · exact Or.inl hjk
    · right
      refine ⟨j - (k + 1), ?_, ?_⟩
      · omega
      · omega
  · intro hj
    constructor
    · rcases hj with hj | ⟨r, hr, rfl⟩ <;> omega
    · rcases hj with hj | ⟨r, hr, rfl⟩ <;> omega

/-- Product of all denominator factors except the pole factor. -/
private theorem sourceDenominatorExceptPoleProduct (m k : ℕ) (hk : k ≤ m) :
    (∏ j ∈ (range (m + 1)).erase k,
        ((X : ℤ[X]) ^ (m + 1 + j) - X ^ (m + 1 + k))) =
      (-1 : ℤ[X]) ^ k * X ^ sourcePoleDenominatorPower m k *
        sourceDeltaPoly k * sourceDeltaPoly (m - k) := by
  rw [erase_range_pole_split m k hk]
  have hdis : Disjoint (range k) ((range (m - k)).image (fun r => k + 1 + r)) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [Finset.mem_image] at hj'
    obtain ⟨r, hr, hrj⟩ := hj'
    have hjk := Finset.mem_range.mp hj
    rw [Finset.mem_range] at hr
    omega
  rw [Finset.prod_union hdis]
  have hhead :
      (∏ j ∈ range k,
          ((X : ℤ[X]) ^ (m + 1 + j) - X ^ (m + 1 + k))) =
        (-1 : ℤ[X]) ^ k *
          X ^ (∑ j ∈ range k, (m + 1 + j)) * sourceDeltaPoly k := by
    calc
      _ = ∏ j ∈ range k,
          (-(X : ℤ[X]) ^ (m + 1 + j) * (X ^ (k - j) - 1)) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        rw [pow_sub_pow_factor (m + 1 + j) (m + 1 + k) (by omega)]
        have hexp : m + 1 + k - (m + 1 + j) = k - j := by omega
        rw [hexp]
        ring
      _ = (∏ j ∈ range k, (-1 : ℤ[X]) * X ^ (m + 1 + j)) *
          ∏ j ∈ range k, (X ^ (k - j) - 1) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro j _
        ring
      _ = ((-1 : ℤ[X]) ^ k *
            X ^ (∑ j ∈ range k, (m + 1 + j))) *
          ∏ j ∈ range k, (X ^ (k - j) - 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
          Finset.prod_pow_eq_pow_sum]
      _ = _ := by
        unfold sourceDeltaPoly
        rw [← Finset.prod_range_reflect
          (fun j => (X : ℤ[X]) ^ (j + 1) - 1) k]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        have hexp : k - j = k - 1 - j + 1 := by omega
        rw [hexp]
  have htail :
      (∏ j ∈ (range (m - k)).image (fun r => k + 1 + r),
          ((X : ℤ[X]) ^ (m + 1 + j) - X ^ (m + 1 + k))) =
        X ^ ((m - k) * (m + 1 + k)) * sourceDeltaPoly (m - k) := by
    rw [Finset.prod_image]
    · calc
        (∏ r ∈ range (m - k),
            ((X : ℤ[X]) ^ (m + 1 + (k + 1 + r)) - X ^ (m + 1 + k))) =
          ∏ r ∈ range (m - k),
            (X ^ (m + 1 + k) * (X ^ (r + 1) - 1)) := by
              apply Finset.prod_congr rfl
              intro r hr
              have hpow :
                  (X : ℤ[X]) ^ (m + 1 + (k + 1 + r)) =
                    X ^ (m + 1 + k) * X ^ (r + 1) := by
                rw [← pow_add]
                congr 1
                omega
              rw [hpow]
              ring
        _ = X ^ ((m - k) * (m + 1 + k)) * sourceDeltaPoly (m - k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_range, ← pow_mul, Nat.mul_comm (m + 1 + k) (m - k)]
          rfl
    · intro a ha b hb hab
      simp only at hab
      omega
  rw [hhead, htail]
  unfold sourcePoleDenominatorPower
  rw [pow_add]
  ring

/-- The Delta factors in the residue and in the erased denominator collapse to
`Delta_m^3` times the remaining numerator segment. -/
private theorem sourceResidue_mul_denominatorDeltas (m k : ℕ) (hk : k ≤ m) :
    sourceResiduePoly m k * sourceDeltaPoly k * sourceDeltaPoly (m - k) =
      C ((-1 : ℤ) ^ (m + k)) *
        X ^ (m + 1 + k * (k + 1) / 2) *
        sourceDeltaPoly m ^ 3 * sourceDeltaSegmentPoly k m := by
  have hmk : k + (m - k) = m := Nat.add_sub_of_le hk
  have h1 := sourceDelta_add k (m - k)
  have h2 := sourceDelta_add (m - k) k
  have h3 := sourceDelta_add k m
  rw [hmk] at h1
  have hcomm : m - k + k = m := by omega
  rw [hcomm] at h2
  have h3' : sourceDeltaPoly (m + k) =
      sourceDeltaPoly k * sourceDeltaSegmentPoly k m := by
    simpa [Nat.add_comm] using h3
  unfold sourceResiduePoly
  rw [h3']
  calc
    _ = C ((-1 : ℤ) ^ (m + k)) *
        X ^ (m + 1 + k * (k + 1) / 2) *
        (sourceDeltaPoly k * sourceDeltaSegmentPoly k (m - k)) ^ 2 *
        (sourceDeltaPoly (m - k) * sourceDeltaSegmentPoly (m - k) k) *
        sourceDeltaSegmentPoly k m := by ring
    _ = _ := by
      rw [← h1, ← h2]
      ring

private theorem sourcePoleExponentBalance (m k : ℕ) (hk : k ≤ m) :
    sourceQuotientClearE m + (m + 1 + k) * (m + 1) + sourceTriangle m =
      sourceQuotientClearD m + (m + 1 + k * (k + 1) / 2) +
        (m + 1 + k) + sourcePoleDenominatorPower m k := by
  rw [sourceTriangle_eq, triangle_succ_div]
  have hden := sourcePoleDenominatorPower_eq m k hk
  have hde := sourceQuotientClearD_sub_E m
  have hkbound :
      k * (k + 1) / 2 ≤ m * (m + 1) + k * m := by
    calc k * (k + 1) / 2 ≤ k * (k + 1) := Nat.div_le_self _ _
      _ ≤ m * (m + 1) := Nat.mul_le_mul hk (by omega)
      _ ≤ m * (m + 1) + k * m := Nat.le_add_right _ _
  have hden' : sourcePoleDenominatorPower m k + k * (k + 1) / 2 =
      m * (m + 1) + k * m := by omega
  -- Name the opaque quantities, then the balance is a polynomial identity in `ℤ`.
  set A := m * (m - 1) / 2 with hA
  set T := k * (k + 1) / 2 with hT
  set P := sourcePoleDenominatorPower m k with hP
  set E := sourceQuotientClearE m with hE
  set D := sourceQuotientClearD m with hD
  zify at hde hden' ⊢
  linear_combination -hde - hden'

/-- **Exact pole evaluation.**  At the pole indexed by `k`, the literal cleared
numerator is the `k`th residue contribution times the erased denominator. -/
theorem eval_clearedMomentNumeratorPoly_at_pole
    (m k : ℕ) (hk : k ≤ m) :
    (clearedMomentNumeratorPoly m (sourceQuotientClearE m)).eval
        ((X : ℤ[X]) ^ (m + 1 + k)) =
      X ^ sourceQuotientClearD m * sourceResiduePoly m k *
        X ^ (m + 1 + k) *
        (clearedMomentDenominatorExceptPoly m k).eval
          ((X : ℤ[X]) ^ (m + 1 + k)) := by
  rw [clearedMomentNumeratorPoly, clearedMomentDenominatorExceptPoly]
  simp only [eval_mul, eval_pow, eval_X, eval_C, eval_prod, eval_sub]
  rw [sourceNumeratorPoleProduct, sourceDenominatorExceptPoleProduct m k hk]
  have hdelta := sourceResidue_mul_denominatorDeltas m k hk
  have hexp := sourcePoleExponentBalance m k hk
  calc
    (X ^ sourceQuotientClearE m * sourceDeltaPoly m ^ 3) *
          (X ^ (m + 1 + k)) ^ (m + 1) *
          ((-1 : ℤ[X]) ^ m * X ^ sourceTriangle m *
            sourceDeltaSegmentPoly k m) =
        X ^ sourceQuotientClearD m * X ^ (m + 1 + k) *
          ((-1 : ℤ[X]) ^ k * X ^ sourcePoleDenominatorPower m k) *
          (C ((-1 : ℤ) ^ (m + k)) *
            X ^ (m + 1 + k * (k + 1) / 2) *
            sourceDeltaPoly m ^ 3 * sourceDeltaSegmentPoly k m) := by
      have hk_sign_sq : ((-1 : ℤ[X]) ^ k) * ((-1 : ℤ[X]) ^ k) = 1 := by
        rw [← pow_add, show k + k = 2 * k by omega, pow_mul]
        norm_num
      have hsign : ((-1 : ℤ[X]) ^ m) =
          (-1 : ℤ[X]) ^ k * (-1 : ℤ[X]) ^ (m + k) := by
        rw [pow_add]
        calc
          (-1 : ℤ[X]) ^ m = 1 * (-1 : ℤ[X]) ^ m := by simp
          _ = (((-1 : ℤ[X]) ^ k) * ((-1 : ℤ[X]) ^ k)) *
                (-1 : ℤ[X]) ^ m := by rw [hk_sign_sq]
          _ = (-1 : ℤ[X]) ^ k *
                ((-1 : ℤ[X]) ^ m * (-1 : ℤ[X]) ^ k) := by ring
      have hpow :
          (X : ℤ[X]) ^ sourceQuotientClearE m *
              X ^ ((m + 1 + k) * (m + 1)) * X ^ sourceTriangle m =
            (X : ℤ[X]) ^ sourceQuotientClearD m *
              X ^ (m + 1 + k * (k + 1) / 2) *
              X ^ (m + 1 + k) * X ^ sourcePoleDenominatorPower m k := by
        rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
        rw [hexp]
      rw [← pow_mul]
      simp only [map_pow, map_neg, map_one]
      calc
        _ = (-1 : ℤ[X]) ^ m *
              (X ^ sourceQuotientClearE m *
                X ^ ((m + 1 + k) * (m + 1)) * X ^ sourceTriangle m) *
              sourceDeltaPoly m ^ 3 * sourceDeltaSegmentPoly k m := by ring
        _ = (-1 : ℤ[X]) ^ k * (-1 : ℤ[X]) ^ (m + k) *
              (X ^ sourceQuotientClearD m *
                X ^ (m + 1 + k * (k + 1) / 2) *
                X ^ (m + 1 + k) * X ^ sourcePoleDenominatorPower m k) *
              sourceDeltaPoly m ^ 3 * sourceDeltaSegmentPoly k m := by
                rw [hsign, hpow]
        _ = _ := by ring
    _ = X ^ sourceQuotientClearD m * sourceResiduePoly m k *
          X ^ (m + 1 + k) *
          ((-1 : ℤ[X]) ^ k * X ^ sourcePoleDenominatorPower m k *
            sourceDeltaPoly k * sourceDeltaPoly (m - k)) := by
      rw [← hdelta]
      ring

#print axioms eval_clearedMomentNumeratorPoly_at_pole

end
end ErdosProblems.Erdos1049.PaperR20
