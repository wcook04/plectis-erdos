import ErdosProblems.Erdos1049.PaperR20.FiniteRemainderSummation

/-!
# The literal moment as a finite rational kernel

This algebraic identity is valid before any partial-fraction certificate is
supplied. It identifies the rational function checked by a polynomial witness
with the actual moment summand in the paper.
-/

namespace ErdosProblems.Erdos1049.PaperR20
open PaperR10
open scoped BigOperators
noncomputable section

def momentRationalKernel (q : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  x ^ (m + 1) * (∏ j ∈ Finset.range m, (1 - q ^ (j + 1))) ^ 3 *
    (∏ j ∈ Finset.range m, (1 - q ^ (j + 1) * x)) /
      (∏ j ∈ Finset.range (m + 1), (1 - q ^ (m + 1 + j) * x))

theorem qPochhammerFinite_kernel (q : ℝ) (s t n : ℕ) :
    qPochhammerFinite (q ^ (s + t)) q n =
      ∏ j ∈ Finset.range n, (1 - q ^ (s + j) * q ^ t) := by
  unfold qPochhammerFinite
  apply Finset.prod_congr rfl
  intro j _
  simp only [pow_add]
  ring

theorem actualMomentTerm_eq_rationalKernel (q : ℝ) (m t : ℕ) :
    PaperR12.actualMomentTerm q m t = momentRationalKernel q m (q ^ t) := by
  have hbase : qPochhammerFinite q q m =
      ∏ j ∈ Finset.range m, (1 - q ^ (j + 1)) := by
    simp only [qPochhammerFinite, pow_succ']
  have hnum : qPochhammerFinite (q ^ (t + 1)) q m =
      ∏ j ∈ Finset.range m, (1 - q ^ (j + 1) * q ^ t) := by
    simpa only [Nat.add_comm 1 t, Nat.add_comm 1] using
      qPochhammerFinite_kernel q 1 t m
  have hden : qPochhammerFinite (q ^ (m + t + 1)) q (m + 1) =
      ∏ j ∈ Finset.range (m + 1), (1 - q ^ (m + 1 + j) * q ^ t) := by
    simpa only [show m + 1 + t = m + t + 1 by omega] using
      qPochhammerFinite_kernel q (m + 1) t (m + 1)
  unfold PaperR12.actualMomentTerm momentRationalKernel
  rw [hbase, hnum, hden, ← pow_mul, Nat.mul_comm t (m + 1)]

/-- A finite rational-function identity is enough; the certificate need not
perform or approximate the infinite sum. -/
theorem actualMoment_eq_of_rationalKernel_certificate {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ)
    (A : Fin m → ℝ) (C : Fin (m + 1) → ℝ)
    (hcertificate : ∀ t : ℕ,
      momentRationalKernel q m (q ^ t) = finiteRationalKernel q m A C t) :
    PaperR12.actualMoment q m =
      (∑ k, C k) * PaperR16.lambert q +
        ∑ j, A j / (1 - q ^ (j.val + 1)) -
        ∑ k, C k * finiteLambertPrefix q (m + k.val) := by
  apply actualMoment_eq_of_finiteRationalKernel_certificate hq0 hq1 m A C
  intro t
  exact (actualMomentTerm_eq_rationalKernel q m t).trans (hcertificate t)

/-- Clear the inverse powers in a finite product without expanding it. -/
theorem inverse_power_product (p : ℝ) (hp : p ≠ 0) (a n : ℕ) (x : ℝ) :
    (∏ j ∈ Finset.range n, (1 - (p⁻¹) ^ (a + j) * x)) =
      (∏ j ∈ Finset.range n, (p ^ (a + j) - x)) /
        p ^ (∑ j ∈ Finset.range n, (a + j)) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [inv_pow]
  field_simp [hp]
  <;> ring

/-- The power balance is a finite natural-number check for each certificate
index. This form permits the producer to remove unnecessary powers of p. -/
theorem momentRationalKernel_clear (p : ℝ) (hp : p ≠ 0) (m d e : ℕ) (x : ℝ)
    (hbalance : (∑ j ∈ Finset.range (m + 1), (m + 1 + j)) + d =
      4 * (∑ j ∈ Finset.range m, (j + 1)) + e)
    (hden : (∏ j ∈ Finset.range (m + 1), (p ^ (m + 1 + j) - x)) ≠ 0) :
    p ^ d * momentRationalKernel (p⁻¹) m x *
        (∏ j ∈ Finset.range (m + 1), (p ^ (m + 1 + j) - x)) =
      p ^ e * x ^ (m + 1) *
        (∏ j ∈ Finset.range m, (p ^ (j + 1) - 1)) ^ 3 *
        (∏ j ∈ Finset.range m, (p ^ (j + 1) - x)) := by
  let T := ∑ j ∈ Finset.range m, (j + 1)
  let S := ∑ j ∈ Finset.range (m + 1), (m + 1 + j)
  have hpower : p ^ d * p ^ S = p ^ e * (p ^ T) ^ 3 * p ^ T := by
    calc
      p ^ d * p ^ S = p ^ (S + d) := by rw [pow_add]; ring
      _ = p ^ (4 * T + e) := by rw [hbalance]
      _ = p ^ e * (p ^ T) ^ 3 * p ^ T := by
        rw [show 4 * T + e = e + (T * 3 + T) by omega,
          pow_add, pow_add, pow_mul]
        ring
  have hbase := inverse_power_product p hp 1 m 1
  have hnum := inverse_power_product p hp 1 m x
  have hbottom := inverse_power_product p hp (m + 1) (m + 1) x
  simp only [one_mul, mul_one, Nat.add_comm 1] at hbase hnum
  unfold momentRationalKernel
  rw [hbase, hnum, hbottom]
  change p ^ d *
    (x ^ (m + 1) * ((∏ j ∈ Finset.range m, (p ^ (j + 1) - 1)) / p ^ T) ^ 3 *
      ((∏ j ∈ Finset.range m, (p ^ (j + 1) - x)) / p ^ T) /
      ((∏ j ∈ Finset.range (m + 1), (p ^ (m + 1 + j) - x)) / p ^ S)) * _ = _
  field_simp [hp, hden]
  linear_combination
    (x ^ (m + 1) * (∏ j ∈ Finset.range m, (p ^ (j + 1) - 1)) ^ 3 *
      (∏ j ∈ Finset.range m, (p ^ (j + 1) - x))) * hpower

#print axioms actualMomentTerm_eq_rationalKernel
#print axioms actualMoment_eq_of_rationalKernel_certificate
#print axioms momentRationalKernel_clear

end
end ErdosProblems.Erdos1049.PaperR20
