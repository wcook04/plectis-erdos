import ErdosProblems.Erdos1049.FiniteResidueInterpolationR14
import ErdosProblems.Erdos1049.QProductBoundsR10
import Mathlib

/-!
# Reciprocal factorials and reflected finite products

Reversal of finite q-factorials and the erased pole product. These are finite algebraic
identities. In particular no analytic source identity is used as a premise.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Finset Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

def triangularExponent (m : ℕ) : ℕ := m.choose 2 + m

lemma triangularExponent_succ (m : ℕ) :
    triangularExponent (m + 1) = triangularExponent m + (m + 1) := by
  simp only [triangularExponent, choose_two_succ]

lemma inverse_power_mul_power (p : K) (hp : p ≠ 0) {a b : ℕ} (hab : a ≤ b) :
    (p⁻¹) ^ a * p ^ b = p ^ (b - a) := by
  apply mul_right_cancel₀ (pow_ne_zero a hp)
  calc
    ((p⁻¹) ^ a * p ^ b) * p ^ a = p ^ b := by
      rw [inv_pow]
      field_simp
    _ = p ^ (b - a) * p ^ a := by rw [← pow_add, Nat.sub_add_cancel hab]

lemma reciprocal_factor (p : K) (hp : p ≠ 0) (m : ℕ) :
    (1 - (p⁻¹) ^ m) * p ^ m = -(1 - p ^ m) := by
  rw [inv_pow]
  field_simp
  <;> ring

/-- Reversal of an entire finite q-factorial, with the exact triangular shift. -/
theorem qPochhammer_reciprocal (p : K) (hp : p ≠ 0) (m : ℕ) :
    qPochhammer p⁻¹ p⁻¹ m * p ^ triangularExponent m =
      (-1 : K) ^ m * qPochhammer p p m := by
  induction m with
  | zero => simp [triangularExponent]
  | succ m ih =>
      rw [qPochhammer_succ, qPochhammer_succ, triangularExponent_succ, pow_add]
      have hi : p⁻¹ * (p⁻¹) ^ m = (p⁻¹) ^ (m + 1) := by rw [pow_succ'];
      have hi' : p * p ^ m = p ^ (m + 1) := by rw [pow_succ'];
      rw [hi, hi']
      calc
        _ = (qPochhammer p⁻¹ p⁻¹ m * p ^ triangularExponent m) *
          ((1 - (p⁻¹) ^ (m + 1)) * p ^ (m + 1)) := by ring
        _ = ((-1 : K) ^ m * qPochhammer p p m) * -(1 - p ^ (m + 1)) := by
          rw [ih, reciprocal_factor p hp]
        _ = _ := by rw [pow_succ]; ring

lemma qPochhammer_reciprocal_div (p : K) (hp : p ≠ 0) (m : ℕ) :
    qPochhammer p⁻¹ p⁻¹ m =
      (-1 : K) ^ m * qPochhammer p p m / p ^ triangularExponent m := by
  apply (eq_div_iff (pow_ne_zero _ hp)).mpr
  exact qPochhammer_reciprocal p hp m

lemma qPochhammerFinite_eq (q z : ℝ) (m : ℕ) :
    PaperR10.qPochhammerFinite z q m = qPochhammer q z m := by
  exact (finite_qPochhammer_product q z m).symm

lemma qPochhammer_q_nonzero {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    qPochhammer q q m ≠ 0 := by
  rw [← qPochhammerFinite_eq]
  exact (PaperR10.qPochhammerFinite_pos hq0.le hq1 hq0.le hq1.le m).ne'

lemma qPochhammer_large_base_nonzero {p : ℝ} (hp : 1 < p) (m : ℕ) :
    qPochhammer p p m ≠ 0 := by
  rw [finite_qPochhammer_product]
  apply prod_ne_zero_iff.mpr
  intro i hi
  have hbase : p ≤ p ^ (i + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hp.le (show 1 ≤ i + 1 by omega)
  have hpow : 1 < p ^ (i + 1) := hp.trans_le hbase
  rw [← pow_succ']
  exact sub_ne_zero.mpr (ne_of_lt hpow)

/-- Reflecting a finite interval removes all reciprocal powers. -/
theorem reflected_numerator_product (p : K) (hp : p ≠ 0) (u r : ℕ) :
    (∏ i ∈ range r, (1 - (p⁻¹) ^ (i + 1) * p ^ (u + r))) =
      qPochhammer p (p ^ u) r := by
  rw [finite_qPochhammer_product]
  calc
    _ = ∏ i ∈ range r, (1 - p ^ u * p ^ (r - 1 - i)) := by
      apply prod_congr rfl
      intro i hi
      have hir := mem_range.mp hi
      rw [inverse_power_mul_power p hp (by omega)]
      rw [← pow_add]
      congr 2
      omega
    _ = _ := prod_range_reflect (fun i => 1 - p ^ u * p ^ i) r

/-- The erased denominator at a pole splits into its left and right factors.
Both sides of the pole are retained, including the cases s=0 and s=L. -/
theorem erased_geometric_pole_product (p : K) (hp : p ≠ 0)
    (a L s : ℕ) (hs : s ≤ L) :
    (∏ j ∈ (range (L + 1)).erase s,
      (1 - (p⁻¹) ^ (a + j) * p ^ (a + s))) =
        qPochhammer p p s * qPochhammer p⁻¹ p⁻¹ (L - s) := by
  have hset : (range (L + 1)).erase s =
      range s ∪ ((range (L - s)).image (fun j => s + 1 + j)) := by
    ext j
    simp only [mem_erase, mem_range, mem_union, mem_image]
    constructor
    · intro hj
      by_cases hjs : j < s
      · exact Or.inl hjs
      · right
        refine ⟨j - (s + 1), by omega, by omega⟩
    · rintro (hj | ⟨k, hk, rfl⟩) <;> omega
  have hdis : Disjoint (range s) ((range (L - s)).image (fun j => s + 1 + j)) := by
    apply disjoint_left.mpr
    intro j hj hj'
    rcases mem_image.mp hj' with ⟨k, hk, rfl⟩
    have := mem_range.mp hj
    omega
  rw [hset, prod_union hdis, prod_image]
  · have hleft : (∏ j ∈ range s, (1 - (p⁻¹) ^ (a + j) * p ^ (a + s))) =
        qPochhammer p p s := by
      rw [finite_qPochhammer_product]
      calc
        _ = ∏ j ∈ range s, (1 - p * p ^ (s - 1 - j)) := by
          apply prod_congr rfl
          intro j hj
          have hjs := mem_range.mp hj
          rw [inverse_power_mul_power p hp (by omega), ← pow_succ']
          congr 2
          omega
        _ = _ := prod_range_reflect (fun j => 1 - p * p ^ j) s
    rw [hleft]
    congr 1
    rw [finite_qPochhammer_product]
    apply prod_congr rfl
    intro j hj
    have he : a + (s + 1 + j) = (a + s) + (j + 1) := by omega
    rw [he, pow_add]
    have hc : (p⁻¹) ^ (a + s) * p ^ (a + s) = 1 := by
      simpa using inverse_power_mul_power p hp (le_refl (a + s))
    have hh : (p⁻¹) ^ (a + s) * (p⁻¹) ^ (j + 1) * p ^ (a + s) =
        (p⁻¹) ^ (j + 1) := by
      calc
        _ = ((p⁻¹) ^ (a + s) * p ^ (a + s)) * (p⁻¹) ^ (j + 1) := by ring
        _ = _ := by rw [hc, one_mul]
    rw [hh, pow_succ']
  · intro i hi j hj hij
    have hij' : s + 1 + i = s + 1 + j := hij
    omega

end ErdosProblems.Erdos1049.PaperR14
