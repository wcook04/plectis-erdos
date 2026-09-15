import ErdosProblems.Erdos1049.QBinomialUnitIdentity
import Mathlib

/-! # The missing free-variable finite source transform
The variable z is independent of q.
Consequently the identity can be specialised in any commutative ring,
including a Laurent polynomial ring; it is not limited to z=q^alpha with
alpha a natural number. The proof uses only two finite q-binomial expansions.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Finset
open scoped BigOperators
variable {R : Type*} [CommRing R]

/-- The literal inner sum with an independent generating variable. -/
def sourceInnerZ (q z : R) (a d v : ℕ) : R :=
  ∑ j ∈ range v,
    (-1 : R) ^ j * q ^ j.choose 2 * z ^ j *
      gaussBinom q (v - 1) j * gaussBinom q (a + d + j - 1) (a - 1)

set_option maxHeartbeats 500000 in
/-- The free-variable finite identity needed for the negative-shift B channel. -/
theorem sourceInnerZ_qPochhammer (q z : R) {a d v : ℕ}
    (ha : 1 ≤ a) (hv : 1 ≤ v) :
    qPochhammer q q (a - 1) * sourceInnerZ q z a d v =
      ∑ h ∈ range a,
        (-1 : R) ^ h * q ^ (h * (d + 1) + h.choose 2) *
          gaussBinom q (a - 1) h * qPochhammer q (z * q ^ h) (v - 1) := by
  unfold sourceInnerZ
  rw [mul_sum]
  have hleft :
      (∑ j ∈ range v,
        qPochhammer q q (a - 1) *
          ((-1 : R) ^ j * q ^ j.choose 2 * z ^ j *
            gaussBinom q (v - 1) j * gaussBinom q (a + d + j - 1) (a - 1))) =
      ∑ j ∈ range v,
        (-1 : R) ^ j * q ^ j.choose 2 * z ^ j * gaussBinom q (v - 1) j *
          qPochhammer q (q ^ (d + j + 1)) (a - 1) := by
    apply sum_congr rfl
    intro j hj
    have hle : a - 1 ≤ a + d + j - 1 := by omega
    have hidx : a + d + j - 1 - (a - 1) + 1 = d + j + 1 := by omega
    have hg := gaussBinom_mul_qPochhammer q hle
    rw [hidx] at hg
    rw [← hg]
    ring
  rw [hleft]
  have ha' : a - 1 + 1 = a := by omega
  have hv' : v - 1 + 1 = v := by omega
  have hexpand :
      (∑ j ∈ range v,
        (-1 : R) ^ j * q ^ j.choose 2 * z ^ j * gaussBinom q (v - 1) j *
          qPochhammer q (q ^ (d + j + 1)) (a - 1)) =
      ∑ j ∈ range v, ∑ h ∈ range a,
        (-1 : R) ^ j * q ^ j.choose 2 * z ^ j * gaussBinom q (v - 1) j *
          qBinomialTerm q (q ^ (d + j + 1)) (a - 1) h := by
    apply sum_congr rfl
    intro j hj
    rw [qPochhammer_eq_sum, ha', mul_sum]
  rw [hexpand, Finset.sum_comm]
  apply sum_congr rfl
  intro h hh
  have hterm (j : ℕ) :
      (-1 : R) ^ j * q ^ j.choose 2 * z ^ j * gaussBinom q (v - 1) j *
          qBinomialTerm q (q ^ (d + j + 1)) (a - 1) h =
      ((-1 : R) ^ h * q ^ (h * (d + 1) + h.choose 2) * gaussBinom q (a - 1) h) *
        qBinomialTerm q (z * q ^ h) (v - 1) j := by
    simp only [qBinomialTerm, pow_add, pow_mul, mul_pow, pow_one]
    ring
  simp_rw [hterm]
  rw [← mul_sum]
  have hp : (∑ j ∈ range v, qBinomialTerm q (z * q ^ h) (v - 1) j) =
      qPochhammer q (z * q ^ h) (v - 1) := by
    simpa only [hv'] using (qPochhammer_eq_sum q (z * q ^ h) (v - 1)).symm
  rw [hp]

/-- Recovery of the supplied nonnegative-power version, with no new premise. -/
theorem sourceInnerZ_power (q : R) (a d v α : ℕ) :
    sourceInnerZ q (q ^ α) a d v = sourceInnerT q a d v α := by
  unfold sourceInnerZ sourceInnerT
  apply sum_congr rfl
  intro j hj
  simp only [pow_mul, pow_add]
  ring

/-- The precise polynomial identity at the actual source indices. -/
theorem actual_source_free_variable_transform (q z : R) (n : ℕ) :
    qPochhammer q q (12 * n) * sourceInnerZ q z (12 * n + 1) (2 * n) (13 * n + 1) =
      ∑ h ∈ range (12 * n + 1),
        (-1 : R) ^ h * q ^ (h * (2 * n + 1) + h.choose 2) *
          gaussBinom q (12 * n) h * qPochhammer q (z * q ^ h) (13 * n) := by
  simpa using sourceInnerZ_qPochhammer q z
    (a := 12 * n + 1) (d := 2 * n) (v := 13 * n + 1) (by omega) (by omega)


end ErdosProblems.Erdos1049.PaperR12
