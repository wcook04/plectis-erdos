import ErdosProblems.Erdos1049.QBinomialUnitIdentity
import Mathlib.Algebra.Polynomial.Roots
import Mathlib

/-!
# Finite simple-pole interpolation, without a partial-fractions assumption

Interpolation in the pole basis and the finite simple-pole expansion.

The numerator is reconstructed from its values at the inverse pole parameters.
The only degree premise is the ordinary proper-fraction degree condition;
there is no premise asserting the partial-fraction identity. The following
source module supplies the concrete parameters and the numerator degree.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset
open scoped BigOperators

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

noncomputable def poleProduct (b : ι → K) (s : Finset ι) : K[X] :=
  ∏ i ∈ s, (1 - C (b i) * X)

lemma poleProduct_eval (b : ι → K) (s : Finset ι) (z : K) :
    (poleProduct b s).eval z = ∏ i ∈ s, (1 - b i * z) := by
  simp [poleProduct, Polynomial.eval_prod]

lemma poleProduct_degree (b : ι → K) (s : Finset ι) :
    (poleProduct b s).natDegree ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [poleProduct]
  | @insert i s hi ih =>
      have he : poleProduct b (insert i s) =
          (1 - C (b i) * X) * poleProduct b s := by simp [poleProduct, hi]
      rw [he, card_insert_of_notMem hi]
      have hlin : (1 - C (b i) * X : K[X]).natDegree ≤ 1 := by
        apply (natDegree_sub_le _ _).trans
        apply max_le
        · simp
        · exact natDegree_mul_le.trans (by simp)
      exact natDegree_mul_le.trans (by omega)

lemma poleProduct_erase_eval_ne_zero (b : ι → K) (s : Finset ι) (i : ι)
    (hi : i ∈ s) (hb0 : ∀ j ∈ s, b j ≠ 0)
    (hb : Set.InjOn b s) :
    (poleProduct b (s.erase i)).eval (b i)⁻¹ ≠ 0 := by
  rw [poleProduct_eval]
  apply prod_ne_zero_iff.mpr
  intro j hj
  obtain ⟨hji, hjs⟩ := mem_erase.mp hj
  intro hz
  have he : b j * (b i)⁻¹ = 1 := (sub_eq_zero.mp hz).symm
  have he' : b j = b i := by
    have hh := congrArg (fun x : K => x * b i) he
    simpa [hb0 i hi, mul_assoc] using hh
  exact hji (hb hjs hi he')

noncomputable def poleResidue (P : K[X]) (b : ι → K) (s : Finset ι) (i : ι) : K :=
  P.eval (b i)⁻¹ / (poleProduct b (s.erase i)).eval (b i)⁻¹

noncomputable def poleInterpolant (P : K[X]) (b : ι → K) (s : Finset ι) : K[X] :=
  ∑ i ∈ s, C (poleResidue P b s i) * poleProduct b (s.erase i)

lemma poleInterpolant_eval_node (P : K[X]) (b : ι → K) (s : Finset ι)
    (i : ι) (hi : i ∈ s) (hb0 : ∀ j ∈ s, b j ≠ 0) (hb : Set.InjOn b s) :
    (poleInterpolant P b s).eval (b i)⁻¹ = P.eval (b i)⁻¹ := by
  classical
  unfold poleInterpolant
  rw [eval_finset_sum]
  rw [sum_eq_single i]
  · simp only [eval_mul, eval_C, poleResidue]
    exact div_mul_cancel₀ _ (poleProduct_erase_eval_ne_zero b s i hi hb0 hb)
  · intro j hj hji
    have him : i ∈ s.erase j := mem_erase.mpr ⟨Ne.symm hji, hi⟩
    have hz : (poleProduct b (s.erase j)).eval (b i)⁻¹ = 0 := by
      rw [poleProduct_eval]
      apply prod_eq_zero him
      simp [hb0 i hi]
    simp [hz]
  · exact fun hn => (hn hi).elim

lemma poleInterpolant_degree (P : K[X]) (b : ι → K) (s : Finset ι) :
    (poleInterpolant P b s).natDegree ≤ s.card - 1 := by
  classical
  unfold poleInterpolant
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply natDegree_mul_le.trans
  have hd := poleProduct_degree b (s.erase i)
  have hc : (s.erase i).card = s.card - 1 := card_erase_of_mem hi
  simpa only [natDegree_C, zero_add, hc] using hd

/-- A division-free interpolation theorem for the simple pole basis. -/
theorem pole_interpolation (P : K[X]) (b : ι → K) (s : Finset ι)
    (hdeg : P.natDegree < s.card) (hb0 : ∀ i ∈ s, b i ≠ 0)
    (hb : Set.InjOn b s) :
    P = poleInterpolant P b s := by
  classical
  apply eq_of_natDegree_lt_card_of_eval_eq P (poleInterpolant P b s)
    (f := fun i : s => (b i)⁻¹)
  · intro i j he
    apply Subtype.ext
    apply hb i.property j.property
    exact inv_injective he
  · intro i
    exact (poleInterpolant_eval_node P b s i i.property hb0 hb).symm
  · rw [Fintype.card_coe]
    have hd := poleInterpolant_degree P b s
    exact max_lt hdeg (by omega)

/-- The actual rational identity follows from the polynomial identity; every
pole denominator is required nonzero at the evaluation point, as it must be. -/
theorem simple_pole_expansion (P : K[X]) (b : ι → K) (s : Finset ι)
    (hdeg : P.natDegree < s.card) (hb0 : ∀ i ∈ s, b i ≠ 0)
    (hb : Set.InjOn b s) (z : K) (hz : ∀ i ∈ s, 1 - b i * z ≠ 0) :
    P.eval z / (poleProduct b s).eval z =
      ∑ i ∈ s, poleResidue P b s i / (1 - b i * z) := by
  have hD : (poleProduct b s).eval z ≠ 0 := by
    rw [poleProduct_eval]
    exact prod_ne_zero_iff.mpr hz
  have he := congrArg (Polynomial.eval z) (pole_interpolation P b s hdeg hb0 hb)
  rw [poleInterpolant, eval_finset_sum] at he
  rw [he, sum_div]
  apply sum_congr rfl
  intro i hi
  have hfactor : (poleProduct b s).eval z =
      (1 - b i * z) * (poleProduct b (s.erase i)).eval z := by
    simp only [poleProduct_eval]
    exact (mul_prod_erase s (fun j => 1 - b j * z) hi).symm
  have hE : (poleProduct b (s.erase i)).eval z ≠ 0 := by
    intro hh
    rw [hfactor, hh, mul_zero] at hD
    exact hD rfl
  simp only [eval_mul, eval_C]
  rw [hfactor]
  exact mul_div_mul_right _ _ hE

lemma finite_qPochhammer_product {R : Type*} [CommRing R] (q z : R) (m : ℕ) :
    qPochhammer q z m = ∏ i ∈ range m, (1 - z * q ^ i) := by
  induction m with
  | zero => simp
  | succ m ih => rw [qPochhammer_succ, prod_range_succ, ih]

end ErdosProblems.Erdos1049.PaperR14
