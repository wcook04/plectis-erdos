import ErdosProblems.Erdos257.PaperCompleteR8.FiniteAtomicMajorants
import ErdosProblems.Erdos257.PaperCompleteR8.DivisorCubeIncidence
import ErdosProblems.Erdos257.PaperCompleteR8.DivisorFrameWeightedBudget
import Mathlib.Data.Nat.Squarefree
import Mathlib

/-!
# Exact fractional divisor-cube identities
The multiplier q need not be coprime to the squarefree prime product.
No independent-Bernoulli distribution is assumed. All means are finite counts.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset

def primeReciprocalMass (P : Finset ℕ) : ℝ := ∑ p ∈ P, (1 : ℝ) / p

def cubeProductCost (q : ℕ) (P : Finset ℕ) (z : ℝ) : ℝ :=
  (1 / (q : ℝ)) * ∏ p ∈ P, (1 + z / (p : ℝ))

def cubeCoefficient (q : ℕ) (P : Finset ℕ) (z : ℝ) : ℕ → ℝ :=
  finiteAtomicCoefficient P.powerset (fun T => q * T.prod id) (fun T => z ^ T.card)

theorem prime_product_pos (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    0 < P.prod id := Finset.prod_pos (fun p hp => (hP p hp).pos)

theorem squarefree_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Squarefree (P.prod id) := by
  classical
  revert hP
  induction P using Finset.induction_on with
  | empty => intro hP; simpa using (squarefree_one : Squarefree (1 : ℕ))
  | @insert p P hpP ih =>
    intro hP
    have hp := hP p (mem_insert_self _ _)
    have hPs : ∀ r ∈ P, Nat.Prime r := fun r hr => hP r (mem_insert_of_mem hr)
    have hc : p.Coprime (P.prod id) := Nat.Coprime.prod_right (fun r hr =>
      (hp.coprime_iff_not_dvd).mpr (fun hpr =>
        hpP ((((Nat.dvd_prime (hPs r hr)).mp hpr).resolve_left hp.ne_one).symm ▸ hr)))
    rw [Finset.prod_insert hpP]
    exact (Nat.squarefree_mul hc).mpr ⟨hp.squarefree, ih hPs⟩

/-- Every divisor is the product of a unique subset of the prime set. -/
theorem prime_product_divisors_eq_powerset (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    (P.prod id).divisors = P.powerset.image (fun T => T.prod id) := by
  classical
  ext d
  constructor
  · intro hd
    have hdM := Nat.dvd_of_mem_divisors hd
    have hdSq : Squarefree d := (squarefree_prime_product P hP).squarefree_of_dvd hdM
    have hsub : d.primeFactors ⊆ P := by
      intro p hp
      have hpD := Nat.mem_primeFactors.mp hp
      have hpM : p ∈ (P.prod id).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpD.1, hpD.2.1.trans hdM, (prime_product_pos P hP).ne'⟩
      change p ∈ (∏ r ∈ P, r).primeFactors at hpM
      rwa [Nat.primeFactors_prod hP] at hpM
    exact mem_image.mpr ⟨d.primeFactors, mem_powerset.mpr hsub,
      Nat.prod_primeFactors_of_squarefree hdSq⟩
  · rintro hd
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨Finset.prod_dvd_prod_of_subset _ _ _ (mem_powerset.mp hT),
      (prime_product_pos P hP).ne'⟩

theorem divisorCube_eq_powerset_image (q : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    divisorCube q P = P.powerset.image (fun T => q * T.prod id) := by
  classical
  rw [divisorCube, prime_product_divisors_eq_powerset P hP, Finset.image_image]
  rfl

/-- Divisibility by a squarefree subset product is exactly the collection
of its prime-coordinate divisibilities, after cancelling q. -/
theorem cube_subset_dvd_iff (q : ℕ) (P T : Finset ℕ) (n : ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hTP : T ⊆ P)
    (hn : 0 < n) (hqn : q ∣ n) :
    q * T.prod id ∣ n ↔ ∀ p ∈ T, q * p ∣ n := by
  constructor
  · intro h p hp
    have hpT : p ∣ T.prod id := Finset.dvd_prod_of_mem id hp
    exact (Nat.mul_dvd_mul_left q hpT).trans h
  · intro h
    obtain ⟨m, rfl⟩ := hqn
    have hm0 : m ≠ 0 := by intro hm; simp [hm] at hn
    have hTm : T ⊆ m.primeFactors := by
      intro p hp
      obtain ⟨v, hv⟩ := h p hp
      have hm : m = p * v := Nat.eq_of_mul_eq_mul_left hq (by simpa [mul_assoc] using hv)
      exact Nat.mem_primeFactors.mpr ⟨hP p (hTP hp), ⟨v, hm⟩, hm0⟩
    exact Nat.mul_dvd_mul_left q
      ((Finset.prod_dvd_prod_of_subset _ _ _ hTm).trans (Nat.prod_primeFactors_dvd m))

theorem cube_incidence_exact (q : ℕ) (P : Finset ℕ) (n : ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hn : 0 < n) (hqn : q ∣ n) :
    ((divisorCube q P).filter (fun a => a ∣ n)).card = 2 ^ cubePrimeRank q P n := by
  classical
  let B := P.filter (fun p => q * p ∣ n)
  have hBP : B ⊆ P := Finset.filter_subset _ _
  have heq : (divisorCube q P).filter (fun a => a ∣ n) =
      B.powerset.image (fun T => q * T.prod id) := by
    rw [divisorCube_eq_powerset_image q P hP]
    ext a
    constructor
    · intro ha
      obtain ⟨haI, had⟩ := mem_filter.mp ha
      obtain ⟨T, hT, rfl⟩ := mem_image.mp haI
      have hTP := mem_powerset.mp hT
      have hd := (cube_subset_dvd_iff q P T n hq hP hTP hn hqn).mp had
      exact mem_image.mpr ⟨T, mem_powerset.mpr
        (fun p hp => mem_filter.mpr ⟨hTP hp, hd p hp⟩), rfl⟩
    · intro ha
      obtain ⟨T, hT, rfl⟩ := mem_image.mp ha
      have hTB := mem_powerset.mp hT
      have hTP := hTB.trans hBP
      refine mem_filter.mpr ⟨mem_image.mpr ⟨T, mem_powerset.mpr hTP, rfl⟩, ?_⟩
      exact (cube_subset_dvd_iff q P T n hq hP hTP hn hqn).mpr
        (fun p hp => (mem_filter.mp (hTB hp)).2)
  rw [heq, Finset.card_image_of_injOn, Finset.card_powerset]
  · rfl
  · exact prime_subset_product_injective B (fun p hp => hP p (hBP hp)) q hq

theorem cube_incidence_zero (q : ℕ) (P : Finset ℕ) (n : ℕ) (hqn : ¬ q ∣ n) :
    ((divisorCube q P).filter (fun a => a ∣ n)).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨haF, han⟩ := mem_filter.mp ha
  obtain ⟨d, hd, rfl⟩ := mem_image.mp haF
  exact hqn ((dvd_mul_right q d).trans han)

/-- Restricted subset sums are the appropriate coordinate product. -/
theorem sum_subset_powers (P B : Finset ℕ) (hBP : B ⊆ P) (z : ℝ) :
    (∑ T ∈ P.powerset, if T ⊆ B then z ^ T.card else 0) = (1 + z) ^ B.card := by
  classical
  have heq : P.powerset.filter (fun T => T ⊆ B) = B.powerset := by
    ext T
    simp only [mem_filter, mem_powerset]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.trans hBP, h⟩
  rw [← Finset.sum_filter, heq]
  have h := Finset.prod_one_add (f := fun _ : ℕ => z) B
  simpa only [Finset.prod_const] using h.symm

/-- Exact positive fractional incidence expansion, including the off-q case. -/
theorem cube_fractional_expansion (q : ℕ) (P : Finset ℕ) (α : ℝ) (n : ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hα : 0 < α) (hn : 0 < n) :
    (((divisorCube q P).filter (fun a => a ∣ n)).card : ℝ) ^ α =
      ∑ d ∈ n.divisors, cubeCoefficient q P ((2 : ℝ) ^ α - 1) d := by
  classical
  rw [cubeCoefficient, finiteAtomicCoefficient_divisor_sum _ _ _ n hn]
  by_cases hqn : q ∣ n
  · rw [cube_incidence_exact q P n hq hP hn hqn]
    let B := P.filter (fun p => q * p ∣ n)
    have hBP : B ⊆ P := Finset.filter_subset _ _
    have heq : (∑ T ∈ P.powerset,
        if q * T.prod id ∣ n then ((2 : ℝ) ^ α - 1) ^ T.card else 0) =
        ∑ T ∈ P.powerset, if T ⊆ B then ((2 : ℝ) ^ α - 1) ^ T.card else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      have hTP := mem_powerset.mp hT
      have hi : q * T.prod id ∣ n ↔ T ⊆ B := by
        rw [cube_subset_dvd_iff q P T n hq hP hTP hn hqn]
        constructor
        · intro h p hp; exact mem_filter.mpr ⟨hTP hp, h p hp⟩
        · intro h p hp; exact (mem_filter.mp (h hp)).2
      simp only [hi]
    rw [heq, sum_subset_powers P B hBP]
    have hc : cubePrimeRank q P n = B.card := rfl
    rw [hc]
    push_cast
    rw [show (1 : ℝ) + ((2 : ℝ) ^ α - 1) = (2 : ℝ) ^ α by ring]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  · rw [cube_incidence_zero q P n hqn]
    simp only [Nat.cast_zero, Real.zero_rpow hα.ne']
    symm
    apply Finset.sum_eq_zero
    intro T hT
    exact if_neg (fun h => hqn ((dvd_mul_right q (T.prod id)).trans h))

/-- Exact cost of the canonical finite majorant. -/
theorem cubeCoefficient_cost (q : ℕ) (P : Finset ℕ) (z : ℝ) :
    (∑' d : ℕ, cubeCoefficient q P z d / (d : ℝ)) = cubeProductCost q P z := by
  classical
  rw [cubeCoefficient, finiteAtomicCoefficient_cost, cubeProductCost, Finset.prod_one_add,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.prod_div_distrib, Finset.prod_const]
  simp only [Nat.cast_mul, Nat.cast_prod, id_eq]
  ring

/-- All finite-cube data required by the infimum theorem are constructed. -/
def cubeCoverFrame (q : ℕ) (P : Finset ℕ) (α : ℝ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hα : 0 < α) (hα1 : α ≤ 1) :
    FiniteCoverFrame where
  support := divisorCube q P
  exponent := α
  coefficient := cubeCoefficient q P ((2 : ℝ) ^ α - 1)
  positive := by
    intro h
    obtain ⟨d, hd, heq⟩ := mem_image.mp h
    have hdpos := Nat.pos_of_mem_divisors hd
    exact (Nat.mul_pos hq hdpos).ne' heq
  exponent_pos := hα
  exponent_le_one := hα1
  coefficient_nonneg := fun d _ => finiteAtomicCoefficient_nonneg _ _ _
    (fun T _ => pow_nonneg (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hα)).le _) d
  column_summable := finiteAtomicCoefficient_column_summable _ _ _
  majorises := fun n hn => (cube_fractional_expansion q P α n hq hP hα hn).le

theorem cubeCoverFrame_cost (q : ℕ) (P : Finset ℕ) (α : ℝ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hα : 0 < α) (hα1 : α ≤ 1) :
    (cubeCoverFrame q P α hq hP hα hα1).cost =
      cubeProductCost q P ((2 : ℝ) ^ α - 1) := cubeCoefficient_cost q P _

/-- Finite prime products, including the empty prime set. -/
theorem cubeProductCost_le_exp (q : ℕ) (P : Finset ℕ) (z : ℝ) (hz : 0 ≤ z) :
    cubeProductCost q P z ≤ Real.exp (z * primeReciprocalMass P) / (q : ℝ) := by
  have hprod : (∏ p ∈ P, (1 + z / (p : ℝ))) ≤
      ∏ p ∈ P, Real.exp (z / (p : ℝ)) := by
    apply Finset.prod_le_prod
    · intro p hp; positivity
    · intro p hp; simpa [add_comm] using Real.add_one_le_exp (z / (p : ℝ))
  have hexp : (∏ p ∈ P, Real.exp (z / (p : ℝ))) =
      Real.exp (z * primeReciprocalMass P) := by
    rw [← Real.exp_sum]
    congr 1
    unfold primeReciprocalMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have h := mul_le_mul_of_nonneg_left (hprod.trans_eq hexp)
    (one_div_nonneg.mpr (Nat.cast_nonneg q))
  simpa [cubeProductCost, div_eq_mul_inv, mul_comm] using h

/-- The complete-period fractional moment equals the canonical cost. -/
theorem cube_fractional_mean (q : ℕ) (P : Finset ℕ) (α : ℝ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hα : 0 < α) :
    (∑ n ∈ Icc 1 (q * P.prod id),
      (((divisorCube q P).filter (fun a => a ∣ n)).card : ℝ) ^ α) /
        (q * P.prod id : ℕ) = cubeProductCost q P ((2 : ℝ) ^ α - 1) := by
  classical
  have hX : 0 < q * P.prod id := Nat.mul_pos hq (prime_product_pos P hP)
  have heq : (∑ n ∈ Icc 1 (q * P.prod id),
      (((divisorCube q P).filter (fun a => a ∣ n)).card : ℝ) ^ α) =
      ∑ n ∈ Icc 1 (q * P.prod id), ∑ T ∈ P.powerset,
        if q * T.prod id ∣ n then ((2 : ℝ) ^ α - 1) ^ T.card else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [cube_fractional_expansion q P α n hq hP hα (mem_Icc.mp hn).1,
      cubeCoefficient, finiteAtomicCoefficient_divisor_sum _ _ _ n (mem_Icc.mp hn).1]
  rw [heq, mean_finite_divisor_atoms]
  · exact (finiteAtomicCoefficient_cost _ _ _).symm.trans (cubeCoefficient_cost q P _)
  · exact hX
  · intro T hT
    exact Nat.mul_pos hq (prime_product_pos T (fun p hp => hP p (mem_powerset.mp hT hp)))
  · intro T hT
    exact Nat.mul_dvd_mul_left q (Finset.prod_dvd_prod_of_subset _ _ _ (mem_powerset.mp hT))

end ErdosProblems.Erdos257.PaperCompleteR8
end
