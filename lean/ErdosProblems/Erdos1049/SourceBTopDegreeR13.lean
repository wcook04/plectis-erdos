import ErdosProblems.Erdos1049.GaussianDegreeR12
import ErdosProblems.Erdos1049.SourceBInitialR12
import Mathlib

/-!
# Exact top degree of the literal cleared B numerator



The unique leading term is the unshifted pair (s,l)=(13*n,1).
This is a finite polynomial proof: neither A*F-B=H nor Omega divisibility
is an assumption. The canonical monic quotient V is defined even before
its remainder is known to vanish; its degree is not misrepresented as
proof that this remainder vanishes.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators

lemma monic_finset_product {ι : Type*} (s : Finset ι) (p : ι → ℤ[X])
    (hp : ∀ i ∈ s, (p i).Monic) : (∏ i ∈ s, p i).Monic := by
  classical
  revert hp
  induction s using Finset.induction_on with
  | empty => intro hp; simp
  | @insert i s his ih =>
      intro hp
      rw [Finset.prod_insert his]
      exact (hp i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

lemma monic_finset_product_natDegree {ι : Type*} (s : Finset ι) (p : ι → ℤ[X])
    (hp : ∀ i ∈ s, (p i).Monic) :
    (∏ i ∈ s, p i).natDegree = ∑ i ∈ s, (p i).natDegree := by
  classical
  revert hp
  induction s using Finset.induction_on with
  | empty => intro hp; simp
  | @insert i s his ih =>
      intro hp
      have hi := hp i (Finset.mem_insert_self i s)
      have hs := monic_finset_product s p
        (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      rw [Finset.prod_insert his, Finset.sum_insert his,
        natDegree_mul' (by simp [hi.leadingCoeff, hs.leadingCoeff])]
      rw [ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))]

lemma sourceD_monic (n : ℕ) : (sourceD n).Monic := by
  unfold sourceD
  exact monic_finset_product _ _ (fun l _ => cyclotomic.monic l ℤ)

lemma sourceOmega_monic (n : ℕ) : (sourceOmega n).Monic := by
  unfold sourceOmega
  exact monic_finset_product _ _
    (fun l _ => (cyclotomic.monic l ℤ).pow _)

lemma sourceDQuotient_monic (n j : ℕ) : (sourceDQuotient n j).Monic := by
  unfold sourceDQuotient
  exact monic_finset_product _ _ (fun l _ => cyclotomic.monic l ℤ)

lemma sourceD_natDegree (n : ℕ) :
    (sourceD n).natDegree = ∑ l ∈ Finset.Icc 1 (15 * n), l.totient := by
  unfold sourceD
  rw [monic_finset_product_natDegree _ _ (fun l _ => cyclotomic.monic l ℤ)]
  simp only [natDegree_cyclotomic]

lemma sourceD_degree_split (n : ℕ) :
    (sourceD n).natDegree =
      (sourceOmega n).natDegree + (sourceComplement n).natDegree := by
  rw [sourceD_factor]
  exact natDegree_mul' (by
    simp [(sourceOmega_monic n).leadingCoeff,
      (sourceComplement_monic_degree n).1.leadingCoeff])

lemma sourceDQuotient_degree_add (n j : ℕ) (hj0 : 0 < j) (hj : j ≤ 15 * n) :
    j + (sourceDQuotient n j).natDegree = (sourceD n).natDegree := by
  have h := congrArg Polynomial.natDegree (sourceDQuotient_factor n j hj0 hj)
  have hm : (X ^ j - 1 : ℤ[X]).Monic := by
    simpa using monic_X_pow_sub_C (1 : ℤ) hj0.ne'
  rw [natDegree_mul' (by
    simp [hm.leadingCoeff, (sourceDQuotient_monic n j).leadingCoeff])] at h
  change (X ^ j - C (1 : ℤ)).natDegree + (sourceDQuotient n j).natDegree =
    (sourceD n).natDegree at h
  rw [natDegree_X_pow_sub_C] at h
  exact h

lemma sourceASummand_ne_zero (n s : ℕ) (hs : s ≤ 13 * n) :
    sourceASummand n s ≠ 0 := by
  apply leadingCoeff_ne_zero.mp
  rw [(sourceASummand_degree_and_leadingCoeff n s hs).2]
  exact pow_ne_zero _ (by norm_num)

lemma sourceShiftedASummand_ne_zero (n s j : ℕ) (hs : s ≤ 13 * n)
    (hj : j ≤ 14 * n) : sourceShiftedASummand n s j ≠ 0 := by
  intro hz
  have h := sourceShiftedASummand_factor n s j hs hj
  rw [hz, mul_zero] at h
  exact sourceASummand_ne_zero n s hs h.symm

lemma sourceShiftedASummand_degree_add (n s j : ℕ) (hs : s ≤ 13 * n)
    (hj : j ≤ 14 * n) :
    j * (2 * n + s) + (sourceShiftedASummand n s j).natDegree =
      sourceASummandDegree n s := by
  have h := congrArg Polynomial.natDegree (sourceShiftedASummand_factor n s j hs hj)
  rw [natDegree_mul' (by
      simpa only [leadingCoeff_X_pow, one_mul] using
        leadingCoeff_ne_zero.mpr (sourceShiftedASummand_ne_zero n s j hs hj)),
    natDegree_X_pow, (sourceASummand_degree_and_leadingCoeff n s hs).1] at h
  exact h

lemma sourceASummandDegree_le_K (n s : ℕ) (hs : s ≤ 13 * n) :
    sourceASummandDegree n s ≤ sourceK n := by
  rw [← sourceASummandDegree_last n]
  rcases lt_or_eq_of_le hs with hlt | rfl
  · exact (sourceASummandDegree_strict n hlt le_rfl).le
  · exact le_rfl

lemma sourceK_gt_M (n : ℕ) (hn : 1 ≤ n) : sourceM n < sourceK n := by
  rw [← sourceASummandDegree_last n]
  unfold sourceASummandDegree sourceAExponent
  have hn2 : 1 ≤ n ^ 2 := one_le_pow₀ hn
  nlinarith [Nat.zero_le ((13 * n).choose 2),
    Nat.zero_le ((n + 1) * (13 * n)), Nat.zero_le (12 * n * (2 * n + 13 * n))]

/-- Natural subtraction is justified by the positive leading index below. -/
noncomputable def sourceClearedBTop (n : ℕ) : ℕ := (sourceD n).natDegree + sourceK n - 1

lemma sourceClearedBTop_add_one (n : ℕ) (hn : 1 ≤ n) :
    sourceClearedBTop n + 1 = (sourceD n).natDegree + sourceK n := by
  have hk := sourceK_gt_M n hn
  unfold sourceClearedBTop
  omega

lemma sourceB_first_term_degree_add (n s l : ℕ) (hs : s ≤ 13 * n)
    (hl0 : 0 < l) (hl : l ≤ 15 * n) :
    (sourceASummand n s * sourceDQuotient n l).natDegree + l =
      sourceASummandDegree n s + (sourceD n).natDegree := by
  rw [natDegree_mul' (by
    simpa only [(sourceDQuotient_monic n l).leadingCoeff, mul_one] using
      leadingCoeff_ne_zero.mpr (sourceASummand_ne_zero n s hs)),
    (sourceASummand_degree_and_leadingCoeff n s hs).1]
  have h := sourceDQuotient_degree_add n l hl0 hl
  omega

lemma sourceB_first_term_le (n s l : ℕ) (hn : 1 ≤ n) (hs : s ≤ 13 * n)
    (hl0 : 0 < l) (hl : l ≤ 15 * n) :
    (sourceASummand n s * sourceDQuotient n l).natDegree ≤ sourceClearedBTop n := by
  have h := sourceB_first_term_degree_add n s l hs hl0 hl
  have hk := sourceASummandDegree_le_K n s hs
  have htop := sourceClearedBTop_add_one n hn
  omega

lemma sourceB_first_term_lt (n s l : ℕ) (hn : 1 ≤ n) (hs : s ≤ 13 * n)
    (hl0 : 0 < l) (hl : l ≤ 15 * n) (hne : s ≠ 13 * n ∨ l ≠ 1) :
    (sourceASummand n s * sourceDQuotient n l).natDegree < sourceClearedBTop n := by
  have h := sourceB_first_term_degree_add n s l hs hl0 hl
  have hk := sourceASummandDegree_le_K n s hs
  have htop := sourceClearedBTop_add_one n hn
  rcases hne with hsne | hlne
  · have hlt : sourceASummandDegree n s < sourceK n := by
      rw [← sourceASummandDegree_last n]
      exact sourceASummandDegree_strict n (by omega) le_rfl
    omega
  · omega

lemma sourceB_shifted_term_lt (n s j : ℕ) (hn : 1 ≤ n) (hs : s ≤ 13 * n)
    (hj0 : 0 < j) (hj : j ≤ 14 * n) :
    (sourceShiftedASummand n s j * sourceDQuotient n j).natDegree < sourceClearedBTop n := by
  rw [natDegree_mul' (by
    simpa only [(sourceDQuotient_monic n j).leadingCoeff, mul_one] using
      leadingCoeff_ne_zero.mpr (sourceShiftedASummand_ne_zero n s j hs hj))]
  have hshift := sourceShiftedASummand_degree_add n s j hs hj
  have hquot := sourceDQuotient_degree_add n j hj0 (by omega)
  have hk := sourceASummandDegree_le_K n s hs
  have htop := sourceClearedBTop_add_one n hn
  have hpos : 0 < j * (2 * n + s) := Nat.mul_pos hj0 (by omega)
  omega

lemma sourceB_top_term_degree_and_leadingCoeff (n : ℕ) (hn : 1 ≤ n) :
    (sourceASummand n (13 * n) * sourceDQuotient n 1).natDegree = sourceClearedBTop n ∧
    (sourceASummand n (13 * n) * sourceDQuotient n 1).leadingCoeff = (-1 : ℤ) ^ (13 * n) := by
  constructor
  · have h := sourceB_first_term_degree_add n (13 * n) 1 le_rfl (by omega) (by omega)
    rw [sourceASummandDegree_last] at h
    have htop := sourceClearedBTop_add_one n hn
    omega
  · rw [leadingCoeff_mul,
      (sourceASummand_degree_and_leadingCoeff n (13 * n) le_rfl).2,
      (sourceDQuotient_monic n 1).leadingCoeff, mul_one]

/-- Exact leading coefficient from the literal finite double sum. -/
theorem actual_cleared_B_top_coefficient (n : ℕ) (hn : 1 ≤ n) :
    (sourceClearedB n).coeff (sourceClearedBTop n) = (-1 : ℤ) ^ (13 * n) := by
  classical
  unfold sourceClearedB
  rw [finset_sum_coeff]
  rw [Finset.sum_eq_single (13 * n)]
  · rw [coeff_add, finset_sum_coeff, finset_sum_coeff]
    have hshift : (∑ j ∈ Finset.Icc 1 (14 * n),
        (sourceShiftedASummand n (13 * n) j * sourceDQuotient n j).coeff
          (sourceClearedBTop n)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact coeff_eq_zero_of_natDegree_lt (sourceB_shifted_term_lt n (13 * n) j hn
        le_rfl (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)
    rw [hshift, add_zero, Finset.sum_eq_single 1]
    · obtain ⟨hd, hc⟩ := sourceB_top_term_degree_and_leadingCoeff n hn
      rw [← hd, coeff_natDegree, hc]
    · intro l hl hne
      exact coeff_eq_zero_of_natDegree_lt (sourceB_first_term_lt n (13 * n) l hn
        le_rfl (Finset.mem_Icc.mp hl).1 (by have h := (Finset.mem_Icc.mp hl).2; omega)
        (Or.inr hne))
    · intro hnot
      exact (hnot (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)).elim
  · intro s hs hne
    have hs' : s ≤ 13 * n := by have h := Finset.mem_range.mp hs; omega
    rw [coeff_add, finset_sum_coeff, finset_sum_coeff]
    have hfirst : (∑ l ∈ Finset.Icc 1 (2 * n + s),
        (sourceASummand n s * sourceDQuotient n l).coeff (sourceClearedBTop n)) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      exact coeff_eq_zero_of_natDegree_lt (sourceB_first_term_lt n s l hn hs'
        (Finset.mem_Icc.mp hl).1 (by have h := (Finset.mem_Icc.mp hl).2; omega)
        (Or.inl hne))
    have hshift : (∑ j ∈ Finset.Icc 1 (14 * n),
        (sourceShiftedASummand n s j * sourceDQuotient n j).coeff (sourceClearedBTop n)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact coeff_eq_zero_of_natDegree_lt (sourceB_shifted_term_lt n s j hn hs'
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)
    rw [hfirst, hshift, zero_add]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim

/-- All n>=1; no source-identity or Omega-divisibility premise. -/
theorem actual_cleared_B_degree_and_leadingCoeff (n : ℕ) (hn : 1 ≤ n) :
    (sourceClearedB n).natDegree = sourceClearedBTop n ∧
    (sourceClearedB n).leadingCoeff = (-1 : ℤ) ^ (13 * n) := by
  have hb : (sourceClearedB n).natDegree ≤ sourceClearedBTop n := by
    unfold sourceClearedB
    apply polynomial_sum_natDegree_le
    intro s hs
    have hs' : s ≤ 13 * n := by have h := Finset.mem_range.mp hs; omega
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply polynomial_sum_natDegree_le
      intro l hl
      exact sourceB_first_term_le n s l hn hs' (Finset.mem_Icc.mp hl).1
        (by have h := (Finset.mem_Icc.mp hl).2; omega)
    · apply polynomial_sum_natDegree_le
      intro j hj
      exact (sourceB_shifted_term_lt n s j hn hs' (Finset.mem_Icc.mp hj).1
        (Finset.mem_Icc.mp hj).2).le
  have hc := actual_cleared_B_top_coefficient n hn
  have hd : (sourceClearedB n).natDegree = sourceClearedBTop n :=
    natDegree_eq_of_le_of_coeff_ne_zero hb (by rw [hc]; exact pow_ne_zero _ (by norm_num))
  refine ⟨hd, ?_⟩
  change (sourceClearedB n).coeff (sourceClearedB n).natDegree = _
  rw [hd, hc]

/-- Removing X^M preserves the nonzero leading coefficient. -/
theorem actual_B_without_monomial_degree_and_leadingCoeff (n : ℕ) (hn : 1 ≤ n) :
    (sourceBWithoutMonomial n).natDegree = sourceClearedBTop n - sourceM n ∧
    (sourceBWithoutMonomial n).leadingCoeff = (-1 : ℤ) ^ (13 * n) := by
  obtain ⟨hd, hc⟩ := actual_cleared_B_degree_and_leadingCoeff n hn
  have hf := actual_B_monomial_factor n
  have hb := congrArg Polynomial.natDegree hf
  rw [natDegree_mul' (by
      simpa only [leadingCoeff_X_pow, one_mul] using
        leadingCoeff_ne_zero.mpr (actual_B_without_monomial_ne_zero n hn)),
    natDegree_X_pow, hd] at hb
  constructor
  · omega
  · have hh := congrArg Polynomial.leadingCoeff hf
    rw [leadingCoeff_mul, leadingCoeff_X_pow, one_mul, hc] at hh
    exact hh.symm

/-- An actual integer polynomial, not an existential source package.
Its equality to the normalised rational B still requires its remainder to be zero. -/
noncomputable def sourceV (n : ℕ) : ℤ[X] :=
  sourceBWithoutMonomial n /ₘ sourceOmega n

noncomputable def sourceOmegaRemainder (n : ℕ) : ℤ[X] :=
  sourceBWithoutMonomial n %ₘ sourceOmega n

/-- Honest remainder-bearing division identity. -/
theorem actual_B_Omega_division (n : ℕ) :
    sourceOmegaRemainder n + sourceOmega n * sourceV n = sourceBWithoutMonomial n :=
  modByMonic_add_div _ _

theorem actual_Omega_remainder_zero_iff (n : ℕ) :
    sourceOmegaRemainder n = 0 ↔ sourceOmega n ∣ sourceBWithoutMonomial n :=
  modByMonic_eq_zero_iff_dvd (sourceOmega_monic n)

/-- Exact degree of the canonical quotient, independent of the remainder.
This cannot be used to infer that the normalisation identity holds. -/
theorem actual_V_quotient_degree (n : ℕ) (hn : 1 ≤ n) :
    (sourceV n).natDegree = (sourceU n).natDegree - 1 := by
  unfold sourceV
  rw [natDegree_divByMonic _ (sourceOmega_monic n),
    (actual_B_without_monomial_degree_and_leadingCoeff n hn).1,
    actual_U_degree]
  have hsplit := sourceD_degree_split n
  have hc := (sourceComplement_monic_degree n).2
  have hk := sourceK_gt_M n hn
  unfold sourceClearedBTop
  omega

/-- The full polynomial normalisation is equivalent to the exact outstanding
remainder assertion; it is deliberately not asserted without that proof. -/
theorem actual_B_inclusion_iff_remainder (n : ℕ) :
    sourceClearedB n = sourceOmega n * X ^ sourceM n * sourceV n ↔
      sourceOmegaRemainder n = 0 := by
  have hX : (X : ℤ[X]) ^ sourceM n ≠ 0 := pow_ne_zero _ X_ne_zero
  rw [actual_B_monomial_factor]
  have hrearr : sourceOmega n * X ^ sourceM n * sourceV n =
      X ^ sourceM n * (sourceOmega n * sourceV n) := by ring
  rw [hrearr]
  have hdiv := actual_B_Omega_division n
  constructor
  · intro h
    have hc : sourceBWithoutMonomial n = sourceOmega n * sourceV n :=
      mul_left_cancel₀ hX h
    rw [hc] at hdiv
    exact add_right_cancel (show sourceOmegaRemainder n + sourceOmega n * sourceV n =
      0 + sourceOmega n * sourceV n by simpa using hdiv)
  · intro h
    have hc : sourceBWithoutMonomial n = sourceOmega n * sourceV n := by
      simpa only [h, zero_add] using hdiv.symm
    rw [hc]

end ErdosProblems.Erdos1049.PaperR13
