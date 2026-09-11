import ErdosProblems.Erdos1041.TetranomialProductSensitiveSelector

/-!
# Erdős #1041: a tail-resultant bonus for the tetranomial selector

The threshold `card S - 1` in the two-safe-tail L2 argument can be raised when
the product of all tail energies is retained.  When that product is at most
one, a family with at most one entry below one has energy at least

`card S - 1 + product`.

This sharp form is supplemented below by a more general, weaker common-bound
variant valid without the product-at-most-one hypothesis.

For tetranomial tails `c + b * w_i^s`, their product is the resultant of the
polynomial and `b*X^s+c`.  This module kernel-checks the finite product-bonus
lemma and its signed-energy consumer.  The companion note performs the
resultant specialization and records deterministic coverage evidence.
-/

open scoped ComplexConjugate

namespace ErdosProblems.Erdos1041

/-- Squared norm commutes with a finite complex product. -/
theorem prod_normSq_eq_normSq_prod
    {ι : Type*} (S : Finset ι) (z : ι → ℂ) :
    ∏ i ∈ S, Complex.normSq (z i) = Complex.normSq (∏ i ∈ S, z i) := by
  convert prod_normSq_pow_eq_normSq_prod_pow S z 1 <;> simp

/-- Resultant-ready bridge: once the product of the tails is identified with
`R`, their real energy product is exactly `normSq R`. -/
theorem prod_tail_normSq_eq_normSq_resultant
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c R : ℂ)
    (hresultant : ∏ i ∈ S, (c + b * v i) = R) :
    ∏ i ∈ S, Complex.normSq (c + b * v i) = Complex.normSq R := by
  rw [prod_normSq_eq_normSq_prod, hresultant]

/-- If `y >= 0`, every member of `z` is at least one, and their total product
with `y` is at most one, then multiplying the large entries into `y` costs no
more than the sum of their excesses above one. -/
theorem exceptional_mul_prod_le_add_sum_sub_one
    {ι : Type*} (S : Finset ι) (z : ι → ℝ) (y : ℝ)
    (hy0 : 0 ≤ y) (hz1 : ∀ i ∈ S, 1 ≤ z i)
    (htotal : y * ∏ i ∈ S, z i ≤ 1) :
    y * ∏ i ∈ S, z i ≤ y + ∑ i ∈ S, (z i - 1) := by
  classical
  induction S using Finset.induction_on generalizing y with
  | empty => simp
  | @insert a S ha ih =>
      have hza1 : 1 ≤ z a := hz1 a (Finset.mem_insert_self _ _)
      have hza0 : 0 ≤ z a := le_trans (by norm_num) hza1
      have hprodS1 : 1 ≤ ∏ i ∈ S, z i := by
        exact Finset.one_le_prod
          (fun i hi => hz1 i (Finset.mem_insert_of_mem hi))
      have hya0 : 0 ≤ y * z a := mul_nonneg hy0 hza0
      have htotal' : (y * z a) * ∏ i ∈ S, z i ≤ 1 := by
        simpa [Finset.prod_insert ha, mul_assoc] using htotal
      have hya_le_total : y * z a ≤ (y * z a) * ∏ i ∈ S, z i :=
        le_mul_of_one_le_right hya0 hprodS1
      have hya1 : y * z a ≤ 1 := le_trans hya_le_total htotal'
      have hy_le_hya : y ≤ y * z a := le_mul_of_one_le_right hy0 hza1
      have hy1 : y ≤ 1 := le_trans hy_le_hya hya1
      have hpair : y * z a ≤ y + (z a - 1) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hza1) (sub_nonneg.mpr hy1)]
      have hih := ih (y * z a) hya0
        (fun i hi => hz1 i (Finset.mem_insert_of_mem hi)) htotal'
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      nlinarith

/-- Sharp two-small-entry principle when the total product is at most one:
energy below `card S - 1 + product` forces two distinct entries below one. -/
theorem exists_two_lt_one_of_product_le_one_and_sum_lt_card_sub_one_add_prod
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hcard : 2 ≤ S.card) (hx0 : ∀ i ∈ S, 0 ≤ x i)
    (hprodle : ∏ i ∈ S, x i ≤ 1)
    (hsum : ∑ i ∈ S, x i < (S.card : ℝ) - 1 + ∏ i ∈ S, x i) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ x i < 1 ∧ x j < 1 := by
  classical
  by_contra htwo
  let T := S.filter fun i => x i < 1
  have hTcard : T.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro i j hi hj
    have hi' : i ∈ S ∧ x i < 1 := by simpa [T] using hi
    have hj' : j ∈ S ∧ x j < 1 := by simpa [T] using hj
    by_contra hij
    exact htwo ⟨i, hi'.1, j, hj'.1, hij, hi'.2, hj'.2⟩
  have hSne : S.Nonempty := Finset.nonempty_of_ne_empty (by
    intro hS
    subst S
    simp at hcard)
  have himpossible (i : ι) (hiS : i ∈ S)
      (herase : ∀ j ∈ S.erase i, 1 ≤ x j) : False := by
    have hprodFactor : ∏ j ∈ S, x j = x i * ∏ j ∈ S.erase i, x j := by
      rw [mul_comm]
      exact (Finset.prod_erase_mul S x hiS).symm
    have hcore : x i * ∏ j ∈ S.erase i, x j ≤
        x i + ∑ j ∈ S.erase i, (x j - 1) := by
      apply exceptional_mul_prod_le_add_sum_sub_one
      · exact hx0 i hiS
      · exact herase
      · rw [← hprodFactor]
        exact hprodle
    have hsumDev : ∑ j ∈ S.erase i, (x j - 1) =
        ∑ j ∈ S.erase i, x j - ((S.erase i).card : ℝ) := by
      simp [Finset.sum_sub_distrib]
    have hsumFactor : ∑ j ∈ S, x j = ∑ j ∈ S.erase i, x j + x i :=
      (Finset.sum_erase_add _ _ hiS).symm
    have hcardErase : ((S.erase i).card : ℝ) = (S.card : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hiS,
        Nat.cast_sub (by omega : 1 ≤ S.card)]
      norm_num
    rw [hsumFactor, hprodFactor] at hsum
    rw [hsumDev, hcardErase] at hcore
    linarith
  by_cases hTne : T.Nonempty
  · obtain ⟨i, hiT⟩ := hTne
    have hi' : i ∈ S ∧ x i < 1 := by simpa [T] using hiT
    apply himpossible i hi'.1
    intro j hjErase
    by_contra hj
    have hjlt : x j < 1 := lt_of_not_ge hj
    have hjT : j ∈ T := by
      simp only [T, Finset.mem_filter]
      exact ⟨Finset.mem_of_mem_erase hjErase, hjlt⟩
    have hji : j = i := (Finset.card_le_one_iff.mp hTcard) hjT hiT
    exact (Finset.mem_erase.mp hjErase).1 hji
  · obtain ⟨i, hiS⟩ := hSne
    apply himpossible i hiS
    intro j hjErase
    by_contra hj
    have hjT : j ∈ T := by
      simp only [T, Finset.mem_filter]
      exact ⟨Finset.mem_of_mem_erase hjErase, lt_of_not_ge hj⟩
    exact hTne ⟨j, hjT⟩

/-- A product bonus sharpens the two-small-entry pigeonhole principle.  The
parameter `bonus` may be any certified lower bound for
`product / M^(card S - 1)`; division is avoided in the formal statement. -/
theorem exists_two_lt_one_of_sum_lt_card_sub_one_add_product_bonus
    {ι : Type*} (S : Finset ι) (x : ι → ℝ) (M bonus : ℝ)
    (hcard : 2 ≤ S.card)
    (hx0 : ∀ i ∈ S, 0 ≤ x i) (hxM : ∀ i ∈ S, x i ≤ M)
    (hM : 1 ≤ M)
    (hproduct : bonus * M ^ (S.card - 1) ≤ ∏ i ∈ S, x i)
    (hsum : ∑ i ∈ S, x i < (S.card : ℝ) - 1 + bonus) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ x i < 1 ∧ x j < 1 := by
  classical
  by_contra htwo
  let T := S.filter fun i => x i < 1
  have hTcard : T.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro i j hi hj
    have hi' : i ∈ S ∧ x i < 1 := by simpa [T] using hi
    have hj' : j ∈ S ∧ x j < 1 := by simpa [T] using hj
    by_contra hij
    exact htwo ⟨i, hi'.1, j, hj'.1, hij, hi'.2, hj'.2⟩
  have hSne : S.Nonempty := Finset.nonempty_of_ne_empty (by
    intro hS
    subst S
    simp at hcard)
  have himpossible (i : ι) (hiS : i ∈ S)
      (herase : ∀ j ∈ S.erase i, 1 ≤ x j) : False := by
    have hsumErase : ((S.erase i).card : ℝ) ≤ ∑ j ∈ S.erase i, x j := by
      calc
        ((S.erase i).card : ℝ) = ∑ _j ∈ S.erase i, (1 : ℝ) := by simp
        _ ≤ ∑ j ∈ S.erase i, x j :=
          Finset.sum_le_sum fun j hj => herase j hj
    have hprodErase : ∏ j ∈ S.erase i, x j ≤ M ^ (S.erase i).card := by
      calc
        ∏ j ∈ S.erase i, x j ≤ ∏ _j ∈ S.erase i, M := by
          exact Finset.prod_le_prod
            (fun j hj => hx0 j (Finset.mem_of_mem_erase hj))
            (fun j hj => hxM j (Finset.mem_of_mem_erase hj))
        _ = M ^ (S.erase i).card := by simp
    have hcardErase : (S.erase i).card = S.card - 1 :=
      Finset.card_erase_of_mem hiS
    have hpowPos : 0 < M ^ (S.card - 1) := by
      exact pow_pos (lt_of_lt_of_le Real.zero_lt_one hM) _
    have hprodFactor : ∏ j ∈ S, x j = x i * ∏ j ∈ S.erase i, x j := by
      rw [mul_comm]
      exact (Finset.prod_erase_mul S x hiS).symm
    have hprodUpper : ∏ j ∈ S, x j ≤ x i * M ^ (S.card - 1) := by
      rw [hprodFactor, ← hcardErase]
      exact mul_le_mul_of_nonneg_left hprodErase (hx0 i hiS)
    have hbonusXi : bonus ≤ x i := by
      have hmul : bonus * M ^ (S.card - 1) ≤
          x i * M ^ (S.card - 1) := le_trans hproduct hprodUpper
      exact le_of_mul_le_mul_right hmul hpowPos
    have hsumFactor : ∑ j ∈ S, x j = ∑ j ∈ S.erase i, x j + x i :=
      (Finset.sum_erase_add _ _ hiS).symm
    have hcastErase : ((S.erase i).card : ℝ) = (S.card : ℝ) - 1 := by
      rw [hcardErase, Nat.cast_sub (by omega : 1 ≤ S.card)]
      norm_num
    rw [hsumFactor] at hsum
    rw [hcastErase] at hsumErase
    linarith
  by_cases hTne : T.Nonempty
  · obtain ⟨i, hiT⟩ := hTne
    have hi' : i ∈ S ∧ x i < 1 := by simpa [T] using hiT
    apply himpossible i hi'.1
    intro j hjErase
    by_contra hj
    have hjlt : x j < 1 := lt_of_not_ge hj
    have hjT : j ∈ T := by
      simp only [T, Finset.mem_filter]
      exact ⟨Finset.mem_of_mem_erase hjErase, hjlt⟩
    have hji : j = i := (Finset.card_le_one_iff.mp hTcard) hjT hiT
    exact (Finset.mem_erase.mp hjErase).1 hji
  · obtain ⟨i, hiS⟩ := hSne
    apply himpossible i hiS
    intro j hjErase
    by_contra hj
    have hjT : j ∈ T := by
      simp only [T, Finset.mem_filter]
      exact ⟨Finset.mem_of_mem_erase hjErase, lt_of_not_ge hj⟩
    exact hTne ⟨j, hjT⟩

/-- Exact complex-tail form of the product-bonus selector. -/
theorem exists_two_tails_norm_lt_one_of_exact_L2_product_bonus
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ)
    (M bonus productTail : ℝ)
    (hcard : 2 ≤ S.card)
    (hM : 1 ≤ M)
    (htailBound : ∀ i ∈ S, Complex.normSq (c + b * v i) ≤ M)
    (htailProduct : ∏ i ∈ S, Complex.normSq (c + b * v i) = productTail)
    (hbonus : bonus * M ^ (S.card - 1) ≤ productTail)
    (hbudget :
      (S.card : ℝ) * Complex.normSq c +
          Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) +
            2 * (conj c * b * (∑ i ∈ S, v i)).re <
        (S.card : ℝ) - 1 + bonus) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      ‖c + b * v i‖ < 1 ∧ ‖c + b * v j‖ < 1 := by
  have hsum : ∑ i ∈ S, Complex.normSq (c + b * v i) <
      (S.card : ℝ) - 1 + bonus := by
    rw [sum_normSq_const_add_mul S v b c]
    exact hbudget
  obtain ⟨i, hiS, j, hjS, hij, hi, hj⟩ :=
    exists_two_lt_one_of_sum_lt_card_sub_one_add_product_bonus
      S (fun k => Complex.normSq (c + b * v k)) M bonus hcard
      (fun k hk => Complex.normSq_nonneg _) htailBound hM
      (by rw [htailProduct]; exact hbonus) hsum
  have hiNorm : ‖c + b * v i‖ < 1 := by
    rw [Complex.normSq_eq_norm_sq] at hi
    nlinarith [norm_nonneg (c + b * v i)]
  have hjNorm : ‖c + b * v j‖ < 1 := by
    rw [Complex.normSq_eq_norm_sq] at hj
    nlinarith [norm_nonneg (c + b * v j)]
  exact ⟨i, hiS, j, hjS, hij, hiNorm, hjNorm⟩

/-- Sharp exact-energy tail selector when the tail product is at most one. -/
theorem exists_two_tails_norm_lt_one_of_exact_L2_tail_product
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) (b c : ℂ)
    (tailProduct : ℝ) (hcard : 2 ≤ S.card)
    (htailProduct : ∏ i ∈ S, Complex.normSq (c + b * v i) = tailProduct)
    (htailProductLe : tailProduct ≤ 1)
    (hbudget :
      (S.card : ℝ) * Complex.normSq c +
          Complex.normSq b * ∑ i ∈ S, Complex.normSq (v i) +
            2 * (conj c * b * (∑ i ∈ S, v i)).re <
        (S.card : ℝ) - 1 + tailProduct) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      ‖c + b * v i‖ < 1 ∧ ‖c + b * v j‖ < 1 := by
  have hsum : ∑ i ∈ S, Complex.normSq (c + b * v i) <
      (S.card : ℝ) - 1 + ∏ i ∈ S, Complex.normSq (c + b * v i) := by
    rw [sum_normSq_const_add_mul S v b c, htailProduct]
    exact hbudget
  obtain ⟨i, hiS, j, hjS, hij, hi, hj⟩ :=
    exists_two_lt_one_of_product_le_one_and_sum_lt_card_sub_one_add_prod
      S (fun k => Complex.normSq (c + b * v k)) hcard
      (fun k hk => Complex.normSq_nonneg _)
      (by rw [htailProduct]; exact htailProductLe) hsum
  have hiNorm : ‖c + b * v i‖ < 1 := by
    rw [Complex.normSq_eq_norm_sq] at hi
    nlinarith [norm_nonneg (c + b * v i)]
  have hjNorm : ‖c + b * v j‖ < 1 := by
    rw [Complex.normSq_eq_norm_sq] at hj
    nlinarith [norm_nonneg (c + b * v j)]
  exact ⟨i, hiS, j, hjS, hij, hiNorm, hjNorm⟩

/-- Coefficient-upper-bound form: combine the root-product estimate for
`sum normSq(v i)` with the independent tail-product bonus. -/
theorem exists_two_tails_norm_lt_one_of_root_and_tail_product_budget
    {ι : Type*} (S : Finset ι) (v : ι → ℂ)
    (b c moment : ℂ) (rootProduct M bonus tailProduct : ℝ)
    (hcard : 2 ≤ S.card) (hmoment : ∑ i ∈ S, v i = moment)
    (hv : ∀ i ∈ S, Complex.normSq (v i) ≤ 1)
    (hrootProduct : ∏ i ∈ S, Complex.normSq (v i) = rootProduct)
    (hM : 1 ≤ M)
    (htailBound : ∀ i ∈ S, Complex.normSq (c + b * v i) ≤ M)
    (htailProduct : ∏ i ∈ S, Complex.normSq (c + b * v i) = tailProduct)
    (hbonus : bonus * M ^ (S.card - 1) ≤ tailProduct)
    (hcoeff :
      (S.card : ℝ) * Complex.normSq c +
          Complex.normSq b * ((S.card : ℝ) - 1 + rootProduct) +
            2 * (conj c * b * moment).re <
        (S.card : ℝ) - 1 + bonus) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      ‖c + b * v i‖ < 1 ∧ ‖c + b * v j‖ < 1 := by
  have hv0 : ∀ i ∈ S, 0 ≤ Complex.normSq (v i) :=
    fun i hi => Complex.normSq_nonneg _
  have hne : S.Nonempty := Finset.nonempty_of_ne_empty (by
    intro h
    subst S
    simp at hcard)
  have hsum := sum_le_card_sub_one_add_prod S
    (fun i => Complex.normSq (v i)) hv0 hv hne
  rw [hrootProduct] at hsum
  have hb0 : 0 ≤ Complex.normSq b := Complex.normSq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum hb0
  apply exists_two_tails_norm_lt_one_of_exact_L2_product_bonus
    S v b c M bonus tailProduct hcard hM htailBound
    htailProduct hbonus
  rw [hmoment]
  nlinarith

/-- Coefficient-upper-bound form of the sharp unit-tail-product selector. -/
theorem exists_two_tails_norm_lt_one_of_root_product_and_unit_tail_product
    {ι : Type*} (S : Finset ι) (v : ι → ℂ)
    (b c moment : ℂ) (rootProduct tailProduct : ℝ)
    (hcard : 2 ≤ S.card) (hmoment : ∑ i ∈ S, v i = moment)
    (hv : ∀ i ∈ S, Complex.normSq (v i) ≤ 1)
    (hrootProduct : ∏ i ∈ S, Complex.normSq (v i) = rootProduct)
    (htailProduct : ∏ i ∈ S, Complex.normSq (c + b * v i) = tailProduct)
    (htailProductLe : tailProduct ≤ 1)
    (hcoeff :
      (S.card : ℝ) * Complex.normSq c +
          Complex.normSq b * ((S.card : ℝ) - 1 + rootProduct) +
            2 * (conj c * b * moment).re <
        (S.card : ℝ) - 1 + tailProduct) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      ‖c + b * v i‖ < 1 ∧ ‖c + b * v j‖ < 1 := by
  have hv0 : ∀ i ∈ S, 0 ≤ Complex.normSq (v i) :=
    fun i hi => Complex.normSq_nonneg _
  have hne : S.Nonempty := Finset.nonempty_of_ne_empty (by
    intro h
    subst S
    simp at hcard)
  have hsum := sum_le_card_sub_one_add_prod S
    (fun i => Complex.normSq (v i)) hv0 hv hne
  rw [hrootProduct] at hsum
  have hb0 : 0 ≤ Complex.normSq b := Complex.normSq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum hb0
  apply exists_two_tails_norm_lt_one_of_exact_L2_tail_product
    S v b c tailProduct hcard htailProduct htailProductLe
  rw [hmoment]
  nlinarith

end ErdosProblems.Erdos1041
