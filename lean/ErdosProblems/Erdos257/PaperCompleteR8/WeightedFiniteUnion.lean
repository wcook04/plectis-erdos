import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn
import ErdosProblems.Erdos257.PaperCompleteR7.TailGluing

/-!
# The weighted class is a hereditary finite-union ideal

The prime sets are enlarged and the actual nonnegative summands are compared.
Individual irrationality or separate return times are never used as a union
supplier.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

theorem primeSetPart_dvd_of_subset {P Q : Finset ℕ} (hPQ : P ⊆ Q) (a : ℕ) :
    primeSetPart P a ∣ primeSetPart Q a := by
  unfold primeSetPart
  exact Finset.prod_dvd_prod_of_subset _ _ _ hPQ

theorem primeWeightedTerm_antitone_primeSet (b : ℕ) (hb : 2 ≤ b)
    {P Q : Finset ℕ} (hPQ : P ⊆ Q) (a : ℕ) :
    primeWeightedTerm b Q a ≤ primeWeightedTerm b P a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [primeWeightedTerm]
  have hP : 0 < primeSetPart P a := primeSetPart_pos P ha
  have hQ : 0 < primeSetPart Q a := primeSetPart_pos Q ha
  have hle : primeSetPart P a ≤ primeSetPart Q a :=
    Nat.le_of_dvd hQ (primeSetPart_dvd_of_subset hPQ a)
  have hbR : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have h := geom_ratio_antitone (b : ℝ) hbR (primeSetPart P a) (primeSetPart Q a) hP hle
  have hh := div_le_div_of_nonneg_right h (Nat.cast_nonneg a)
  convert hh using 1 <;> unfold primeWeightedTerm <;> rw [div_div, mul_comm ((a : ℕ) : ℝ)]

theorem summable_primeWeighted_enlarge (b : ℕ) (hb : 2 ≤ b)
    (A : Set ℕ) {P Q : Finset ℕ} (hPQ : P ⊆ Q)
    (hs : Summable (Set.indicator A (primeWeightedTerm b P))) :
    Summable (Set.indicator A (primeWeightedTerm b Q)) := by
  classical
  apply Summable.of_nonneg_of_le
    (fun a => Set.indicator_nonneg (fun a _ => primeWeightedTerm_nonneg b hb Q a) a) _ hs
  intro a
  by_cases ha : a ∈ A
  · simpa only [Set.indicator_of_mem ha] using primeWeightedTerm_antitone_primeSet b hb hPQ a
  · simp only [Set.indicator_of_notMem ha, le_refl]

theorem finitePrimeWeighted_mono (b : ℕ) (hb : 2 ≤ b)
    {A B : Set ℕ} (hBA : B ⊆ A) (hA : FinitePrimeWeighted b A) :
    FinitePrimeWeighted b B := by
  classical
  obtain ⟨P, hPn, hP, hs⟩ := hA
  refine ⟨P, hPn, hP, Summable.of_nonneg_of_le
    (fun a => Set.indicator_nonneg (fun a _ => primeWeightedTerm_nonneg b hb P a) a) ?_ hs⟩
  intro a
  by_cases ha : a ∈ B
  · simp only [Set.indicator_of_mem ha, Set.indicator_of_mem (hBA ha), le_refl]
  · rw [Set.indicator_of_notMem ha]
    exact Set.indicator_nonneg (fun a _ => primeWeightedTerm_nonneg b hb P a) a

theorem finitePrimeWeighted_empty (b : ℕ) : FinitePrimeWeighted b ∅ := by
  refine ⟨{2}, by simp, ?_, ?_⟩
  · intro p hp
    have hp2 : p = 2 := by simpa using hp
    subst p
    exact Nat.prime_two
  · simpa only [Set.indicator_empty] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

theorem finitePrimeWeighted_union (b : ℕ) (hb : 2 ≤ b)
    {A B : Set ℕ} (hA : FinitePrimeWeighted b A) (hB : FinitePrimeWeighted b B) :
    FinitePrimeWeighted b (A ∪ B) := by
  classical
  obtain ⟨P, hPn, hP, hsA⟩ := hA
  obtain ⟨Q, hQn, hQ, hsB⟩ := hB
  let U := P ∪ Q
  have hsA' := summable_primeWeighted_enlarge b hb A
    (show P ⊆ U from Finset.subset_union_left) hsA
  have hsB' := summable_primeWeighted_enlarge b hb B
    (show Q ⊆ U from Finset.subset_union_right) hsB
  refine ⟨U, hPn.mono Finset.subset_union_left, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hQ p hp
  · apply Summable.of_nonneg_of_le
      (fun a => Set.indicator_nonneg (fun a _ => primeWeightedTerm_nonneg b hb U a) a)
      _ (hsA'.add hsB')
    intro a
    have hn := primeWeightedTerm_nonneg b hb U a
    by_cases ha : a ∈ A <;> by_cases hb' : a ∈ B <;>
      simp [ha, hb', hn]

def finiteSupportUnion (I : Finset ℕ) (E : ℕ → Set ℕ) : Set ℕ :=
  {a | ∃ i ∈ I, a ∈ E i}

@[simp] theorem finiteSupportUnion_empty (E : ℕ → Set ℕ) :
    finiteSupportUnion ∅ E = ∅ := by ext a; simp [finiteSupportUnion]

@[simp] theorem finiteSupportUnion_insert (i : ℕ) (I : Finset ℕ) (E : ℕ → Set ℕ) :
    finiteSupportUnion (insert i I) E = E i ∪ finiteSupportUnion I E := by
  ext a
  simp only [finiteSupportUnion, Set.mem_setOf_eq, Finset.mem_insert, Set.mem_union]
  constructor
  · rintro ⟨j, rfl | hj, ha⟩
    · exact Or.inl ha
    · exact Or.inr ⟨j, hj, ha⟩
  · rintro (ha | ⟨j, hj, ha⟩)
    · exact ⟨i, Or.inl rfl, ha⟩
    · exact ⟨j, Or.inr hj, ha⟩

theorem finitePrimeWeighted_finiteUnion (b : ℕ) (hb : 2 ≤ b)
    (I : Finset ℕ) (E : ℕ → Set ℕ) (hE : ∀ i ∈ I, FinitePrimeWeighted b (E i)) :
    FinitePrimeWeighted b (finiteSupportUnion I E) := by
  classical
  revert hE
  induction I using Finset.induction_on with
  | empty => intro _; simpa using finitePrimeWeighted_empty b
  | @insert i I hi ih =>
    intro hE
    rw [finiteSupportUnion_insert]
    exact finitePrimeWeighted_union b hb (hE i (mem_insert_self _ _))
      (ih (fun j hj => hE j (mem_insert_of_mem hj)))

theorem finiteSupportUnion_positive (I : Finset ℕ) (E : ℕ → Set ℕ)
    (hE : ∀ i ∈ I, 0 ∉ E i) : 0 ∉ finiteSupportUnion I E := by
  rintro ⟨i, hi, hzero⟩
  exact hE i hi hzero

theorem hostPrefix_eq_finiteSupportUnion (E : ℕ → Set ℕ) (j : ℕ) :
    hostPrefix E j = finiteSupportUnion (range (j + 1)) E := by
  ext a
  simp only [hostPrefix, finiteSupportUnion, Set.mem_setOf_eq, Finset.mem_range]
  constructor <;> rintro ⟨i, hi, ha⟩ <;> exact ⟨i, by omega, ha⟩

end ErdosProblems.Erdos257.PaperCompleteR8
end
