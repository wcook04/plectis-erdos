import ErdosProblems.Erdos68.DivisorChannelBasis

/-!
# Full integral coordinate theorem

Short label res:divisor-channel-coordinates. The supplied library proves the
isolated moment/channel values, but does not prove spanning and uniqueness.
Here the auxiliary index 1 is represented by coordinate 0, and coordinate j>0
represents U_(j+1). Thus coordinates have type ℕ →₀ ℤ with no constrained
coordinate. The target coefficient vectors satisfy f 0 = 0, exactly the
paper's index convention n≥1 before its later restriction to n≥2.

The proof supplies spanning by triangular elimination, independence by the
moment/channel observables, and the explicit coefficient formula. This is
stronger than checking finitely many example matrices.
STATUS: uncompiled proof candidate. No axioms or proof placeholders.
-/
namespace ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open Finsupp

/-- An isolated unit has no coordinate at 0 and none above its own index. -/
lemma isolated_unit_outside (n i : ℕ) (hout : i = 0 ∨ n < i) :
    isolatedChannelUnit n i = 0 := by
  revert i
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hout
    by_cases hn : n ≤ 1
    · rw [isolatedChannelUnit_of_le_one hn]
      rfl
    · have hn2 : 2 ≤ n := by omega
      have hni : n ≠ i := by omega
      have hpred : n - 1 ≠ i := by omega
      have hT : adjacentDifference n i = 0 := by
        simp [adjacentDifference, hni, hpred, Ne.symm hni, Ne.symm hpred]
      rw [isolatedChannelUnit_of_two_le hn2, Finsupp.sub_apply, hT,
        Finsupp.finset_sum_apply]
      have hsum : (∑ d ∈ (Finset.Ico 2 n).attach,
          (if d.1 ∣ n then (channelWeight n d.1 : ℤ) •
            isolatedChannelUnit d.1 else 0) i) = 0 := by
        apply Finset.sum_eq_zero
        intro d _
        by_cases hdvd : d.1 ∣ n
        · have hdlt : d.1 < n := (Finset.mem_Ico.mp d.2).2
          have hz := ih d.1 hdlt i (by omega : i = 0 ∨ d.1 < i)
          simp [hdvd, Finsupp.smul_apply, hz]
        · simp [hdvd]
      rw [hsum]
      simp

lemma isolated_unit_leading {n : ℕ} (hn : 2 ≤ n) :
    isolatedChannelUnit n n = -1 := by
  have hpred : n - 1 ≠ n := by omega
  have hT : adjacentDifference n n = -1 := by
    simp [adjacentDifference, hpred, Ne.symm hpred]
  rw [isolatedChannelUnit_of_two_le hn, Finsupp.sub_apply, hT,
    Finsupp.finset_sum_apply]
  have hsum : (∑ d ∈ (Finset.Ico 2 n).attach,
      (if d.1 ∣ n then (channelWeight n d.1 : ℤ) •
        isolatedChannelUnit d.1 else 0) n) = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    by_cases hdvd : d.1 ∣ n
    · have hz := isolated_unit_outside d.1 n
        (Or.inr (Finset.mem_Ico.mp d.2).2)
      simp [hdvd, Finsupp.smul_apply, hz]
    · simp [hdvd]
  rw [hsum, sub_zero]

/-- b_0=e_1 and b_j=U_(j+1) for j>0. -/
noncomputable def channelBasisColumn (j : ℕ) : ℕ →₀ ℤ :=
  if j = 0 then single 1 1 else isolatedChannelUnit (j + 1)

noncomputable def channelSynthesis (a : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  a.sum (fun j z => z • channelBasisColumn j)

lemma channelSynthesis_add (a b : ℕ →₀ ℤ) :
    channelSynthesis (a + b) = channelSynthesis a + channelSynthesis b := by
  unfold channelSynthesis
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => add_smul _ _ _)

lemma channelSynthesis_single (j : ℕ) (z : ℤ) :
    channelSynthesis (single j z) = z • channelBasisColumn j := by
  unfold channelSynthesis
  exact Finsupp.sum_single_index (by simp)

lemma basisColumn_moment (j : ℕ) :
    factorialMoment (channelBasisColumn j) = if j = 0 then 1 else 0 := by
  by_cases hj : j = 0
  · simp [channelBasisColumn, hj, factorialMoment_single]
  · simp only [channelBasisColumn, if_neg hj]
    exact factorialMoment_isolatedChannelUnit (by omega)

lemma basisColumn_channel (j d : ℕ) (hd : 2 ≤ d) :
    channelNumerator (channelBasisColumn j) d =
      (if j = 0 then 1 else 0) +
      (if j = d - 1 then (d.factorial : ℤ) - 1 else 0) := by
  by_cases hj : j = 0
  · subst j
    have hdn : ¬ (0 : ℕ) = d - 1 := by omega
    have h1d : (1 : ℕ) < d := by omega
    simp [channelBasisColumn, channelNumerator_single, channelWeight,
      Nat.div_eq_of_lt h1d, hdn]
  · have hj2 : 2 ≤ j + 1 := by omega
    rw [channelBasisColumn, if_neg hj,
      channelNumerator_isolatedChannelUnit hj2 hd]
    by_cases heq : d = j + 1
    · subst d
      simp [hj]
    · have hne : j ≠ d - 1 := by omega
      simp [heq, hj, hne]

lemma synthesis_moment (a : ℕ →₀ ℤ) :
    factorialMoment (channelSynthesis a) = a 0 := by
  classical
  change factorialMoment (∑ j ∈ a.support, a j • channelBasisColumn j) = _
  rw [factorialMoment_sum]
  simp_rw [factorialMoment_smul, basisColumn_moment]
  by_cases ha : a 0 = 0
  · simp [mul_ite, ha, Finsupp.mem_support_iff]
  · simp [mul_ite, ha, Finsupp.mem_support_iff]

lemma synthesis_channel (a : ℕ →₀ ℤ) (d : ℕ) (hd : 2 ≤ d) :
    channelNumerator (channelSynthesis a) d =
      a 0 + ((d.factorial : ℤ) - 1) * a (d - 1) := by
  classical
  change channelNumerator (∑ j ∈ a.support, a j • channelBasisColumn j) d = _
  rw [channelNumerator_sum]
  simp_rw [channelNumerator_smul, basisColumn_channel _ d hd, mul_add]
  rw [Finset.sum_add_distrib]
  have hfirst : (∑ j ∈ a.support, a j * (if j = 0 then (1 : ℤ) else 0)) = a 0 := by
    by_cases ha : a 0 = 0 <;> simp [mul_ite, ha, Finsupp.mem_support_iff]
  have hsecond : (∑ j ∈ a.support, a j *
      (if j = d - 1 then (d.factorial : ℤ) - 1 else 0)) =
      ((d.factorial : ℤ) - 1) * a (d - 1) := by
    by_cases ha : a (d - 1) = 0 <;>
      simp [mul_ite, ha, Finsupp.mem_support_iff, mul_comm]
  rw [hfirst, hsecond]

/-- Independence uses the observables, not a rational determinant argument. -/
theorem channelSynthesis_injective : Function.Injective channelSynthesis := by
  intro a b hab
  have hzero := congrArg factorialMoment hab
  rw [synthesis_moment, synthesis_moment] at hzero
  ext j
  by_cases hj : j = 0
  · simpa [hj] using hzero
  · have hd : 2 ≤ j + 1 := by omega
    have hchan : channelNumerator (channelSynthesis a) (j + 1) =
        channelNumerator (channelSynthesis b) (j + 1) :=
      congrArg (fun f => channelNumerator f (j + 1)) hab
    rw [synthesis_channel _ _ hd, synthesis_channel _ _ hd] at hchan
    have hfac : (1 : ℤ) < (j + 1).factorial := by
      exact_mod_cast Nat.one_lt_factorial.mpr hd
    have hne : ((j + 1).factorial : ℤ) - 1 ≠ 0 := by omega
    have hmul : (((j + 1).factorial : ℤ) - 1) * a j =
        (((j + 1).factorial : ℤ) - 1) * b j := by
      rw [hzero] at hchan
      simpa only [Nat.add_sub_cancel] using (add_left_cancel hchan)
    exact mul_left_cancel₀ hne hmul

/-- Integral spanning with a specified upper support, proved by eliminating
its highest coefficient using the unit leading coefficient -1. -/
lemma exists_synthesis_of_bounded_support (N : ℕ) (f : ℕ →₀ ℤ)
    (hzero : f 0 = 0) (hbound : ∀ i : ℕ, N < i → f i = 0) :
    ∃ a : ℕ →₀ ℤ, channelSynthesis a = f := by
  classical
  induction N generalizing f with
  | zero =>
    have hf : f = 0 := by
      ext i
      by_cases hi : i = 0
      · simpa [hi] using hzero
      · exact hbound i (by omega)
    refine ⟨0, ?_⟩
    simp [channelSynthesis, hf]
  | succ N ih =>
    by_cases hN : N = 0
    · subst N
      refine ⟨single 0 (f 1), ?_⟩
      rw [channelSynthesis_single]
      simp only [channelBasisColumn, if_pos rfl]
      ext i
      by_cases hi : i = 1
      · subst i
        simp
      · by_cases hi0 : i = 0
        · subst i
          simp [hzero]
        · have hfi : f i = 0 := hbound i (by omega)
          simp [Finsupp.smul_apply, Finsupp.single_apply, hi, Ne.symm hi, hfi]
    · have hn2 : 2 ≤ N + 1 := by omega
      let f' := f + f (N + 1) • isolatedChannelUnit (N + 1)
      have hf'0 : f' 0 = 0 := by
        simp [f', Finsupp.add_apply, Finsupp.smul_apply, hzero,
          isolated_unit_outside (N + 1) 0 (Or.inl rfl)]
      have hf'bound : ∀ i : ℕ, N < i → f' i = 0 := by
        intro i hi
        by_cases heq : i = N + 1
        · subst i
          simp [f', Finsupp.add_apply, Finsupp.smul_apply,
            isolated_unit_leading hn2, smul_eq_mul]
        · have hNi : N + 1 < i := by omega
          simp [f', Finsupp.add_apply, Finsupp.smul_apply, hbound i hNi,
            isolated_unit_outside (N + 1) i (Or.inr hNi)]
      obtain ⟨a, ha⟩ := ih f' hf'0 hf'bound
      refine ⟨a + single N (-f (N + 1)), ?_⟩
      rw [channelSynthesis_add, channelSynthesis_single, ha]
      simp only [channelBasisColumn, if_neg hN]
      dsimp [f']
      simp only [neg_smul]
      first
        | exact add_neg_cancel_right _ _
        | simp

/-- Each coefficient vector on n≥1 has a UNIQUE finite integral expansion. -/
theorem existsUnique_channel_coordinates (f : ℕ →₀ ℤ) (hzero : f 0 = 0) :
    ∃! a : ℕ →₀ ℤ, channelSynthesis a = f := by
  classical
  let N := f.support.sup id
  have hbound : ∀ i : ℕ, N < i → f i = 0 := by
    intro i hi
    by_contra hfi
    have hmem : i ∈ f.support := Finsupp.mem_support_iff.mpr hfi
    have hle : i ≤ N := Finset.le_sup (f := id) hmem
    omega
  obtain ⟨a, ha⟩ := exists_synthesis_of_bounded_support N f hzero hbound
  exact ⟨a, ha, fun b hb => channelSynthesis_injective (hb.trans ha.symm)⟩

/-- The unique coordinates have the literal quotient formula printed in the note. -/
theorem channel_coordinates_formula (a f : ℕ →₀ ℤ)
    (ha : channelSynthesis a = f) :
    a 0 = factorialMoment f ∧
    ∀ d : ℕ, 2 ≤ d →
      a (d - 1) = (channelNumerator f d - factorialMoment f) /
        ((d.factorial : ℤ) - 1) := by
  have hm : a 0 = factorialMoment f := by
    rw [← ha, synthesis_moment]
  refine ⟨hm, ?_⟩
  intro d hd
  have hc := synthesis_channel a d hd
  rw [ha, hm] at hc
  have hfac : (1 : ℤ) < d.factorial := by
    exact_mod_cast Nat.one_lt_factorial.mpr hd
  have hne : (d.factorial : ℤ) - 1 ≠ 0 := by omega
  have hnum : channelNumerator f d - factorialMoment f =
      ((d.factorial : ℤ) - 1) * a (d - 1) := by omega
  have hdiv : ((d.factorial : ℤ) - 1) ∣
      channelNumerator f d - factorialMoment f := ⟨a (d - 1), hnum⟩
  symm
  apply (Int.ediv_eq_iff_eq_mul_left hne hdiv).mpr
  rw [hnum]
  ring

/-- Whole displayed coordinate theorem: isolated observables, integral basis,
and the unique coefficient formula. The recurrence is the definition of U_n
and is exposed by isolatedChannelUnit_of_two_le in the supplied source. -/
theorem divisor_channel_coordinates :
    (∀ n : ℕ, 2 ≤ n → factorialMoment (isolatedChannelUnit n) = 0) ∧
    (∀ n d : ℕ, 2 ≤ n → 2 ≤ d →
      channelNumerator (isolatedChannelUnit n) d =
        if d = n then (n.factorial : ℤ) - 1 else 0) ∧
    (∀ f : ℕ →₀ ℤ, f 0 = 0 →
      ∃! a : ℕ →₀ ℤ, channelSynthesis a = f) ∧
    (∀ a f : ℕ →₀ ℤ, channelSynthesis a = f →
      a 0 = factorialMoment f ∧
      ∀ d : ℕ, 2 ≤ d → a (d - 1) =
        (channelNumerator f d - factorialMoment f) / ((d.factorial : ℤ) - 1)) :=
  ⟨fun _ hn => factorialMoment_isolatedChannelUnit hn,
   fun _ _ hn hd => channelNumerator_isolatedChannelUnit hn hd,
   existsUnique_channel_coordinates, channel_coordinates_formula⟩

end ErdosProblems.Erdos68.PaperComplete
