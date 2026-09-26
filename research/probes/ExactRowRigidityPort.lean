import Erdos249257.BooleanMobiusCofinalExactRows

/-!
# Kernel probe: exact Boolean rows are rigid below half depth

Scratch file for the kernel-probe workflow.

Let `D`, `E` be exact Boolean quotient rows at the same endpoint `n`: supports in
`[2, n]` with quotient sum `2^(n-1) - 1`.  If every rank `i` with `2 ≤ i < J` has
Mersenne gap `mersenneWeight i - mersenneTail i` larger than `2 (n + 1) / 2^n`, then
`D` and `E` agree on every rank below `J` (`exactRow_agree_below_of_two_le`).
Equivalently, two distinct such rows first disagree at a rank whose gap is at most
`2 (n + 1) / 2^n` (`exactRow_gap_le`).

The only inputs are strict superincreasingness of the Mersenne weights and the
exact-row approximation `abs_exactLocalMersenneRowValue_sub_half_le` of
`Erdos249257.BooleanMobiusCofinalExactRows`.  If two finite supports first
disagree at rank `j`, their Mersenne values differ by at least the rank-`j` gap
(`gap_le_sub_of_least_diff`); two values within `ε` of one half therefore first
disagree at a rank whose gap is at most `2 ε` (`gap_le_two_mul_of_ne`).

`exactRow_agree_below` is the statement as first written, with the gap hypothesis
over every rank `i < J`.  At rank `0` the gap is `-mersenneTail 0 < 0`, because
`mersenneWeight 0 = 1 / 0 = 0`, so that hypothesis fails whenever `J ≥ 1`
(`not_exactRow_agree_below_hyp`) and the statement is vacuous.
`exactRow_agree_below_of_two_le` asks for the gap bound only on the ranks
`2 ≤ i < J` that a support in `[2, n]` can occupy, and has the same conclusion.

Every definition used is the public one: `mersenneWeight`, `mersenneTail`,
`mersenneWeightRat`, `localPrefixQuotient`, `localMersennePrefixValue`,
`exactLocalMersenneRowValue` and `mersenneGap` in namespace `Erdos249257`.
-/

namespace Erdos249257
namespace ExactRowRigidity

/-! ## Finite subsums of a tail -/

/-- A finite Mersenne subsum supported strictly above `j` is at most the tail after `j`. -/
theorem sum_le_mersenneTail {S : Finset ℕ} {j : ℕ} (hS : ∀ d ∈ S, j < d) :
    ∑ d ∈ S, mersenneWeight d ≤ mersenneTail j := by
  have hinj : Set.InjOn (fun d : ℕ => d - j - 1) (S : Set ℕ) := by
    intro a ha b hb hab
    have h1 : j < a := hS a (Finset.mem_coe.1 ha)
    have h2 : j < b := hS b (Finset.mem_coe.1 hb)
    have hab' : a - j - 1 = b - j - 1 := hab
    omega
  have hkey : ∑ k ∈ S.image (fun d : ℕ => d - j - 1), mersenneWeight (j + k + 1)
      = ∑ d ∈ S, mersenneWeight d := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hjd : j < d := hS d hd
    have e : j + (d - j - 1) + 1 = d := by omega
    show mersenneWeight (j + (d - j - 1) + 1) = mersenneWeight d
    rw [e]
  rw [← hkey, mersenneTail]
  have hnonneg : ∀ k : ℕ, k ∉ S.image (fun d : ℕ => d - j - 1) →
      0 ≤ mersenneWeight (j + k + 1) :=
    fun k _ => (mersenneWeight_pos (by omega : 0 < j + k + 1)).le
  exact sum_le_hasSum (S.image (fun d : ℕ => d - j - 1)) hnonneg
    (summable_mersenneTail j).hasSum

/-! ## Gap separation -/

/-- **Gap separation.**  If two finite supports first disagree at rank `j`, the one
containing `j` has Mersenne value larger by at least the rank-`j` gap. -/
theorem gap_le_sub_of_least_diff
    {D E : Finset ℕ} {j : ℕ}
    (hlow : ∀ i, i < j → (i ∈ D ↔ i ∈ E))
    (hjD : j ∉ D) (hjE : j ∈ E) :
    mersenneWeight j - mersenneTail j
      ≤ (∑ d ∈ E, mersenneWeight d) - (∑ d ∈ D, mersenneWeight d) := by
  have hDsplit :
      (∑ d ∈ D.filter (fun d => d < j), mersenneWeight d)
          + (∑ d ∈ D.filter (fun d => ¬ d < j), mersenneWeight d)
        = ∑ d ∈ D, mersenneWeight d :=
    Finset.sum_filter_add_sum_filter_not D (fun d => d < j) mersenneWeight
  have hEsplit :
      (∑ d ∈ E.filter (fun d => d < j), mersenneWeight d)
          + (∑ d ∈ E.filter (fun d => ¬ d < j), mersenneWeight d)
        = ∑ d ∈ E, mersenneWeight d :=
    Finset.sum_filter_add_sum_filter_not E (fun d => d < j) mersenneWeight
  have hlowset : D.filter (fun d => d < j) = E.filter (fun d => d < j) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hlt⟩
      exact ⟨(hlow i hlt).1 hi, hlt⟩
    · rintro ⟨hi, hlt⟩
      exact ⟨(hlow i hlt).2 hi, hlt⟩
  have hlowsum :
      ∑ d ∈ D.filter (fun d => d < j), mersenneWeight d
        = ∑ d ∈ E.filter (fun d => d < j), mersenneWeight d := by
    rw [hlowset]
  -- the high part of `D` avoids `j`, so it lies strictly above `j`
  have hDhi : ∑ d ∈ D.filter (fun d => ¬ d < j), mersenneWeight d ≤ mersenneTail j := by
    refine sum_le_mersenneTail ?_
    intro d hd
    have hd' := Finset.mem_filter.1 hd
    have hdD : d ∈ D := hd'.1
    have hdj : ¬ d < j := hd'.2
    by_cases h : j < d
    · exact h
    · exfalso
      have hdeq : d = j := by omega
      rw [hdeq] at hdD
      exact hjD hdD
  -- the high part of `E` contains `j`, and its other terms are nonnegative
  have hjmem : j ∈ E.filter (fun d => ¬ d < j) :=
    Finset.mem_filter.2 ⟨hjE, Nat.lt_irrefl j⟩
  have hEhi : mersenneWeight j
      ≤ ∑ d ∈ E.filter (fun d => ¬ d < j), mersenneWeight d := by
    have hsplit :
        mersenneWeight j + ∑ d ∈ (E.filter (fun d => ¬ d < j)).erase j, mersenneWeight d
          = ∑ d ∈ E.filter (fun d => ¬ d < j), mersenneWeight d :=
      Finset.add_sum_erase _ mersenneWeight hjmem
    have hnn : 0 ≤ ∑ d ∈ (E.filter (fun d => ¬ d < j)).erase j, mersenneWeight d := by
      refine Finset.sum_nonneg ?_
      intro d hd
      have hdj : d ≠ j := Finset.ne_of_mem_erase hd
      have hdf : ¬ d < j := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hd)).2
      exact (mersenneWeight_pos (by omega : 0 < d)).le
    linarith
  linarith

/-! ## Rigidity -/

/-- Two finite supports whose Mersenne values both lie within `ε` of one half, and
which differ, first disagree at a rank whose gap is at most `2 ε`. -/
theorem gap_le_two_mul_of_ne
    {D E : Finset ℕ} {ε : ℝ}
    (hDval : |(∑ d ∈ D, mersenneWeight d) - 1 / 2| ≤ ε)
    (hEval : |(∑ d ∈ E, mersenneWeight d) - 1 / 2| ≤ ε)
    (hne : D ≠ E) :
    ∃ j : ℕ,
      (∀ i, i < j → (i ∈ D ↔ i ∈ E)) ∧ ¬ (j ∈ D ↔ j ∈ E) ∧
        mersenneWeight j - mersenneTail j ≤ 2 * ε := by
  have hex : ∃ i : ℕ, ¬ (i ∈ D ↔ i ∈ E) := by
    by_contra h
    refine hne (Finset.ext fun i => ?_)
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨hD1, hD2⟩ := abs_le.1 hDval
  obtain ⟨hE1, hE2⟩ := abs_le.1 hEval
  have hlow : ∀ i, i < Nat.find hex → (i ∈ D ↔ i ∈ E) := by
    intro i hi
    by_contra h
    exact Nat.find_min hex hi h
  have hspec : ¬ (Nat.find hex ∈ D ↔ Nat.find hex ∈ E) := Nat.find_spec hex
  refine ⟨Nat.find hex, hlow, hspec, ?_⟩
  by_cases hjD : Nat.find hex ∈ D
  · have hjE : Nat.find hex ∉ E := fun h => hspec ⟨fun _ => h, fun _ => hjD⟩
    have hlow' : ∀ i, i < Nat.find hex → (i ∈ E ↔ i ∈ D) :=
      fun i hi => (hlow i hi).symm
    have hgap := gap_le_sub_of_least_diff hlow' hjE hjD
    linarith
  · have hjE : Nat.find hex ∈ E := by
      by_contra h
      exact hspec ⟨fun hh => absurd hh hjD, fun hh => absurd hh h⟩
    have hgap := gap_le_sub_of_least_diff hlow hjD hjE
    linarith

/-! ## Exact quotient rows -/

theorem exactLocalMersenneRowValue_eq_sum (D : Finset ℕ) :
    exactLocalMersenneRowValue D = ∑ d ∈ D, mersenneWeight d := by
  unfold exactLocalMersenneRowValue localMersennePrefixValue
  rw [Rat.cast_sum]
  exact Finset.sum_congr rfl fun d _ => cast_mersenneWeightRat d

/-- **Exact rows cluster.**  Two distinct exact Boolean quotient rows at the same
endpoint `n` first disagree at a rank whose gap is at most `2 (n + 1) / 2^n`. -/
theorem exactRow_gap_le
    {D E : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hDq : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (hEq : localPrefixQuotient E n = 2 ^ (n - 1) - 1)
    (hne : D ≠ E) :
    ∃ j : ℕ,
      (∀ i, i < j → (i ∈ D ↔ i ∈ E)) ∧ ¬ (j ∈ D ↔ j ∈ E) ∧
        mersenneWeight j - mersenneTail j ≤ 2 * (((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
  have hDval :
      |(∑ d ∈ D, mersenneWeight d) - 1 / 2| ≤ ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
    rw [← exactLocalMersenneRowValue_eq_sum]
    exact abs_exactLocalMersenneRowValue_sub_half_le hn hD hDq
  have hEval :
      |(∑ d ∈ E, mersenneWeight d) - 1 / 2| ≤ ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
    rw [← exactLocalMersenneRowValue_eq_sum]
    exact abs_exactLocalMersenneRowValue_sub_half_le hn hE hEq
  exact gap_le_two_mul_of_ne hDval hEval hne

/-- The rigidity statement as first written: the gap hypothesis ranges over every
rank `i < J`.  `not_exactRow_agree_below_hyp` shows that hypothesis fails for every
`J ≥ 1`; `exactRow_agree_below_of_two_le` is the form with content. -/
theorem exactRow_agree_below
    {D E : Finset ℕ} {n J : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hDq : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (hEq : localPrefixQuotient E n = 2 ^ (n - 1) - 1)
    (hgap : ∀ i, i < J →
      2 * (((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) < mersenneWeight i - mersenneTail i) :
    ∀ i, i < J → (i ∈ D ↔ i ∈ E) := by
  by_cases hne : D = E
  · subst hne
    intro i _
    exact Iff.rfl
  · intro i hi
    obtain ⟨j, hlow, _, hjgap⟩ := exactRow_gap_le hn hD hDq hE hEq hne
    by_contra hcon
    have hji : j ≤ i := by
      by_contra h
      exact hcon (hlow i (by omega))
    exact absurd hjgap (not_le.2 (hgap j (by omega)))

/-! ## Rank zero, and the rigidity statement with content -/

/-- The rank-zero gap is negative: `mersenneWeight 0 = 1 / 0 = 0`. -/
theorem mersenneWeight_zero_sub_mersenneTail_zero_neg :
    mersenneWeight 0 - mersenneTail 0 < 0 := by
  rw [mersenneWeight_zero]
  have h := mersenneTail_pos 0
  linarith

/-- The gap hypothesis of `exactRow_agree_below` fails at rank `0` whenever `J ≥ 1`. -/
theorem not_exactRow_agree_below_hyp {n J : ℕ} (hJ : 0 < J) :
    ¬ ∀ i, i < J →
      2 * (((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) < mersenneWeight i - mersenneTail i := by
  intro hgap
  have h0 := hgap 0 hJ
  have hpos : 0 ≤ 2 * (((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by positivity
  have hneg := mersenneWeight_zero_sub_mersenneTail_zero_neg
  linarith

/-- **Exact rows agree below the threshold rank.**  If every rank `i` with
`2 ≤ i < J` has gap larger than `2 (n + 1) / 2^n`, all exact Boolean quotient rows
at endpoint `n` carry the same Boolean word on the ranks below `J`. -/
theorem exactRow_agree_below_of_two_le
    {D E : Finset ℕ} {n J : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hDq : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (hEq : localPrefixQuotient E n = 2 ^ (n - 1) - 1)
    (hgap : ∀ i, 2 ≤ i → i < J →
      2 * (((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) < mersenneWeight i - mersenneTail i) :
    ∀ i, i < J → (i ∈ D ↔ i ∈ E) := by
  by_cases hne : D = E
  · subst hne
    intro i _
    exact Iff.rfl
  · intro i hi
    obtain ⟨j, hlow, hjne, hjgap⟩ := exactRow_gap_le hn hD hDq hE hEq hne
    have hj2 : 2 ≤ j := by
      by_cases hjD : j ∈ D
      · exact (hD j hjD).1
      · have hjE : j ∈ E := by
          by_contra hjE'
          exact hjne ⟨fun h => absurd h hjD, fun h => absurd h hjE'⟩
        exact (hE j hjE).1
    by_contra hcon
    have hji : j ≤ i := by
      by_contra h
      exact hcon (hlow i (by omega))
    exact absurd hjgap (not_le.2 (hgap j hj2 (by omega)))

/-! ## The same statements with the public gap `mersenneGap` -/

theorem exactRow_mersenneGap_le
    {D E : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hDq : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (hEq : localPrefixQuotient E n = 2 ^ (n - 1) - 1)
    (hne : D ≠ E) :
    ∃ j : ℕ,
      (∀ i, i < j → (i ∈ D ↔ i ∈ E)) ∧ ¬ (j ∈ D ↔ j ∈ E) ∧
        mersenneGap j ≤ 2 * (((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) :=
  exactRow_gap_le hn hD hDq hE hEq hne

theorem exactRow_agree_below_mersenneGap
    {D E : Finset ℕ} {n J : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hDq : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (hEq : localPrefixQuotient E n = 2 ^ (n - 1) - 1)
    (hgap : ∀ i, 2 ≤ i → i < J →
      2 * (((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) < mersenneGap i) :
    ∀ i, i < J → (i ∈ D ↔ i ∈ E) :=
  exactRow_agree_below_of_two_le hn hD hDq hE hEq hgap

end ExactRowRigidity
end Erdos249257

#print axioms Erdos249257.ExactRowRigidity.sum_le_mersenneTail
#print axioms Erdos249257.ExactRowRigidity.gap_le_sub_of_least_diff
#print axioms Erdos249257.ExactRowRigidity.gap_le_two_mul_of_ne
#print axioms Erdos249257.ExactRowRigidity.exactLocalMersenneRowValue_eq_sum
#print axioms Erdos249257.ExactRowRigidity.exactRow_gap_le
#print axioms Erdos249257.ExactRowRigidity.exactRow_agree_below
#print axioms Erdos249257.ExactRowRigidity.mersenneWeight_zero_sub_mersenneTail_zero_neg
#print axioms Erdos249257.ExactRowRigidity.not_exactRow_agree_below_hyp
#print axioms Erdos249257.ExactRowRigidity.exactRow_agree_below_of_two_le
#print axioms Erdos249257.ExactRowRigidity.exactRow_mersenneGap_le
#print axioms Erdos249257.ExactRowRigidity.exactRow_agree_below_mersenneGap
