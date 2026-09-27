import Erdos249257.BooleanMobiusCofinalExactRows

/-!
# Exact Boolean quotient rows agree below a gap threshold

An exact Boolean quotient row at endpoint `n ≥ 2` is a finite set `D` of
integers in `[2, n]` with `localPrefixQuotient D n = 2^(n-1) - 1`
(`ExactLocalMersenneHalfRow`).  Its Mersenne value `∑ d ∈ D, 1 / (2^d - 1)`
lies within `(n + 1) / 2^n` of `1/2`
(`abs_exactLocalMersenneRowValue_sub_half_le`).  The gap at rank `j` is
`mersenneWeight j - mersenneTail j`, which is `mersenneGap j`.

This module proves the following.

* `sum_le_mersenneTail`: a finite Mersenne subsum supported strictly above `j`
  is at most `mersenneTail j`.
* `gap_le_sub_of_least_diff`: if two finite sets first disagree at rank `j`,
  the one containing `j` has Mersenne value larger by at least the gap at `j`.
* `gap_le_two_mul_of_ne`: two distinct finite sets whose Mersenne values both
  lie within `ε` of `1/2` first disagree at a rank whose gap is at most `2 ε`.
* `exactLocalMersenneRowValue_eq_sum`: `exactLocalMersenneRowValue D` is the
  real sum `∑ d ∈ D, mersenneWeight d`.
* `exactRow_gap_le`: two distinct exact rows at the same endpoint `n` first
  disagree at a rank whose gap is at most `2 (n + 1) / 2^n`.
* `exactRow_agree_below_of_two_le`: if the gap at every rank `i` with
  `2 ≤ i < J` exceeds `2 (n + 1) / 2^n`, any two exact rows at endpoint `n`
  contain the same ranks below `J`.  Ranks `0` and `1` lie in no exact row, so
  the hypothesis starts at rank `2`.
* `exactRow_mersenneGap_le` and `exactRow_agree_below_mersenneGap` state the
  last two results with the gap written as `mersenneGap`.

The module does not determine the ranks at which the gap exceeds
`2 (n + 1) / 2^n`, and it does not prove that an exact row exists at any
endpoint.
-/

namespace Erdos249257.ExactRowRigidity

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

/-- The row value of an exact-row support is the real Mersenne sum over the
support. -/
theorem exactLocalMersenneRowValue_eq_sum (D : Finset ℕ) :
    exactLocalMersenneRowValue D = ∑ d ∈ D, mersenneWeight d := by
  unfold exactLocalMersenneRowValue localMersennePrefixValue
  rw [Rat.cast_sum]
  exact Finset.sum_congr rfl fun d _ => cast_mersenneWeightRat d

/-- **First disagreement of exact rows.**  Two distinct exact Boolean quotient
rows at the same endpoint `n` first disagree at a rank whose gap is at most
`2 (n + 1) / 2^n`. -/
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

/-! ## Agreement below a threshold rank -/

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

/-- `exactRow_gap_le` with the gap written as `mersenneGap`. -/
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

/-- `exactRow_agree_below_of_two_le` with the gap written as `mersenneGap`. -/
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

#print axioms sum_le_mersenneTail
#print axioms gap_le_sub_of_least_diff
#print axioms gap_le_two_mul_of_ne
#print axioms exactLocalMersenneRowValue_eq_sum
#print axioms exactRow_gap_le
#print axioms exactRow_agree_below_of_two_le
#print axioms exactRow_mersenneGap_le
#print axioms exactRow_agree_below_mersenneGap

end Erdos249257.ExactRowRigidity
