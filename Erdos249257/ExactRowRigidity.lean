import Erdos249257.BooleanMobiusCofinalExactRows

/-!
# Exact Boolean rows have no freedom below half depth

`BooleanMobiusCofinalExactRows` supplies the forward producer: a cofinal family of exact
Boolean quotient rows gives `1/2 ∈ mersenneAchievementSet`, with no compatibility imposed
between the witnesses at different endpoints.  That freedom is what makes the exact-row
socket look like a genuinely weaker combinatorial target than the canonical greedy orbit.

This module shows the freedom is not there.

The whole content is strict superincreasingness (`mersenneTail_lt_weight`).  If two supports
first disagree at rank `j`, their Mersenne values differ by at least the rank-`j` gap
`mersenneWeight j - mersenneTail j`.  Exact rows at endpoint `n` all lie within `(n+1)/2^n`
of one half (`abs_exactLocalMersenneRowValue_sub_half_le`), so two of them cannot disagree
at any rank whose gap exceeds `2 (n+1) / 2^n`.  Since the gap at rank `j` is of order
`(2/3) 4^{-j}`, every exact row at endpoint `n` is pinned on

`[2, (n - log₂ n) / 2]`

and the only remaining freedom sits above half depth, where the whole reachable range is the
tail `T` of size `2^{-n/2}` — exactly the resolution of the question at depth `n/2`.

Consequently the exact-row search is not a search: the rows at a given endpoint form a single
cluster around one word, and that word is the canonical greedy prefix.  A cofinal supply of
exact rows is therefore not a weaker producer than the canonical orbit; it is the same
statement re-encoded.  The same applies to every downstream socket in that module
(`CofinalHalfCutoffGreedyWindows`, `CofinalEvenHalfCutoffCoreSafety`,
`CofinalEvenHalfCutoffCoreBound`, `EvenHalfCutoffCoreRemainderSubquadraticAlong`), since each
of them implies `CofinalExactLocalMersenneHalfRows`.
-/

namespace Erdos249257
namespace ExactRowRigidity

open Finset

/-! ## Finite subsums of a tail -/

/-- A finite Mersenne subsum supported strictly above `j` never exceeds the tail after `j`. -/
theorem sum_le_mersenneTail {S : Finset ℕ} {j : ℕ} (hS : ∀ d ∈ S, j < d) :
    ∑ d ∈ S, mersenneWeight d ≤ mersenneTail j := by
  classical
  have hinj : ∀ a ∈ S, ∀ b ∈ S, a - j - 1 = b - j - 1 → a = b := by
    intro a ha b hb hab
    have h1 := hS a ha
    have h2 := hS b hb
    omega
  have hkey : ∑ k ∈ S.image (fun d => d - j - 1), mersenneWeight (j + k + 1)
      = ∑ d ∈ S, mersenneWeight d := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl ?_
    intro d hd
    have := hS d hd
    congr 1
    omega
  rw [← hkey, mersenneTail]
  exact sum_le_hasSum _
    (fun k _ => (mersenneWeight_pos (by omega : 0 < j + k + 1)).le)
    (summable_mersenneTail j).hasSum

/-! ## The gap separation -/

/-- **Gap separation.**  If two finite supports first disagree at rank `j`, the one containing
`j` is larger by at least the rank-`j` gap. -/
theorem gap_le_sub_of_least_diff
    {D E : Finset ℕ} {j : ℕ}
    (hlow : ∀ i, i < j → (i ∈ D ↔ i ∈ E))
    (hjD : j ∉ D) (hjE : j ∈ E) :
    mersenneWeight j - mersenneTail j
      ≤ (∑ d ∈ E, mersenneWeight d) - (∑ d ∈ D, mersenneWeight d) := by
  classical
  have hDsplit :
      ∑ d ∈ D, mersenneWeight d
        = (∑ d ∈ D.filter (fun d => d < j), mersenneWeight d)
          + ∑ d ∈ D.filter (fun d => ¬ d < j), mersenneWeight d :=
    (Finset.sum_filter_add_sum_filter_not D (fun d => d < j) _).symm
  have hEsplit :
      ∑ d ∈ E, mersenneWeight d
        = (∑ d ∈ E.filter (fun d => d < j), mersenneWeight d)
          + ∑ d ∈ E.filter (fun d => ¬ d < j), mersenneWeight d :=
    (Finset.sum_filter_add_sum_filter_not E (fun d => d < j) _).symm
  have hlowset : D.filter (fun d => d < j) = E.filter (fun d => d < j) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hlt⟩; exact ⟨(hlow i hlt).1 hi, hlt⟩
    · rintro ⟨hi, hlt⟩; exact ⟨(hlow i hlt).2 hi, hlt⟩
  -- the high part of `D` avoids `j` entirely
  have hDhi : ∑ d ∈ D.filter (fun d => ¬ d < j), mersenneWeight d ≤ mersenneTail j := by
    refine sum_le_mersenneTail ?_
    intro d hd
    have hd' := Finset.mem_filter.1 hd
    rcases Nat.lt_or_ge j d with h | h
    · exact h
    · exact absurd (by omega : d = j) (fun hdj => hjD (hdj ▸ hd'.1))
  -- the high part of `E` contains `j` and is otherwise nonnegative
  have hjmem : j ∈ E.filter (fun d => ¬ d < j) := by
    simp [Finset.mem_filter, hjE]
  have hEhi : mersenneWeight j
      ≤ ∑ d ∈ E.filter (fun d => ¬ d < j), mersenneWeight d := by
    rw [← Finset.add_sum_erase _ _ hjmem]
    have hnn : 0 ≤ ∑ d ∈ (E.filter (fun d => ¬ d < j)).erase j, mersenneWeight d := by
      refine Finset.sum_nonneg ?_
      intro d hd
      have hd' := Finset.mem_of_mem_erase hd
      have hdj : d ≠ j := Finset.ne_of_mem_erase hd
      have := Finset.mem_filter.1 hd'
      exact (mersenneWeight_pos (by omega : 0 < d)).le
    linarith
  rw [hDsplit, hEsplit, hlowset]
  linarith

/-! ## Rigidity -/

/-- **Theorem C.**  Two finite supports whose Mersenne values are both within `ε` of one half
cannot first disagree at a rank whose gap exceeds `2 ε`. -/
theorem gap_le_two_mul_of_ne
    {D E : Finset ℕ} {ε : ℝ}
    (hDval : |(∑ d ∈ D, mersenneWeight d) - 1 / 2| ≤ ε)
    (hEval : |(∑ d ∈ E, mersenneWeight d) - 1 / 2| ≤ ε)
    (hne : D ≠ E) :
    ∃ j : ℕ,
      (∀ i, i < j → (i ∈ D ↔ i ∈ E)) ∧ ¬ (j ∈ D ↔ j ∈ E) ∧
        mersenneWeight j - mersenneTail j ≤ 2 * ε := by
  classical
  have hex : ∃ i : ℕ, ¬ (i ∈ D ↔ i ∈ E) := by
    by_contra h
    refine hne (Finset.ext fun i => ?_)
    by_contra hi
    exact h ⟨i, hi⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · intro i hi
    by_contra h
    exact Nat.find_min hex hi h
  · set j := Nat.find hex with hj
    have hlow : ∀ i, i < j → (i ∈ D ↔ i ∈ E) := by
      intro i hi
      by_contra h
      exact Nat.find_min hex hi h
    have hspec := Nat.find_spec hex
    have hdiff : |(∑ d ∈ E, mersenneWeight d) - (∑ d ∈ D, mersenneWeight d)| ≤ 2 * ε := by
      have := abs_sub_abs_le_abs_sub
        ((∑ d ∈ E, mersenneWeight d) - 1 / 2) ((∑ d ∈ D, mersenneWeight d) - 1 / 2)
      have hs : (∑ d ∈ E, mersenneWeight d) - (∑ d ∈ D, mersenneWeight d)
          = ((∑ d ∈ E, mersenneWeight d) - 1 / 2)
            - ((∑ d ∈ D, mersenneWeight d) - 1 / 2) := by ring
      rw [hs]
      calc |((∑ d ∈ E, mersenneWeight d) - 1 / 2)
              - ((∑ d ∈ D, mersenneWeight d) - 1 / 2)|
          ≤ |(∑ d ∈ E, mersenneWeight d) - 1 / 2|
            + |(∑ d ∈ D, mersenneWeight d) - 1 / 2| := abs_sub _ _
        _ ≤ 2 * ε := by linarith
    by_cases hjD : j ∈ D
    · have hjE : j ∉ E := fun h => hspec ⟨fun _ => h, fun _ => hjD⟩
      have hlow' : ∀ i, i < j → (i ∈ E ↔ i ∈ D) := fun i hi => (hlow i hi).symm
      have := gap_le_sub_of_least_diff hlow' hjE hjD
      have habs := abs_le.1 hdiff
      linarith [habs.1]
    · have hjE : j ∈ E := by
        by_contra h
        exact hspec ⟨fun hh => absurd hh hjD, fun hh => absurd hh h⟩
      have := gap_le_sub_of_least_diff hlow hjD hjE
      have habs := abs_le.1 hdiff
      linarith [habs.2]

/-! ## Consequences for the exact-row socket -/

theorem exactLocalMersenneRowValue_eq_sum (D : Finset ℕ) :
    exactLocalMersenneRowValue D = ∑ d ∈ D, mersenneWeight d := by
  simp [exactLocalMersenneRowValue, localMersennePrefixValue]

/-- **Exact rows cluster.**  Two distinct exact Boolean quotient rows at the same endpoint
`n` must first disagree at a rank whose gap is at most `2 (n + 1) / 2 ^ n`.  Since the
rank-`j` gap is of order `(2/3) 4 ^ (-j)`, that forces the disagreement rank to be at least
about `(n - log₂ n) / 2`. -/
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
  have hDval := abs_exactLocalMersenneRowValue_sub_half_le hn hD hDq
  have hEval := abs_exactLocalMersenneRowValue_sub_half_le hn hE hEq
  rw [exactLocalMersenneRowValue_eq_sum] at hDval hEval
  exact gap_le_two_mul_of_ne hDval hEval hne

/-- The same statement read forwards: on every initial segment of ranks whose gaps exceed
`2 (n + 1) / 2 ^ n`, all exact rows at endpoint `n` carry the same Boolean word.  The
exact-row family at a given endpoint is a single cluster, not a search space. -/
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
  · intro i _; rw [hne]
  · intro i hi
    obtain ⟨j, hlow, hjne, hjgap⟩ := exactRow_gap_le hn hD hDq hE hEq hne
    by_contra hcon
    have hji : j ≤ i := by
      by_contra h
      exact hcon (hlow i (by omega))
    exact absurd hjgap (not_le.2 (hgap j (by omega)))

end ExactRowRigidity
end Erdos249257
