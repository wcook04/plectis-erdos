import Erdos249257.SuffixCylinderProfiledAdjacency

/-!
# Carry-pivot normal form for numeral-adjacent boundary words

`SuffixCylinderProfiledAdjacency` proves the coarse bound: a binary
increment changes any divisor coefficient by at most one.  This module
replaces that inequality with the exact structure.  A pair of words whose
suffix numerals are consecutive differs in exactly one carry block: a
unique pivot rank `d` flips from unselected to selected, every strictly
deeper rank through the cutoff flips from selected to unselected, and
every shallower rank agrees.  The divisor-coefficient discrepancy at any
row is then an exact signed divisor-incidence identity, not merely a
`≤ +1` estimate.

The two core lemmas are deliberately stated at the set level, where
`supportSuffixNumeral` is a plain structural recursion, and transfer to
`HalfWord` boundary words in one line.  A stage-level corollary consumes
`ProfiledGapStage.HasAdjacentPrefixes` directly.

These are structural normal forms for the profiled two-sheet frontier.
They make no claim about the open problem statuses recorded in
`docs/RELATED_PROBLEMS.md`.

This module was derived and kernel-checked inside the agent workbench
(`docs/AGENT_WORKBENCH.md`); the session ledger is
`workbench/sessions/carry_pivot_2026_07_27/`.
-/

namespace Erdos249257.SuffixCylinderCarryPivot

open Erdos249257
open Erdos249257.FixedCoeffRewindPhase
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderInStrip
open Erdos249257.SuffixCylinderProfiledGap

/-- Equal zero-based suffix numerals force pointwise membership agreement
on every rank the numeral reads. -/
theorem mem_iff_of_supportSuffixNumeral_eq
    (A B : Set ℕ) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    ∀ N : ℕ, supportSuffixNumeral A 0 N = supportSuffixNumeral B 0 N →
      ∀ e, 1 ≤ e → e ≤ N → (e ∈ A ↔ e ∈ B) := by
  intro N
  induction N with
  | zero =>
      intro _ e he1 he2
      omega
  | succ N ih =>
      intro heq e he1 he2
      have hA' : (0 + N + 1 ∈ A) ↔ (N + 1 ∈ A) := by rw [Nat.zero_add]
      have hB' : (0 + N + 1 ∈ B) ↔ (N + 1 ∈ B) := by rw [Nat.zero_add]
      rw [supportSuffixNumeral, supportSuffixNumeral] at heq
      by_cases hA : (0 : ℕ) + N + 1 ∈ A
      · by_cases hB : (0 : ℕ) + N + 1 ∈ B
        · rw [if_pos hA, if_pos hB] at heq
          have hnum :
              supportSuffixNumeral A 0 N = supportSuffixNumeral B 0 N := by
            omega
          rcases Nat.lt_or_ge e (N + 1) with hlt | hge
          · exact ih hnum e he1 (by omega)
          · have hee : e = N + 1 := by omega
            subst hee
            exact ⟨fun _ => hB'.mp hB, fun _ => hA'.mp hA⟩
        · rw [if_pos hA, if_neg hB] at heq
          omega
      · by_cases hB : (0 : ℕ) + N + 1 ∈ B
        · rw [if_neg hA, if_pos hB] at heq
          omega
        · rw [if_neg hA, if_neg hB] at heq
          have hnum :
              supportSuffixNumeral A 0 N = supportSuffixNumeral B 0 N := by
            omega
          rcases Nat.lt_or_ge e (N + 1) with hlt | hge
          · exact ih hnum e he1 (by omega)
          · have hee : e = N + 1 := by omega
            subst hee
            constructor
            · intro h
              exact absurd (hA'.mpr h) hA
            · intro h
              exact absurd (hB'.mpr h) hB

/-- Set-level carry-pivot normal form: consecutive zero-based suffix
numerals decompose as one pivot rank entering `A`, a fully flipped deeper
block, and an agreeing shallow block. -/
theorem exists_carry_pivot_of_supportSuffixNumeral_succ
    (A B : Set ℕ) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    ∀ N : ℕ, supportSuffixNumeral A 0 N = supportSuffixNumeral B 0 N + 1 →
      ∃ d, 1 ≤ d ∧ d ≤ N ∧ d ∈ A ∧ d ∉ B ∧
        (∀ e, d < e → e ≤ N → (e ∉ A ∧ e ∈ B)) ∧
        (∀ e, 1 ≤ e → e < d → (e ∈ A ↔ e ∈ B)) := by
  intro N
  induction N with
  | zero =>
      intro heq
      simp [supportSuffixNumeral] at heq
  | succ N ih =>
      intro heq
      have hA' : (0 + N + 1 ∈ A) ↔ (N + 1 ∈ A) := by rw [Nat.zero_add]
      have hB' : (0 + N + 1 ∈ B) ↔ (N + 1 ∈ B) := by rw [Nat.zero_add]
      rw [supportSuffixNumeral, supportSuffixNumeral] at heq
      by_cases hA : (0 : ℕ) + N + 1 ∈ A
      · by_cases hB : (0 : ℕ) + N + 1 ∈ B
        · rw [if_pos hA, if_pos hB] at heq
          omega
        · rw [if_pos hA, if_neg hB] at heq
          have hnum :
              supportSuffixNumeral A 0 N = supportSuffixNumeral B 0 N := by
            omega
          refine ⟨N + 1, by omega, le_refl _, hA'.mp hA, ?_, ?_, ?_⟩
          · intro h
            exact hB (hB'.mpr h)
          · intro e he1 he2
            omega
          · intro e he1 he2
            exact mem_iff_of_supportSuffixNumeral_eq A B N hnum e he1
              (by omega)
      · by_cases hB : (0 : ℕ) + N + 1 ∈ B
        · rw [if_neg hA, if_pos hB] at heq
          have hnum :
              supportSuffixNumeral A 0 N =
                supportSuffixNumeral B 0 N + 1 := by
            omega
          obtain ⟨d, hd1, hdN, hdA, hdB, hdeep, hshallow⟩ := ih hnum
          refine ⟨d, hd1, by omega, hdA, hdB, ?_, hshallow⟩
          intro e hde heN
          rcases Nat.lt_or_ge e (N + 1) with hlt | hge
          · exact hdeep e hde (by omega)
          · have hee : e = N + 1 := by omega
            subst hee
            exact ⟨fun h => hA (hA'.mpr h), hB'.mp hB⟩
        · rw [if_neg hA, if_neg hB] at heq
          omega

/-- Word-level carry-pivot normal form for numeral-adjacent boundary
words: the entire difference between the two literal supports is one
positive pivot with a completely flipped deeper suffix. -/
theorem exists_carry_pivot_of_wordSuffixNumeral_succ
    {N : ℕ} (lower upper : HalfWord N)
    (hsucc : wordSuffixNumeral lower 0 N = wordSuffixNumeral upper 0 N + 1) :
    ∃ d, 1 ≤ d ∧ d ≤ N ∧
      d ∈ wordSupport lower ∧ d ∉ wordSupport upper ∧
      (∀ e, d < e → e ≤ N →
        (e ∉ wordSupport lower ∧ e ∈ wordSupport upper)) ∧
      (∀ e, 1 ≤ e → e < d →
        (e ∈ wordSupport lower ↔ e ∈ wordSupport upper)) := by
  classical
  exact exists_carry_pivot_of_supportSuffixNumeral_succ
    (wordSupport lower) (wordSupport upper) N hsucc

private theorem mem_wordSupport_le {N : ℕ} {a : HalfWord N} {e : ℕ}
    (he : e ∈ wordSupport a) : e ≤ N := by
  obtain ⟨h, -⟩ := he
  omega

/-- Exact divisor-incidence cocycle: under a carry-pivot decomposition,
the coefficient discrepancy at row `m` is determined by whether the pivot
divides `m` against how many deeper ranks through the cutoff divide `m`.
This sharpens the coarse `≤ +1` adjacency bound into an equality. -/
theorem supportCoeff_add_deepDivisorCount_eq_of_carry_pivot
    {N : ℕ} (lower upper : HalfWord N) (m d : ℕ)
    (hlow : d ∈ wordSupport lower) (hup : d ∉ wordSupport upper)
    (habove : ∀ e, d < e → e ≤ N →
      (e ∉ wordSupport lower ∧ e ∈ wordSupport upper))
    (hbelow : ∀ e, 1 ≤ e → e < d →
      (e ∈ wordSupport lower ↔ e ∈ wordSupport upper)) :
    supportCoeff (wordSupport lower) m +
        ((m.divisors).filter (fun e => d < e ∧ e ≤ N)).card =
      supportCoeff (wordSupport upper) m +
        (if d ∈ m.divisors then 1 else 0) := by
  classical
  have hLc : supportCoeff (wordSupport lower) m
      = (m.divisors.filter fun e => e ∈ wordSupport lower).card :=
    supportCoeff_eq_card_filter _ _
  have hUc : supportCoeff (wordSupport upper) m
      = (m.divisors.filter fun e => e ∈ wordSupport upper).card :=
    supportCoeff_eq_card_filter _ _
  have hPiv : (if d ∈ m.divisors then 1 else 0)
      = (m.divisors.filter fun e => e = d).card := by
    rw [Finset.filter_eq']
    by_cases hdm : d ∈ m.divisors <;> simp [hdm]
  have hdisjL :
      Disjoint (m.divisors.filter fun e => e ∈ wordSupport lower)
        (m.divisors.filter fun e => d < e ∧ e ≤ N) := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_filter] at he he'
    exact (habove e he'.2.1 he'.2.2).1 he.2
  have hdisjU :
      Disjoint (m.divisors.filter fun e => e ∈ wordSupport upper)
        (m.divisors.filter fun e => e = d) := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_filter] at he he'
    rw [he'.2] at he
    exact hup he.2
  have hunion :
      (m.divisors.filter fun e => e ∈ wordSupport lower) ∪
          (m.divisors.filter fun e => d < e ∧ e ≤ N)
        = (m.divisors.filter fun e => e ∈ wordSupport upper) ∪
          (m.divisors.filter fun e => e = d) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hes, hel⟩ | ⟨hes, hgt, hle⟩)
      · rcases lt_trichotomy e d with h | h | h
        · exact Or.inl
            ⟨hes, (hbelow e (Nat.pos_of_mem_divisors hes) h).1 hel⟩
        · exact Or.inr ⟨hes, h⟩
        · exact absurd hel (habove e h (mem_wordSupport_le hel)).1
      · exact Or.inl ⟨hes, (habove e hgt hle).2⟩
    · rintro (⟨hes, heu⟩ | ⟨hes, rfl⟩)
      · rcases lt_trichotomy e d with h | h | h
        · exact Or.inl
            ⟨hes, (hbelow e (Nat.pos_of_mem_divisors hes) h).2 heu⟩
        · subst h
          exact absurd heu hup
        · exact Or.inr ⟨hes, h, mem_wordSupport_le heu⟩
      · exact Or.inl ⟨hes, hlow⟩
  rw [hLc, hUc, hPiv, ← Finset.card_union_of_disjoint hdisjL,
    ← Finset.card_union_of_disjoint hdisjU, hunion]

/-- Stage form: adjacent profiled prefixes carry a unique boundary carry
pivot through the profiled cutoff. -/
theorem profiledGapStage_carry_pivot_of_hasAdjacentPrefixes
    {M N : ℕ} (T : ProfiledGapStage M N)
    (hadjacent : T.HasAdjacentPrefixes) :
    ∃ d, 1 ≤ d ∧ d ≤ M ∧
      d ∈ wordSupport T.lowerPrefix ∧ d ∉ wordSupport T.upperPrefix ∧
      (∀ e, d < e → e ≤ M →
        (e ∉ wordSupport T.lowerPrefix ∧ e ∈ wordSupport T.upperPrefix)) ∧
      (∀ e, 1 ≤ e → e < d →
        (e ∈ wordSupport T.lowerPrefix ↔ e ∈ wordSupport T.upperPrefix)) :=
  exists_carry_pivot_of_wordSuffixNumeral_succ
    T.lowerPrefix T.upperPrefix hadjacent

#print axioms mem_iff_of_supportSuffixNumeral_eq
#print axioms exists_carry_pivot_of_supportSuffixNumeral_succ
#print axioms exists_carry_pivot_of_wordSuffixNumeral_succ
#print axioms supportCoeff_add_deepDivisorCount_eq_of_carry_pivot
#print axioms profiledGapStage_carry_pivot_of_hasAdjacentPrefixes

end Erdos249257.SuffixCylinderCarryPivot
