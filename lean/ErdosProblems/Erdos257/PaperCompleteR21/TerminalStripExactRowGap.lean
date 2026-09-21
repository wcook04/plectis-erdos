import Erdos249257.TerminalOnlyCofinal
import Erdos249257.BooleanMobiusCriticalCapacityCofinal
import Erdos249257.DyadicPrefixCompression
import ErdosProblems.Erdos257.PaperCompleteR20.SixMembershipConditions

/-!
Paper-form restatement of the whole asserted environment

* `record:257rig-c17` (`paper/reasoning-parts/erdos257/a257_front.tex:4325`),
  "Terminal bounds at unbounded depths".

The environment carries four mathematical assertions:

1. the displayed implication: a cofinal supply of finite supports
   `D ⊆ {2,…,M}` with `|ihc(D,M-1)| ≤ B(M) = 2⌊√M⌋ + 4` produces an infinite
   `A ⊆ ℕ_{≥1}` with `X_A(2) = 1/2`
   (`paper_terminal_strip_forces_half_membership`);
2. the finite-support identity `ihc(D,M-1) = 2^(M-1) - Q(D,M)`
   (`paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient`);
3. its consequence that an exact row `Q(D,M) = 2^(M-1) - 1` has carry `1`
   (`paper_exact_row_integerHalfCarry_eq_one`);
4. the `M = 6` witness `D = {2,3}` with `Q(D,6) = 30` and carry `2`, which
   satisfies the terminal bound and is not an exact row
   (`paper_terminal_strip_witness_six`);
5. the closing cross-reference to Proposition `prop:collapsed-list`, that both
   cofinal existence statements are equivalent to half-membership
   (`paper_both_cofinal_statements_iff_half_membership`).

Paper notation: `B(m) = halfStripBound m`, `ihc(D,N) = integerHalfCarry ↑D N`,
`Q(D,M) = localPrefixQuotient D M = ∑_{d ∈ D} ⌊2^M/(2^d-1)⌋`,
`X_A(2) = erdosSupportSeries 2 A`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.HalfCarryReachability

/-! ## The displayed implication -/

/-- Paper display of `record:257rig-c17`: if for every `N ≥ 0` there are
`M ≥ max{N,1}` and `D ⊆ {2,…,M}` with `|ihc(D,M-1)| ≤ B(M) = 2⌊√M⌋+4`, then
some infinite `A ⊆ ℕ_{≥1}` satisfies `X_A(2) = 1/2`.  No compatibility between
the different finite supports is required. -/
theorem paper_terminal_strip_forces_half_membership
    (hcofinal : ∀ N : ℕ, ∃ M : ℕ, max N 1 ≤ M ∧ ∃ D : Finset ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
      |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ (halfStripBound M : ℝ)) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  classical
  have hstrip : HalfCarryCofinalTerminalOnlyStrip := by
    intro N
    obtain ⟨M, hM, D, hD, hcarry⟩ := hcofinal N
    refine ⟨M, hM, fun i ↦ decide (i.val ∈ D), ?_, ?_, ?_⟩
    · have h0 : (0 : ℕ) ∉ D := fun h ↦ by have := (hD 0 h).1; omega
      simp [h0]
    · intro _
      have h1 : (1 : ℕ) ∉ D := fun h ↦ by have := (hD 1 h).1; omega
      simp [h1]
    · have hsupp :
          wordSupport (fun i : Fin (M + 1) ↦ decide (i.val ∈ D)) = (↑D : Set ℕ) := by
        ext m
        simp only [wordSupport, Set.mem_setOf_eq, Finset.mem_coe, decide_eq_true_eq]
        constructor
        · rintro ⟨_, hm⟩
          exact hm
        · intro hm
          exact ⟨by have := (hD m hm).2; omega, hm⟩
      rw [hsupp]
      exact hcarry
  obtain ⟨A, hA0, hvalue⟩ :=
    half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip hstrip
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue.symm
  exact ⟨A, fun hfinite ↦ finite_boolSupport_ne_half A hfinite hA0 hseries,
    hA0, hseries⟩

/-! ## The finite-support carry identity and the exact-row gap -/

/-- The environment's displayed identity for a finite support: for `M ≥ 1` and
`D ⊆ {2,3,…}`,

`ihc(D, M-1) = 2^(M-1) - Q(D,M)`.

The Möbius-centred carry of a finite support is its signed endpoint defect
`halfEndpointTarget M - Q(D,M) = (2^(M-1) - 1) - Q(D,M)`, and the integer
half-carry is that centred carry plus one. -/
theorem paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) =
      (2 : ℤ) ^ (M - 1) - (localPrefixQuotient D M : ℤ) := by
  have h := mobiusCenteredHalfCarry_coe_finset_eq_localEndpointDefect hD (M - 1)
  rw [show M - 1 + 1 = M from by omega] at h
  have hpow : (1 : ℕ) ≤ 2 ^ (M - 1) := Nat.one_le_pow _ _ (by norm_num)
  have htarget : ((halfEndpointTarget M : ℕ) : ℤ) = (2 : ℤ) ^ (M - 1) - 1 := by
    unfold halfEndpointTarget
    rw [Nat.cast_sub hpow]
    push_cast
    ring
  unfold mobiusCenteredHalfCarry localEndpointDefect at h
  rw [htarget] at h
  linarith

/-- The environment's consequence: an exact row, `Q(D,M) = 2^(M-1) - 1` in the
sense of Definition `record:257bm-d4`, has carry exactly `1`. -/
theorem paper_exact_row_integerHalfCarry_eq_one
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hexact : localPrefixQuotient D M = 2 ^ (M - 1) - 1) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) = 1 := by
  have hpow : (1 : ℕ) ≤ 2 ^ (M - 1) := Nat.one_le_pow _ _ (by norm_num)
  have h := paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient hM hD
  rw [hexact, Nat.cast_sub hpow] at h
  push_cast at h
  linarith

/-! ## The `M = 6` witness -/

/-- The environment's worked instance.  At `M = 6` the support `D = {2,3}`
lies in `{2,…,6}`, has `Q(D,6) = 30` and carry `ihc(D,5) = 2`; the carry
satisfies the terminal bound `|ihc(D,5)| ≤ B(6) = 8`, and `D` is not an exact
row because `Q(D,6) ≠ 2^5 - 1 = 31`. -/
theorem paper_terminal_strip_witness_six :
    (∀ d ∈ ({2, 3} : Finset ℕ), 2 ≤ d ∧ d ≤ 6) ∧
      localPrefixQuotient ({2, 3} : Finset ℕ) 6 = 30 ∧
      integerHalfCarry (↑({2, 3} : Finset ℕ) : Set ℕ) (6 - 1) = 2 ∧
      |(integerHalfCarry (↑({2, 3} : Finset ℕ) : Set ℕ) (6 - 1) : ℝ)| ≤
        (halfStripBound 6 : ℝ) ∧
      localPrefixQuotient ({2, 3} : Finset ℕ) 6 ≠ 2 ^ (6 - 1) - 1 := by
  have hrange : ∀ d ∈ ({2, 3} : Finset ℕ), 2 ≤ d ∧ d ≤ 6 := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> norm_num
  have hD : ∀ d ∈ ({2, 3} : Finset ℕ), 2 ≤ d := fun d hd ↦ (hrange d hd).1
  have hQ : localPrefixQuotient ({2, 3} : Finset ℕ) 6 = 30 := by
    rw [localPrefixQuotient, Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3)]
    norm_num [localMersenneQuotient]
  have hcarry : integerHalfCarry (↑({2, 3} : Finset ℕ) : Set ℕ) (6 - 1) = 2 := by
    have h := paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient
      (D := ({2, 3} : Finset ℕ)) (M := 6) (by norm_num) hD
    rw [hQ] at h
    rw [h]
    norm_num
  have hsqrt : Nat.sqrt 6 = 2 := by
    have h1 : 2 ≤ Nat.sqrt 6 := Nat.le_sqrt.mpr (by norm_num)
    have h2 : Nat.sqrt 6 < 3 := Nat.sqrt_lt.mpr (by norm_num)
    omega
  refine ⟨hrange, hQ, hcarry, ?_, ?_⟩
  · rw [hcarry]
    simp only [halfStripBound, hsqrt]
    norm_num
  · rw [hQ]
    norm_num

/-! ## The closing cross-reference -/

/-- The environment's closing sentence: both cofinal existence statements —
the exact-row condition of Definition `record:257bm-d4` and the terminal-strip
condition displayed here — imply and are implied by half-membership.  This is
the content of Proposition `prop:collapsed-list`, items (c) and (e). -/
theorem paper_both_cofinal_statements_iff_half_membership :
    ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ CofinalExactLocalMersenneHalfRows) ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ HalfCarryCofinalTerminalOnlyStrip) :=
  ⟨ErdosProblems.Erdos257.PaperCompleteR20.half_mem_iff_cofinal_exact_rows,
    ErdosProblems.Erdos257.PaperCompleteR20.half_mem_iff_cofinal_terminal_strip⟩

#print axioms paper_terminal_strip_forces_half_membership
#print axioms paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient
#print axioms paper_exact_row_integerHalfCarry_eq_one
#print axioms paper_terminal_strip_witness_six
#print axioms paper_both_cofinal_statements_iff_half_membership

end ErdosProblems.Erdos257.PaperCompleteR21
