import ErdosProblems.Erdos257.PaperCompleteR20.SixMembershipConditions

/-!
Paper-form restatements of three asserted environments of the long Erdős #257
manuscript `paper/reasoning-parts/erdos257/a257_front.tex`:

* `lem:sqwitness` (line 8400) — at perfect-square depths the integer half carry
  of an achieving support equals the analytic tail, which is at most
  `2k + 4 = B(k²)`;
* `prop:cpgs-equiv` (line 8744) — the positivity conjunct of `CPGS` is
  unconditionally true, hence deletable, and what survives is exactly
  `(greedyMersenneSkippedSupport(1/2)).Infinite`, so `CPGS ⟺ HALF`;
* `prop:strip-equiv` (line 8766) — cofinal finite sets `D ⊆ {2,…,M}` with
  `|ihc(D, M−1)| ≤ 2⌊√M⌋ + 4` are the terminal-strip condition, are equivalent
  to `1/2 ∈ 𝒜`, and the relaxed constant `6` holds at every depth.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.HalfCarryReachability

/-! ## `lem:sqwitness` -/

/-- Long `lem:sqwitness`.  For `A` with `1 ∉ A` and `X_A(2) = 1/2`, at every
`k ≥ 1` the integer half carry at depth `k² − 1` equals the binary coefficient
tail at `k²`, which is at most `2k + 4`, and `B(k²) = 2k + 4` exactly. -/
theorem paper_square_depth_terminal_bound (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2) (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k ^ 2 - 1) : ℝ) = binaryCoeffTail (supportCoeff A) (k ^ 2) ∧
      binaryCoeffTail (supportCoeff A) (k ^ 2) ≤ 2 * (k : ℝ) + 4 ∧
      (halfStripBound (k ^ 2) : ℝ) = 2 * (k : ℝ) + 4 :=
  PaperCompleteR20.square_depth_witness A hone hhalf k hk

/-! ## `prop:cpgs-equiv` -/

/-- Long `prop:cpgs-equiv`, every asserted clause.

`CPGS` is written in the paper's own shape `∀ N, ∃ c ≥ N` with the positivity
conjunct `0 < r(1/2)(c−1)` and the skip condition `r(1/2)(c−1) < w_c`.  The
conjuncts below are: that shape agrees with the tree's
`CofinalPositiveHalfGreedySkips`; the positivity conjunct is unconditionally
true at every index; hence deleting it changes nothing; what survives is
exactly infinitude of the greedy skipped support; and therefore `CPGS ⟺ HALF`. -/
theorem paper_cpgs_equiv :
    ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
        0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
        greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
      ↔ CofinalPositiveHalfGreedySkips) ∧
      (∀ n : ℕ, 0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ ∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
            greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ (1 / 2 : ℝ) ∈ mersenneAchievementSet) := by
  have hpos : ∀ n : ℕ, 0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n :=
    greedyMersenneRemainderRat_half_pos
  have hshape : (∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
      ↔ CofinalPositiveHalfGreedySkips := by
    constructor
    · intro h N
      obtain ⟨c, hc, hp, hs⟩ := h (max N 4)
      exact ⟨c, hc, hp, hs⟩
    · intro h N
      obtain ⟨c, hc, hp, hs⟩ := h N
      exact ⟨c, (le_max_left N 4).trans hc, hp, hs⟩
  have hdrop : (∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
      ↔ ∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c := by
    constructor
    · intro h N
      obtain ⟨c, hc, -, hs⟩ := h N
      exact ⟨c, hc, hs⟩
    · intro h N
      obtain ⟨c, hc, hs⟩ := h N
      exact ⟨c, hc, hpos (c - 1), hs⟩
  have hhalf : (∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
      ↔ (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
    hshape.trans cofinalPositiveHalfGreedySkips_iff_half_mem
  refine ⟨hshape, hpos, hdrop, ?_, hhalf⟩
  exact hdrop.symm.trans
    (hhalf.trans half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite)

/-! ## `prop:strip-equiv` -/

private theorem real_sqrt_le_natSqrt_succ (M : ℕ) :
    Real.sqrt (M : ℝ) ≤ (Nat.sqrt M : ℝ) + 1 := by
  have hnat : M < (Nat.sqrt M + 1) * (Nat.sqrt M + 1) := Nat.lt_succ_sqrt M
  have hR : (M : ℝ) ≤ ((Nat.sqrt M : ℝ) + 1) ^ 2 := by
    have h : (M : ℝ) ≤ ((Nat.sqrt M : ℝ) + 1) * ((Nat.sqrt M : ℝ) + 1) := by
      exact_mod_cast hnat.le
    nlinarith [h]
  calc Real.sqrt (M : ℝ) ≤ Real.sqrt (((Nat.sqrt M : ℝ) + 1) ^ 2) :=
        Real.sqrt_le_sqrt hR
    _ = (Nat.sqrt M : ℝ) + 1 := Real.sqrt_sq (by positivity)

/-- Final clause of `prop:strip-equiv`: the relaxed constant `6` gives a bound
at *every* depth, via `√M ≤ ⌊√M⌋ + 1`.  It is not needed for the cofinal
statement, whose constant is `4`. -/
theorem paper_relaxed_constant_six_every_depth
    (A : Set ℕ) (hone : 1 ∉ A) (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (M : ℕ) (hM : 1 ≤ M) :
    |(integerHalfCarry A (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 6 := by
  have hi := integerHalfCarry_eq_scaled_residual_add_tail A hone (M - 1)
  rw [hvalue, sub_self, mul_zero, zero_add, Nat.sub_add_cancel hM] at hi
  have hnn := binaryCoeffTail_nonneg (supportCoeff A) M
  have hub := binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A M
  have hsq := real_sqrt_le_natSqrt_succ M
  rw [hi, abs_of_nonneg hnn]
  linarith

/-- Long `prop:strip-equiv`, the two equivalences.

Finite sets `D ⊆ {2,…,M}` at arbitrarily large depths `M` with
`|ihc(D, M−1)| ≤ 2⌊√M⌋ + 4` are exactly the terminal-strip condition
`HalfCarryCofinalTerminalOnlyStrip`, and that condition is equivalent to
`1/2 ∈ 𝒜`: constant `4` already suffices at cofinally many depths. -/
theorem paper_terminal_strip_equiv :
    ((∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ D : Finset ℕ,
        (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
        |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 4)
      ↔ HalfCarryCofinalTerminalOnlyStrip) ∧
      ((∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ D : Finset ℕ,
          (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
          |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 4)
        ↔ (1 / 2 : ℝ) ∈ mersenneAchievementSet) := by
  classical
  have hcast : ∀ M : ℕ, ((halfStripBound M : ℕ) : ℝ) = 2 * (Nat.sqrt M : ℝ) + 4 := by
    intro M
    unfold halfStripBound
    push_cast
    ring
  have hbridge : (∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ D : Finset ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
      |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 4)
      ↔ HalfCarryCofinalTerminalOnlyStrip := by
    constructor
    · intro hfin N
      obtain ⟨M, hM, D, hD, hcarry⟩ := hfin (max N 1)
      refine ⟨M, hM, fun i => decide (i.val ∈ D), ?_, ?_, ?_⟩
      · have h0 : (0 : ℕ) ∉ D := fun h => by have := (hD 0 h).1; omega
        simp [h0]
      · intro _
        have h1 : (1 : ℕ) ∉ D := fun h => by have := (hD 1 h).1; omega
        simp [h1]
      · have hsupp :
            wordSupport (fun i : Fin (M + 1) => decide (i.val ∈ D)) = (↑D : Set ℕ) := by
          ext m
          simp only [wordSupport, Set.mem_setOf_eq, Finset.mem_coe, decide_eq_true_eq]
          constructor
          · rintro ⟨-, hm⟩
            exact hm
          · intro hm
            exact ⟨by have := (hD m hm).2; omega, hm⟩
        rw [hsupp, hcast M]
        exact hcarry
    · intro hstrip N
      obtain ⟨M, hM, a, hzero, hone, hcarry⟩ := hstrip N
      refine ⟨M, (le_max_left N 1).trans hM,
        (Finset.range (M + 1)).filter (fun n => n ∈ wordSupport a), ?_, ?_⟩
      · intro d hd
        rw [Finset.mem_filter, Finset.mem_range] at hd
        obtain ⟨hdM, hdsupp⟩ := hd
        refine ⟨?_, by omega⟩
        rcases Nat.lt_or_ge d 2 with hlt | hge
        · interval_cases d
          · exact absurd hdsupp (zero_not_mem_wordSupport_of_terminalOnlyWitness hzero)
          · exact absurd hdsupp (one_not_mem_wordSupport_of_terminalOnlyWitness hone)
        · exact hge
      · have hcoe : (((Finset.range (M + 1)).filter
            (fun n => n ∈ wordSupport a) : Finset ℕ) : Set ℕ) = wordSupport a := by
          ext n
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
          constructor
          · rintro ⟨-, h⟩
            exact h
          · intro h
            obtain ⟨hn, hb⟩ := h
            exact ⟨hn, ⟨hn, hb⟩⟩
        rw [hcoe, ← hcast M]
        exact hcarry
  exact ⟨hbridge, hbridge.trans PaperCompleteR20.half_mem_iff_cofinal_terminal_strip.symm⟩

#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_square_depth_terminal_bound
#print axioms ErdosProblems.Erdos257.PaperCompleteR20.square_depth_witness
#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_cpgs_equiv
#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_relaxed_constant_six_every_depth
#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_equiv

end ErdosProblems.Erdos257.PaperCompleteR21
