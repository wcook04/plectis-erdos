import ErdosProblems.Rem.C6

/-!
# T1 — the C6 residual invariant is FALSE, and no interval induction can replace it

The brief for this file was:

> `ErdosProblems/Rem/C6.lean` reports the invariant "residual after rank `d` is
> `< 2 ^ (2 * s - d)`" as empirically TRUE with max ratio `0.99989`, and that it
> would give `ρ s < 2 ^ (s + 1)` outright, but its induction does not close.
> Close it.

It cannot be closed.  **The invariant is false.**  This file proves that, and
then proves that the failure is structural rather than incidental: no ceiling
family whatsoever propagates through the rank recursion by one-step interval
induction and reaches `2 ^ (s + 1)`; every such family is `Ω(4 ^ s)`.

Contents.

* §1  `seamResidual` / `seamResidualUpto` — the residual of the descending seam
  greedy of row `s` after the ranks `2, …, d` have been offered — together with
  `seamResidualUpto_last`, which identifies the residual after the final rank
  `s - 1` with the corpus's `seamIntegerGreedyRemainder s`.  So the object
  studied here really is C6's object.
* §2  `ResidualInvariant`, C6's statement verbatim, and **`not_residualInvariant`**:
  it fails at `s = 13`, `d = 7`, where the residual is `524419` and
  `2 ^ (2 * 13 - 7) = 524288`.  The row is not degenerate — `s = 13` is well
  inside the range C6 reports as tested, and `ρ 13 = 15147 < 2 ^ 14`, so the
  *conclusion* survives at that row while the invariant does not.
* §3  Why: `residual_lt_of_taken` shows the *taken* branch of the step closes
  cleanly, and `invariant_step_dichotomy` shows the only way the step can fail
  is the *declined* branch with the residual inside the tangency window
  `[2 ^ (2 * s - d - 1), truncatedMersenneWeight s (d + 1))`.
  `tangency_window_thirteen` exhibits that window being entered.
* §4  The no-go.  `IntervalCeiling s` is the class of ceiling families that
  propagate through the greedy step law using nothing but the step law: exactly
  the class C6's induction lives in.
  - `intervalCeiling_obligations_iff`: the class is characterised, not merely
    illustrated — its two obligations are *equivalent* to "the step carries
    `[0, bound d)` into `[0, bound (d+1))` for every residual value".
  - `IntervalCeiling.sound`: the obligations do bound the true residual.
  - `trivialCeiling`: the class is inhabited.
  - `IntervalCeiling.four_pow_le`: every member satisfies
    `4 ^ s ≤ 105 * bound (s - 1) + 90`.  Hence
    `IntervalCeiling.two_pow_lt`: `2 ^ (s + 1) < bound (s - 1)` for `s ≥ 8`, and
    `IntervalCeiling.no_better_than_trivial`: the trivial ceiling
    `2 ^ (2 * s - 1) - 2 ^ s` cannot be beaten by more than the factor `105 / 2`.
  - `declined_floor_terminal` / `start_lt_of_terminal_lt`: starting the induction
    at a later rank does not help — `min (B a) (2 ^ (s+1) + 4) ≤ B (s - 1)`, so an
    interval induction can transport a bound along the rank recursion but never
    produce one.

  This is C1's `le_of_descent_of_quadrupling` phenomenon one level down, at the
  rank recursion instead of the row recursion.
* §5  What survives: the ceiling that *is* correct is the weight itself,
  `seamResidualUpto s d < truncatedMersenneWeight s d`.  `WeightCeilingAt` names
  it, `weightCeiling_thirteen` proves it at the very row that refutes C6, and
  `remainder_lt_of_weightCeiling` shows it yields `ρ s < 2 ^ (s + 1) + 4`.  It is
  MEASURED, not proved, and by §4 it is not provable by interval induction
  either (`weightCeiling_not_intervalCeiling`).  `weight_satisfies_declined` and
  `weight_fails_taken` localise the failure to the *taken* obligation alone.

Anti-vacuity.  Every theorem with a non-trivial hypothesis has a companion
exhibiting the hypothesis holding: `trivialCeiling` and
`trivialCeiling_two_pow_lt` for `IntervalCeiling`; `weight_satisfies_declined`
and `declined_floor_terminal_weight` for `declined_floor_terminal`;
`weightCeiling_thirteen` for `remainder_lt_of_weightCeiling`;
`tangency_window_thirteen` for the second disjunct of
`invariant_step_dichotomy`; `residualInvariant_twelve` and
`residualInvariant_fourteen` to show `ResidualInvariant` is not a misstatement
that fails everywhere.  The only statement in the file that is asserted without
proof is `WeightCeilingAt` for general `s`, and it is labelled MEASURED
throughout.
-/

namespace ErdosProblems.Three.T1

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy

/-! ## 1. The rank-indexed residual of the descending seam greedy -/

/-- `seamResidual s k` is the capacity left after the descending seam greedy of
row `s` has offered the first `k` ranks, namely `2, 3, …, k + 1`. -/
def seamResidual (s : ℕ) : ℕ → ℕ
  | 0 => seamSubsetTarget s
  | k + 1 =>
      if truncatedMersenneWeight s (k + 2) ≤ seamResidual s k then
        seamResidual s k - truncatedMersenneWeight s (k + 2)
      else
        seamResidual s k

/-- `seamResidualUpto s d` is the residual after the ranks `2, …, d` have been
offered.  (`seamResidualUpto s 1 = seamSubsetTarget s`: nothing offered yet.) -/
def seamResidualUpto (s d : ℕ) : ℕ := seamResidual s (d - 1)

theorem seamResidualUpto_one (s : ℕ) : seamResidualUpto s 1 = seamSubsetTarget s := rfl

/-- One rank of the descending greedy, indexed by the rank. -/
theorem seamResidualUpto_succ {s d : ℕ} (hd : 1 ≤ d) :
    seamResidualUpto s (d + 1) =
      if truncatedMersenneWeight s (d + 1) ≤ seamResidualUpto s d then
        seamResidualUpto s d - truncatedMersenneWeight s (d + 1)
      else
        seamResidualUpto s d := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  simp only [seamResidualUpto, Nat.add_sub_cancel, seamResidual]

/-- The greedy never increases the residual. -/
theorem seamResidualUpto_succ_le {s d : ℕ} (hd : 1 ≤ d) :
    seamResidualUpto s (d + 1) ≤ seamResidualUpto s d := by
  rw [seamResidualUpto_succ hd]
  split <;> omega

/-- Running the corpus greedy from the rank-`k+2` suffix, started at the
residual left by the first `k` ranks, is the same as running it from the top. -/
theorem integerGreedyRemainder_seamWeightsFrom (s : ℕ) :
    ∀ k, k + 2 ≤ s →
      integerGreedyRemainder (seamWeightsFrom s (k + 2)) (seamResidual s k)
        = seamIntegerGreedyRemainder s := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hlt : k + 2 < s := by omega
      have := ih (by omega)
      rw [seamWeightsFrom_eq_cons hlt, RemC6.integerGreedyRemainder_cons] at this
      simpa only [seamResidual, show k + 1 + 2 = k + 2 + 1 by omega] using this

/-- **The residual after the final rank `s - 1` is the corpus remainder.**  This
is what makes `seamResidualUpto` the right object: at `d = s - 1` it *is*
`ρ s = seamIntegerGreedyRemainder s`. -/
theorem seamResidualUpto_last {s : ℕ} (hs : 2 ≤ s) :
    seamResidualUpto s (s - 1) = seamIntegerGreedyRemainder s := by
  have h := integerGreedyRemainder_seamWeightsFrom s (s - 2) (by omega)
  rw [show s - 2 + 2 = s by omega, seamWeightsFrom_eq_nil (le_refl s)] at h
  simpa only [seamResidualUpto, show s - 1 - 1 = s - 2 by omega,
    RemC6.integerGreedyRemainder_nil] using h

/-! ## 2. C6's residual invariant, and its refutation -/

/-- **C6's invariant, verbatim.**  From the measurement note of
`ErdosProblems/Rem/C6.lean`: "the residual after rank `d` has been offered stays
strictly below `2 ^ (2 * s - d)` — the top bit of the rank-`d` weight — at every
`d` and every `s` tested (maximal observed ratio `0.99989`)"; and "At `d = s - 1`
that is exactly `ρ s < 2 ^ (s + 1)`".

Row `5` is excluded, because it is the corpus's known degenerate row
(`ρ 5 = 71 > 2 ^ 6`); the refutation below does not need it. -/
def ResidualInvariant : Prop :=
  ∀ s d : ℕ, 6 ≤ s → 2 ≤ d → d < s → seamResidualUpto s d < 2 ^ (2 * s - d)

/-- The residual of row `13` after ranks `2, …, 7` have been offered. -/
theorem seamResidualUpto_thirteen_seven : seamResidualUpto 13 7 = 524419 := by
  norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- **The refutation.**  At `s = 13`, `d = 7` the residual is `524419` while
`2 ^ (2 * 13 - 7) = 2 ^ 19 = 524288`.  The invariant is false. -/
theorem not_residualInvariant : ¬ ResidualInvariant := by
  intro h
  have := h 13 7 (by norm_num) (by norm_num) (by norm_num)
  rw [seamResidualUpto_thirteen_seven] at this
  norm_num at this

/-- The failure is by `131`, against a bound of `524288`: a relative overshoot of
about `2.5 · 10⁻⁴`.  C6's reported maximum ratio was `0.99989`; the true ratio at
this row is `> 1`. -/
theorem residual_thirteen_seven_exceeds :
    2 ^ (2 * 13 - 7) + 131 = seamResidualUpto 13 7 := by
  rw [seamResidualUpto_thirteen_seven]; norm_num

/-! ### The refuting row is not degenerate

`ρ 13 = 15147`, so `ρ 13 < 2 ^ 14 = 2 ^ (13 + 1)`: the *conclusion* C6 wanted to
extract from the invariant is true at the very row where the invariant fails.
The invariant is a false route to a (measured) true statement, not a symptom of
the statement being false. -/

theorem seamIntegerGreedyRemainder_thirteen : seamIntegerGreedyRemainder 13 = 15147 := by
  rw [← seamResidualUpto_last (s := 13) (by norm_num)]
  norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

theorem seamIntegerGreedyRemainder_thirteen_lt : seamIntegerGreedyRemainder 13 < 2 ^ (13 + 1) := by
  rw [seamIntegerGreedyRemainder_thirteen]; norm_num

/-- Row `13` is a *miss* for the half point (`ρ 13 > 2 ^ 13`), so it is a genuine
row of the hard kind, not a hit that could be dismissed. -/
theorem seamIntegerGreedyRemainder_thirteen_gt : 2 ^ 13 < seamIntegerGreedyRemainder 13 := by
  rw [seamIntegerGreedyRemainder_thirteen]; norm_num

/-! ## 3. Exactly which step fails, and why

The brief asked for the precise step at which C6's induction breaks.  It is the
*declined* branch, and the break is a tangency, not a slack: the taken branch
closes with room to spare, while the declined branch closes only up to the low
bits of the next weight. -/

/-- **The taken branch closes.**  This half of C6's induction is fine: if rank
`d + 1` is accepted, halving the ceiling is exactly paid for by the top bit of
the accepted weight. -/
theorem residual_lt_of_taken {s d : ℕ} (hd : 1 ≤ d) (hds : d + 1 ≤ 2 * s)
    (htaken : truncatedMersenneWeight s (d + 1) ≤ seamResidualUpto s d)
    (h : seamResidualUpto s d < 2 ^ (2 * s - d)) :
    seamResidualUpto s (d + 1) < 2 ^ (2 * s - (d + 1)) := by
  have hw := RemC6.two_pow_le_truncatedMersenneWeight (s := s) (d := d + 1) (by omega) hds
  have hdbl : (2 : ℕ) ^ (2 * s - d) = 2 ^ (2 * s - (d + 1)) + 2 ^ (2 * s - (d + 1)) := by
    rw [show 2 * s - d = (2 * s - (d + 1)) + 1 by omega, pow_succ]; ring
  rw [seamResidualUpto_succ hd, if_pos htaken]
  omega

/-- **The declined branch closes only up to the low bits of the weight.**  If
rank `d + 1` is refused, the residual is trapped below the *whole* rank-`d+1`
weight, which exceeds the halved ceiling `2 ^ (2 * s - d - 1)` by its remaining
bits.  That excess is the entire gap in C6's induction. -/
theorem residual_lt_of_declined {s d : ℕ} (hd : 1 ≤ d) (hds : d + 1 ≤ s)
    (hdecl : seamResidualUpto s d < truncatedMersenneWeight s (d + 1)) :
    seamResidualUpto s (d + 1)
      < 2 ^ (2 * s - (d + 1)) + 2 ^ (2 * s - 2 * (d + 1) + 1) := by
  have hup := RemC6.truncatedMersenneWeight_le (s := s) (d := d + 1) (by omega) hds
  rw [seamResidualUpto_succ hd, if_neg (not_le.mpr hdecl)]
  omega

/-- **The dichotomy.**  Given the invariant at rank `d`, either it propagates to
rank `d + 1`, or the residual sits in the tangency window
`[2 ^ (2 * s - d - 1), truncatedMersenneWeight s (d + 1))` — a window of width
strictly less than `2 ^ (2 * s - 2 * d - 1)`, i.e. a `2 ^ (-d)` fraction of the
ceiling.  No induction can close without excluding that window, and the window
is *not* empty: see `tangency_window_thirteen`. -/
theorem invariant_step_dichotomy {s d : ℕ} (hd : 1 ≤ d) (hds : d + 1 ≤ 2 * s)
    (h : seamResidualUpto s d < 2 ^ (2 * s - d)) :
    seamResidualUpto s (d + 1) < 2 ^ (2 * s - (d + 1)) ∨
      (2 ^ (2 * s - (d + 1)) ≤ seamResidualUpto s d ∧
        seamResidualUpto s d < truncatedMersenneWeight s (d + 1)) := by
  by_cases htaken : truncatedMersenneWeight s (d + 1) ≤ seamResidualUpto s d
  · exact Or.inl (residual_lt_of_taken hd hds htaken h)
  · rw [not_le] at htaken
    by_cases hsmall : seamResidualUpto s d < 2 ^ (2 * s - (d + 1))
    · refine Or.inl ?_
      rw [seamResidualUpto_succ hd, if_neg (not_le.mpr htaken)]
      exact hsmall
    · exact Or.inr ⟨by omega, htaken⟩

/-- The residual of row `13` after ranks `2, …, 6` have been offered. -/
theorem seamResidualUpto_thirteen_six : seamResidualUpto 13 6 = 524419 := by
  norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- **The tangency window is entered.**  At `s = 13`, `d = 6` the residual
`524419` lies in `[2 ^ 19, truncatedMersenneWeight 13 7) = [524288, 528416)`, so
the second disjunct of `invariant_step_dichotomy` genuinely occurs; rank `7` is
declined and the invariant is destroyed at rank `7`.  The window has width
`4128` out of a ceiling of `524288`. -/
theorem tangency_window_thirteen :
    2 ^ (2 * 13 - (6 + 1)) ≤ seamResidualUpto 13 6 ∧
      seamResidualUpto 13 6 < truncatedMersenneWeight 13 7 := by
  rw [seamResidualUpto_thirteen_six]
  refine ⟨by norm_num, ?_⟩
  norm_num [truncatedMersenneWeight]

/-! ### The invariant is not misstated: it holds at the neighbouring rows

If `ResidualInvariant` were false for a bookkeeping reason it would fail
everywhere.  It does not: rows `12` and `14` satisfy it at every rank.  Row `13`
is a genuine, isolated tangency. -/

theorem residualInvariant_twelve :
    ∀ d : ℕ, 2 ≤ d → d < 12 → seamResidualUpto 12 d < 2 ^ (2 * 12 - d) := by
  intro d h2 h12
  interval_cases d <;>
    norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

theorem residualInvariant_fourteen :
    ∀ d : ℕ, 2 ≤ d → d < 14 → seamResidualUpto 14 d < 2 ^ (2 * 14 - d) := by
  intro d h2 h14
  interval_cases d <;>
    norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- Same instance, phrased as the invariant holding at rank `6` and failing at
rank `7`: the break is a single step, not an accumulation. -/
theorem invariant_holds_at_six_fails_at_seven :
    seamResidualUpto 13 6 < 2 ^ (2 * 13 - 6) ∧
      ¬ seamResidualUpto 13 7 < 2 ^ (2 * 13 - 7) := by
  rw [seamResidualUpto_thirteen_six, seamResidualUpto_thirteen_seven]
  constructor <;> norm_num

/-! ## 4. The no-go: interval induction cannot reach `2 ^ (s + 1)`

C6's induction is an *interval* induction: it carries a ceiling `B d` depending
only on the row and the rank, and asks it to propagate through the greedy step
law without knowing which branch the step actually takes.  §3 shows that
particular ceiling fails.  This section shows that **no** ceiling in that class
succeeds, and by a wide margin: every one of them is `Ω(4 ^ s)`, so the whole
class is stuck within a constant factor of the trivial ceiling
`seamSubsetTarget s = 2 ^ (2 * s - 1) - 2 ^ s`.

This is the rank-recursion analogue of C1's `le_of_descent_of_quadrupling`. -/

private theorem four_pow_eq' (s : ℕ) : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]

private theorem two_mul_seamSubsetTarget {s : ℕ} (hs : 1 ≤ s) :
    2 * seamSubsetTarget s + 2 * 2 ^ s = 4 ^ s := by
  have h1 : (2 : ℕ) ^ s ≤ 2 ^ (2 * s - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℕ) ^ (2 * s - 1) * 2 = 4 ^ s := by
    rw [← pow_succ, show 2 * s - 1 + 1 = 2 * s by omega, pow_mul]; norm_num
  show 2 * (2 ^ (2 * s - 1) - 2 ^ s) + 2 * 2 ^ s = 4 ^ s
  omega

private theorem two_pow_le_of_le {k s : ℕ} (h : k ≤ s) : (2 : ℕ) ^ k ≤ 2 ^ s :=
  Nat.pow_le_pow_right (by norm_num) h

/-- Rank `2` is always accepted, for every row `s ≥ 3`. -/
theorem weight_two_le_target {s : ℕ} (hs : 3 ≤ s) :
    truncatedMersenneWeight s 2 ≤ seamSubsetTarget s := by
  have hkey : 6 * 2 ^ s ≤ 4 ^ s := by
    rw [four_pow_eq']
    exact Nat.mul_le_mul_right _ (le_trans (by norm_num) (two_pow_le_of_le hs))
  have h2C := two_mul_seamSubsetTarget (s := s) (by omega)
  have hw2 : truncatedMersenneWeight s 2 = 4 ^ s / 3 := by norm_num [truncatedMersenneWeight]
  have hd := Nat.div_add_mod (4 ^ s) 3
  have hd' : 4 ^ s % 3 < 3 := Nat.mod_lt _ (by norm_num)
  omega

theorem seamResidualUpto_two {s : ℕ} (hs : 3 ≤ s) :
    seamResidualUpto s 2 = seamSubsetTarget s - truncatedMersenneWeight s 2 := by
  simp only [seamResidualUpto, seamResidual]
  rw [if_pos (weight_two_le_target hs)]

/-- Rank `3` is always accepted too — equivalently, the residual after rank `2`
still dominates the rank-`3` weight — for every row `s ≥ 6`.  This is what
forces any interval ceiling to be at least `truncatedMersenneWeight s 3`. -/
theorem weight_three_le_residual {s : ℕ} (hs : 6 ≤ s) :
    truncatedMersenneWeight s 3 ≤ seamResidualUpto s 2 := by
  have hkey : 42 * 2 ^ s ≤ 4 ^ s := by
    rw [four_pow_eq']
    refine Nat.mul_le_mul_right _ ?_
    calc (42 : ℕ) ≤ 2 ^ 6 := by norm_num
    _ ≤ 2 ^ s := two_pow_le_of_le hs
  have h2C := two_mul_seamSubsetTarget (s := s) (by omega)
  have hw2 : truncatedMersenneWeight s 2 = 4 ^ s / 3 := by norm_num [truncatedMersenneWeight]
  have hw3 : truncatedMersenneWeight s 3 = 4 ^ s / 7 := by norm_num [truncatedMersenneWeight]
  have d3 := Nat.div_add_mod (4 ^ s) 3
  have d3' : 4 ^ s % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have d7 := Nat.div_add_mod (4 ^ s) 7
  have d7' : 4 ^ s % 7 < 7 := Nat.mod_lt _ (by norm_num)
  rw [seamResidualUpto_two (by omega)]
  omega

/-! ### The two obligations are exactly a branch-blind one-step induction

Before the no-go, the class has to be pinned down, or the no-go proves nothing.
`greedyStep` is the greedy step as a function of the residual alone, and
`intervalCeiling_obligations_iff` says the two obligations of `IntervalCeiling`
are *equivalent* to "the interval `[0, bound d)` is carried into
`[0, bound (d+1))` by the step".  Not merely sufficient — forced. -/

/-- The rank-`d` greedy step, as a function of the residual alone. -/
def greedyStep (s d r : ℕ) : ℕ :=
  if truncatedMersenneWeight s d ≤ r then r - truncatedMersenneWeight s d else r

theorem seamResidualUpto_succ_eq_greedyStep {s d : ℕ} (hd : 1 ≤ d) :
    seamResidualUpto s (d + 1) = greedyStep s (d + 1) (seamResidualUpto s d) := by
  rw [seamResidualUpto_succ hd, greedyStep]

/-- **The obligations characterise the class.**  A rank-indexed ceiling carries
`[0, B d)` into `[0, B (d+1))` under the greedy step *for every residual value*
if and only if it satisfies the two obligations of `IntervalCeiling`. -/
theorem intervalCeiling_obligations_iff {s d : ℕ} (B : ℕ → ℕ) :
    (∀ r : ℕ, r < B d → greedyStep s (d + 1) r < B (d + 1)) ↔
      (min (B d) (truncatedMersenneWeight s (d + 1)) ≤ B (d + 1) ∧
        B d ≤ B (d + 1) + truncatedMersenneWeight s (d + 1)) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hc
      rw [not_le] at hc
      have h1 : B (d + 1) < B d := lt_of_lt_of_le hc (min_le_left _ _)
      have h2 : B (d + 1) < truncatedMersenneWeight s (d + 1) :=
        lt_of_lt_of_le hc (min_le_right _ _)
      have hstep := h (B (d + 1)) h1
      rw [greedyStep, if_neg (not_le.mpr h2)] at hstep
      omega
    · by_contra hc
      rw [not_le] at hc
      have hstep := h (B (d + 1) + truncatedMersenneWeight s (d + 1)) (by omega)
      rw [greedyStep, if_pos (by omega)] at hstep
      omega
  · rintro ⟨hmin, htak⟩ r hr
    rw [greedyStep]
    split
    · omega
    · rename_i hnt
      rcases le_total (B d) (truncatedMersenneWeight s (d + 1)) with hc | hc
      · rw [min_eq_left hc] at hmin; omega
      · rw [min_eq_right hc] at hmin; omega

/-- **The class of ceilings C6's induction lives in.**  `bound` is a ceiling for
the residual that depends on the rank alone, `start` says it is valid where the
induction starts, and `declined` / `taken` are exactly the two obligations the
one-step induction must discharge — with no knowledge of which branch the greedy
actually takes at rank `d + 1`.  (`declined`: the residual is then below both
`bound d` and the refused weight.  `taken`: the residual drops by the accepted
weight.) -/
structure IntervalCeiling (s : ℕ) where
  bound : ℕ → ℕ
  start : seamResidualUpto s 2 < bound 2
  declined : ∀ d, 2 ≤ d → d + 1 < s →
    min (bound d) (truncatedMersenneWeight s (d + 1)) ≤ bound (d + 1)
  taken : ∀ d, 2 ≤ d → d + 1 < s →
    bound d ≤ bound (d + 1) + truncatedMersenneWeight s (d + 1)

/-- **Soundness.**  The two obligations really do suffice: an `IntervalCeiling`
bounds the residual at every rank.  So the class is the right abstraction — it is
not an artificially crippled one. -/
theorem IntervalCeiling.sound {s : ℕ} (K : IntervalCeiling s) :
    ∀ d, 2 ≤ d → d < s → seamResidualUpto s d < K.bound d := by
  intro d
  induction d with
  | zero => intro h; omega
  | succ d ih =>
      intro h2 hlt
      rcases Nat.lt_or_ge d 2 with hd | hd
      · rw [show d + 1 = 2 by omega]; exact K.start
      · have hIH := ih hd (by omega)
        rw [seamResidualUpto_succ (by omega : 1 ≤ d)]
        by_cases ht : truncatedMersenneWeight s (d + 1) ≤ seamResidualUpto s d
        · rw [if_pos ht]
          have := K.taken d hd hlt
          omega
        · rw [if_neg ht]
          have hmin := K.declined d hd hlt
          rcases le_total (K.bound d) (truncatedMersenneWeight s (d + 1)) with hc | hc
          · rw [min_eq_left hc] at hmin; omega
          · rw [min_eq_right hc] at hmin; omega

/-- **The class is inhabited**: the corpus's trivial ceiling is an
`IntervalCeiling`.  (Anti-vacuity for everything below.) -/
def trivialCeiling (s : ℕ) : IntervalCeiling s where
  bound := fun _ => seamSubsetTarget s + 1
  start := by
    have : seamResidualUpto s 2 ≤ seamSubsetTarget s := by
      simp only [seamResidualUpto, seamResidual]
      split <;> omega
    omega
  declined := by intro d _ _; exact min_le_left _ _
  taken := by intro d _ _; omega

/-! ### The tail of the weight word is small

`∑_{j ≥ 4} 4 ^ s / (2 ^ j - 1) < (2/15) · 4 ^ s`, while the single rank-`3`
weight is `4 ^ s / 7 > (2/15) · 4 ^ s`.  That gap is what makes the `taken`
obligation unable to erode the `declined` obligation. -/

private theorem fifteen_mul_weight_le {s a : ℕ} (ha : 4 ≤ a) :
    15 * (2 ^ a * truncatedMersenneWeight s a) ≤ 16 * 4 ^ s := by
  have hP : (16 : ℕ) ≤ 2 ^ a := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ a := two_pow_le_of_le ha
  have hmul : (2 ^ a - 1) * truncatedMersenneWeight s a ≤ 4 ^ s := by
    have := Nat.div_mul_le_self (4 ^ s) (2 ^ a - 1)
    simpa [truncatedMersenneWeight, Nat.mul_comm] using this
  calc 15 * (2 ^ a * truncatedMersenneWeight s a)
      = (15 * 2 ^ a) * truncatedMersenneWeight s a := by ring
    _ ≤ (16 * (2 ^ a - 1)) * truncatedMersenneWeight s a :=
        Nat.mul_le_mul_right _ (by omega)
    _ = 16 * ((2 ^ a - 1) * truncatedMersenneWeight s a) := by ring
    _ ≤ 16 * 4 ^ s := Nat.mul_le_mul_left _ hmul

private theorem weightSum_tail_aux (s : ℕ) :
    ∀ n a, 4 ≤ a → s ≤ a + n →
      15 * (2 ^ a * ∑ j ∈ Finset.Ico a s, truncatedMersenneWeight s j) ≤ 32 * 4 ^ s := by
  intro n
  induction n with
  | zero =>
      intro a _ hsa
      rw [Finset.Ico_eq_empty (by omega)]
      simp
  | succ n ih =>
      intro a ha hsa
      rcases Nat.lt_or_ge a s with hlt | hge
      · rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
        have hIH := ih (a + 1) (by omega) (by omega)
        have hpow : (2 : ℕ) ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring
        rw [hpow] at hIH
        have hIH' : 15 * (2 ^ a * ∑ j ∈ Finset.Ico (a + 1) s, truncatedMersenneWeight s j)
            ≤ 16 * 4 ^ s := by
          have hassoc : 15 * (2 * 2 ^ a * ∑ j ∈ Finset.Ico (a + 1) s, truncatedMersenneWeight s j)
              = 2 * (15 * (2 ^ a * ∑ j ∈ Finset.Ico (a + 1) s, truncatedMersenneWeight s j)) := by
            ring
          rw [hassoc] at hIH
          omega
        have hwa := fifteen_mul_weight_le (s := s) (a := a) ha
        have hdist : 15 * (2 ^ a * (truncatedMersenneWeight s a
              + ∑ j ∈ Finset.Ico (a + 1) s, truncatedMersenneWeight s j))
            = 15 * (2 ^ a * truncatedMersenneWeight s a)
              + 15 * (2 ^ a * ∑ j ∈ Finset.Ico (a + 1) s, truncatedMersenneWeight s j) := by
          ring
        rw [hdist]
        omega
      · rw [Finset.Ico_eq_empty (by omega)]
        simp

/-- **The tail bound.**  `15 · ∑_{j = 4}^{s-1} w_j ≤ 2 · 4 ^ s`. -/
theorem fifteen_mul_weightSum_tail_le (s : ℕ) :
    15 * ∑ j ∈ Finset.Ico 4 s, truncatedMersenneWeight s j ≤ 2 * 4 ^ s := by
  have h := weightSum_tail_aux s s 4 (by norm_num) (by omega)
  have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
  rw [h16] at h
  have hdist : 15 * (16 * ∑ j ∈ Finset.Ico 4 s, truncatedMersenneWeight s j)
      = 16 * (15 * ∑ j ∈ Finset.Ico 4 s, truncatedMersenneWeight s j) := by ring
  rw [hdist] at h
  omega

/-- Chaining the `taken` obligation from rank `3` to rank `b`. -/
theorem IntervalCeiling.chain {s : ℕ} (K : IntervalCeiling s) :
    ∀ b, 3 ≤ b → b < s →
      K.bound 3 ≤ K.bound b + ∑ j ∈ Finset.Ico 4 (b + 1), truncatedMersenneWeight s j := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => intro _; simp
  | succ b hb ih =>
      intro hlt
      have hIH := ih (by omega)
      have htak := K.taken b (by omega) (by omega)
      rw [Finset.sum_Ico_succ_top (by omega : 4 ≤ b + 1)]
      omega

/-- The `declined` obligation at rank `2` forces the ceiling at rank `3` to be at
least the whole rank-`3` weight. -/
theorem IntervalCeiling.weight_three_le {s : ℕ} (hs : 6 ≤ s) (K : IntervalCeiling s) :
    truncatedMersenneWeight s 3 ≤ K.bound 3 := by
  have hstart := K.start
  have hres := weight_three_le_residual (s := s) hs
  have hmin := K.declined 2 (by norm_num) (by omega)
  have hle : truncatedMersenneWeight s 3 ≤ K.bound 2 := by omega
  rw [min_eq_right hle] at hmin
  exact hmin

/-- **The no-go, quantitative.**  Every interval ceiling for row `s ≥ 6`
satisfies `4 ^ s ≤ 105 · bound (s - 1) + 90`.  The trivial ceiling has
`2 · bound = 4 ^ s - 2 ^ (s+1)`, so no interval induction improves on it by more
than the constant factor `105 / 2`.  The `4 ^ s` scale cannot be left at all. -/
theorem IntervalCeiling.four_pow_le {s : ℕ} (hs : 6 ≤ s) (K : IntervalCeiling s) :
    4 ^ s ≤ 105 * K.bound (s - 1) + 90 := by
  have hchain := K.chain (s - 1) (by omega) (by omega)
  rw [show s - 1 + 1 = s by omega] at hchain
  have hw3 := K.weight_three_le hs
  have htail := fifteen_mul_weightSum_tail_le s
  have hw3' : truncatedMersenneWeight s 3 = 4 ^ s / 7 := by norm_num [truncatedMersenneWeight]
  have d7 := Nat.div_add_mod (4 ^ s) 7
  have d7' : 4 ^ s % 7 < 7 := Nat.mod_lt _ (by norm_num)
  omega

/-- **The no-go, in the form that matters.**  For `s ≥ 8` no interval ceiling
reaches `2 ^ (s + 1)`.  So the target `ρ s < 2 ^ (s + 1)` — never mind
`ρ s ≤ 2 ^ s` — is unreachable by any one-step induction on the rank recursion,
whatever ceiling it carries.  C6's induction "does not close" because nothing in
its class closes. -/
theorem IntervalCeiling.two_pow_lt {s : ℕ} (hs : 8 ≤ s) (K : IntervalCeiling s) :
    2 ^ (s + 1) < K.bound (s - 1) := by
  have h := K.four_pow_le (by omega)
  have hA : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := four_pow_eq' s
  have h256 : (256 : ℕ) ≤ 2 ^ s := by
    calc (256 : ℕ) = 2 ^ 8 := by norm_num
    _ ≤ 2 ^ s := two_pow_le_of_le hs
  have hbig : 211 * 2 ^ s ≤ 4 ^ s := by
    rw [hA]; exact Nat.mul_le_mul_right _ (by omega)
  have hsucc : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  omega

/-- The same conclusion stated against the corpus's trivial ceiling: an interval
ceiling can be smaller than `seamSubsetTarget s`, but never by more than the
factor `105 / 2 < 53`. -/
theorem IntervalCeiling.no_better_than_trivial {s : ℕ} (hs : 6 ≤ s) (K : IntervalCeiling s) :
    2 * seamSubsetTarget s ≤ 105 * K.bound (s - 1) + 90 := by
  have h := K.four_pow_le hs
  have h2C := two_mul_seamSubsetTarget (s := s) (by omega)
  omega

/-! ### Starting the induction later does not help

`IntervalCeiling` starts at rank `2`.  The obvious escape is to start at some
later rank `a`, having computed the residual there by brute force (this is what
C6 §6 does with ranks `4, 5`).  It does not help: the `declined` obligation alone
forces `min (B a) (w d) ≤ B d` at every later rank, so the ceiling can never fall
below `min (B a) (2 ^ (s+1) + 4)`.  **An interval induction can transport a bound
along the rank recursion; it can never produce one.** -/

theorem truncatedMersenneWeight_antitone {s d : ℕ} (hd : 1 ≤ d) :
    truncatedMersenneWeight s (d + 1) ≤ truncatedMersenneWeight s d := by
  have h1 : (2 : ℕ) ^ d - 1 ≤ 2 ^ (d + 1) - 1 := by
    have : (2 : ℕ) ^ d ≤ 2 ^ (d + 1) := two_pow_le_of_le (by omega)
    omega
  have h2 : 0 < (2 : ℕ) ^ d - 1 := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ d := two_pow_le_of_le hd
    simp only [pow_one] at this
    omega
  exact Nat.div_le_div_left h1 h2

/-- The weight ceiling *does* satisfy the `declined` obligation, at every rank
and every row: the weights are antitone, so refusing rank `d + 1` leaves the
residual below `truncatedMersenneWeight s (d + 1)` automatically.  (Used below
as anti-vacuity for the late-start no-go.) -/
theorem weight_satisfies_declined (s d : ℕ) :
    min (truncatedMersenneWeight s d) (truncatedMersenneWeight s (d + 1))
      ≤ truncatedMersenneWeight s (d + 1) := min_le_right _ _

/-- The `declined` obligation alone pins a floor under every later ceiling. -/
theorem declined_floor {s a : ℕ} {B : ℕ → ℕ} (ha : 1 ≤ a)
    (hdec : ∀ d, a ≤ d → d + 1 < s →
      min (B d) (truncatedMersenneWeight s (d + 1)) ≤ B (d + 1)) :
    ∀ d, a ≤ d → d < s → min (B a) (truncatedMersenneWeight s d) ≤ B d := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => intro _; exact min_le_left _ _
  | succ d hd ih =>
      intro hlt
      have hIH := ih (by omega)
      have hstep := hdec d hd hlt
      have hanti : truncatedMersenneWeight s (d + 1) ≤ truncatedMersenneWeight s d :=
        truncatedMersenneWeight_antitone (by omega)
      have hle : min (B a) (truncatedMersenneWeight s (d + 1))
          ≤ min (B d) (truncatedMersenneWeight s (d + 1)) := by
        refine le_min ?_ (min_le_right _ _)
        exact le_trans (le_min (min_le_left _ _) (le_trans (min_le_right _ _) hanti)) hIH
      exact le_trans hle hstep

/-- **The late-start no-go.**  Whatever rank `a` the induction starts at, the
ceiling it ends with at rank `s - 1` is at least `min (B a) (2 ^ (s+1) + 4)`.
Hence if the final ceiling is below `2 ^ (s + 1)`, the starting one already was:
the induction contributed nothing. -/
theorem declined_floor_terminal {s a : ℕ} (hs : 4 ≤ s) (ha : 1 ≤ a) (has : a ≤ s - 1)
    {B : ℕ → ℕ}
    (hdec : ∀ d, a ≤ d → d + 1 < s →
      min (B d) (truncatedMersenneWeight s (d + 1)) ≤ B (d + 1)) :
    min (B a) (2 ^ (s + 1) + 4) ≤ B (s - 1) := by
  have h := declined_floor ha hdec (s - 1) has (by omega)
  rwa [RemC6.truncatedMersenneWeight_terminal hs] at h

/-- The contrapositive, spelled out. -/
theorem start_lt_of_terminal_lt {s a : ℕ} (hs : 4 ≤ s) (ha : 1 ≤ a) (has : a ≤ s - 1)
    {B : ℕ → ℕ}
    (hdec : ∀ d, a ≤ d → d + 1 < s →
      min (B d) (truncatedMersenneWeight s (d + 1)) ≤ B (d + 1))
    (hfinal : B (s - 1) < 2 ^ (s + 1)) :
    B a < 2 ^ (s + 1) := by
  have h := declined_floor_terminal hs ha has hdec
  rcases le_total (B a) (2 ^ (s + 1) + 4) with hc | hc
  · rw [min_eq_left hc] at h; omega
  · rw [min_eq_right hc] at h; omega

/-- **Anti-vacuity for the late-start no-go.**  The `declined` hypothesis is not
empty: the weight ceiling satisfies it at every row and every starting rank. -/
theorem declined_floor_terminal_weight {s a : ℕ} (hs : 4 ≤ s) (ha : 1 ≤ a) (has : a ≤ s - 1) :
    min (truncatedMersenneWeight s a) (2 ^ (s + 1) + 4)
      ≤ truncatedMersenneWeight s (s - 1) :=
  declined_floor_terminal hs ha has (fun d _ _ => weight_satisfies_declined s d)

/-- **Anti-vacuity for the fixed-start no-go.**  `IntervalCeiling s` is inhabited,
so `IntervalCeiling.two_pow_lt` is a statement about a non-empty class. -/
theorem trivialCeiling_two_pow_lt {s : ℕ} (hs : 8 ≤ s) :
    2 ^ (s + 1) < (trivialCeiling s).bound (s - 1) :=
  IntervalCeiling.two_pow_lt hs (trivialCeiling s)

/-! ## 5. What is actually true, and what it would buy

The ceiling that survives measurement is not `2 ^ (2 * s - d)` but the rank-`d`
weight itself.  At `s = 13, d = 7` it holds with room (`524419 < 528416`) exactly
where C6's ceiling fails.  It is **MEASURED, not proved**; and by §4 it is not
provable by the induction C6 attempted either — see
`weightCeiling_not_intervalCeiling`. -/

/-- The corrected ceiling: the residual after rank `d` is below the rank-`d`
weight.  MEASURED for every `s ∈ [6, 3000]` and every `d ∈ [2, s-1]`; the largest
observed ratio is `0.99998` at `(s, d) = (606, 602)`.  NOT PROVED. -/
def WeightCeilingAt (s : ℕ) : Prop :=
  ∀ d : ℕ, 2 ≤ d → d < s → seamResidualUpto s d < truncatedMersenneWeight s d

/-- What the corrected ceiling would buy, if it were proved: the unconditional
bound `ρ s < 2 ^ (s + 1) + 4`.  Note this is *weaker* than the `ρ s < 2 ^ (s+1)`
C6 hoped for, by the four low bits of the terminal weight. -/
theorem remainder_lt_of_weightCeiling {s : ℕ} (hs : 4 ≤ s) (h : WeightCeilingAt s) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 4 := by
  have hd := h (s - 1) (by omega) (by omega)
  rw [seamResidualUpto_last (by omega), RemC6.truncatedMersenneWeight_terminal hs] at hd
  exact hd

/-- **Anti-vacuity.**  The corrected ceiling holds at `s = 13` — the very row
that refutes C6's ceiling.  So `remainder_lt_of_weightCeiling` is not vacuous. -/
theorem weightCeiling_thirteen : WeightCeilingAt 13 := by
  intro d h2 h13
  interval_cases d <;>
    norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

theorem seamIntegerGreedyRemainder_thirteen_lt' : seamIntegerGreedyRemainder 13 < 2 ^ (13 + 1) + 4 :=
  remainder_lt_of_weightCeiling (by norm_num) weightCeiling_thirteen

/-- **The corrected ceiling is out of reach of the same induction.**  For
`s ≥ 10` the family `d ↦ truncatedMersenneWeight s d` is *not* an
`IntervalCeiling`: it is far too small for §4's lower bound.  So the honest
statement is not "C6's induction needs a stronger hypothesis"; it is "no
one-step induction on the rank recursion can carry any ceiling of size
`O(2 ^ s)` at all". -/
theorem weightCeiling_not_intervalCeiling {s : ℕ} (hs : 10 ≤ s) :
    ¬ ∃ K : IntervalCeiling s, K.bound = truncatedMersenneWeight s := by
  rintro ⟨K, hK⟩
  have h := K.four_pow_le (by omega)
  rw [hK, RemC6.truncatedMersenneWeight_terminal (by omega)] at h
  have hA : (4 : ℕ) ^ s = 2 ^ s * 2 ^ s := four_pow_eq' s
  have h1024 : (1024 : ℕ) ≤ 2 ^ s := by
    calc (1024 : ℕ) = 2 ^ 10 := by norm_num
    _ ≤ 2 ^ s := two_pow_le_of_le hs
  have hbig : 1024 * 2 ^ s ≤ 4 ^ s := by
    rw [hA]; exact Nat.mul_le_mul_right _ h1024
  have hsucc : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  omega

/-- The weight ceiling fails the `taken` obligation, because consecutive weights
are in ratio
strictly greater than `2`.  At `s = 13, d = 4`: `w 4 = 4473924` but
`2 * w 5 = 4329604`.  **That is the whole diagnosis.**  The declined branch of the
corrected invariant is free; the taken branch is short by
`w d - 2 * w (d+1) ≈ 4 ^ s / (2 ^ d - 1)(2 ^ (d+1) - 1)`, and because the rank
map doubles, that shortfall can never be absorbed by a rank-indexed ceiling. -/
theorem weight_fails_taken :
    ¬ truncatedMersenneWeight 13 4
        ≤ truncatedMersenneWeight 13 5 + truncatedMersenneWeight 13 5 := by
  norm_num [truncatedMersenneWeight]

/-!
## Measurement note (not a theorem — recorded for the record)

Reproducing the corpus definitions verbatim (`truncatedMersenneWeight`,
`seamSubsetTarget`, `seamWeights`, `integerGreedyRemainder`) and scanning
`s ∈ [6, 3000]`, `d ∈ [2, s-1]`:

* C6's ceiling `seamResidualUpto s d < 2 ^ (2 * s - d)` fails **exactly once**,
  at `(s, d) = (13, 7)`, with ratio `1.00025`.  That single failure is the
  theorem `not_residualInvariant` above.  Excluding it, the maximum ratio is
  `0.9999807` at `(s, d) = (606, 602)`.  C6's reported maximum `0.99989` is
  therefore a scan that missed row `13`; the invariant it records as "TRUE
  empirically" is false.
* The corrected ceiling `seamResidualUpto s d < truncatedMersenneWeight s d`
  holds at **every** `(s, d)` in that range, with the same maximum ratio
  `0.9999807` at `(606, 602)`.  It fails at `s = 5`, the corpus's known
  degenerate row (`ρ 5 = 71 > 2 ^ 6`).
* `ρ s < 2 ^ (s + 1)` holds for every `s ∈ [6, 3000]`; `s = 5` is the sole
  exceedance in `[5, 3000]`.  So the *conclusion* C6 wanted is not in doubt; only
  its route is.

Why the ceiling is tight, and why §4 is what it is.  Writing
`x d := seamResidualUpto s d / 2 ^ (2 * s - d)`, the greedy step reads
`x (d+1) = 2 * x d` when rank `d + 1` is refused and
`x (d+1) = 2 * x d - w (d+1) / 2 ^ (2*s-d-1)` when it is accepted, with
`w (d+1) / 2 ^ (2*s-d-1) = 1 + O(2 ^ (-d))`.  That is the doubling map with an
`O(2 ^ (-d))` perturbation of the cut point.  Two consequences, both visible in
this file:

* the invariant `x d < 1` is destroyed precisely when `x d` lands in
  `[1/2, (1 + O(2^(-d)))/2)` — the tangency window of
  `invariant_step_dichotomy`, of relative width `2 ^ (-d)`.  Row `13` lands in
  it at `d = 6` (`tangency_window_thirteen`);
* because the map is *expanding*, any slack in a rank-indexed ceiling doubles
  every step while the available correction only decays like `2 ^ (-d)`.  That
  is the mechanism behind §4: no interval ceiling can shrink faster than the
  weights themselves, and the weights only sum to a constant fraction of `4 ^ s`.

Consequently the assigned target — "close C6's induction and obtain
`ρ s < 2 ^ (s+1)` unconditionally" — is not merely open; the route is closed.
Any proof of `ρ s < 2 ^ (s+1)` must use information the rank recursion does not
carry: which ranks are actually declined (C6 §5's `SeamSkipsLast`), or the
row-to-row recursion, or the conjugacy of the induced doubling map.
-/

end ErdosProblems.Three.T1
