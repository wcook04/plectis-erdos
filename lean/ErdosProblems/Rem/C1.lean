/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.R1
import ErdosProblems.Bit.R2
import ErdosProblems.Bit.R3
import ErdosProblems.Bit.R4

/-!
# Rem C1: the persistent-surplus branch, and why the forward iteration cannot close

`BitR2.half_mem_of_remainderReachesHalfPointCofinally` reduces Erdős `#257`'s
`1/2` question to one inequality at cofinally many rows,

    `seamIntegerGreedyRemainder s ≤ 2 ^ s`.

This file examines the complementary branch — **persistent surplus**,
`2 ^ s < seamIntegerGreedyRemainder s` for every `s ≥ S` — and asks whether the
row-law and ceiling hypotheses stated below refute it.  They do not, for three
independent reasons proved here.

## 1.  Two upper bounds never collide

The forward form of the descent law is an *upper* bound,
`ρ (s+1) + 2 ^ (s+1) + 4 ≤ 4 * ρ s`, and every ceiling the corpus can supply at
an arbitrary row is also an *upper* bound.  `le_of_descent_of_quadrupling` shows
that the two are compatible whenever the ceiling merely quadruples per row:
a descent solution starting under such a ceiling stays under it forever.  The
corpus's unconditional ceiling `seamSubsetTarget` quadruples exactly
(`seamSubsetTarget_quadruples`), and so does every `K * 4 ^ s`.  So the
comparison the C1 angle proposes is *identically satisfied* — it can never
produce a contradiction.  This is the named obstruction, as a theorem rather
than a remark.

## 2.  Persistent surplus does not put the rows on the right branch

The forward *lower* bound `4 * ρ s ≤ ρ (s+1) + 2 ^ (s+1) + 2 * s` — the only
half of `BitR1.remainder_step_of_top_mem` that could drive growth — needs the
brand-new top rank of row `s+1` to be selected.  Persistent surplus does not
supply that.  Rows `25`, `31` and `37` are kernel-certified counterexamples:
each carries a surplus `2 ^ s < ρ s`, and at each the lower half of the row law
*fails*, so the successor row is good (`BitR1.lateAt_26`, `lateAt_32`,
`lateAt_38`).  The forward iteration cannot even be started.

## 3.  A model of the whole row-level theory with persistent surplus

`surplusModel c s = 2 ^ s + c` satisfies simultaneously, for `2 ≤ c` and
`3 * c ≤ 2 * s`:

* persistent surplus `2 ^ s < f s` (the half point is never reached);
* `BitR1.StepLaw` — the exact two-sided row law of the forced run;
* the good-row ceiling `3 * f s < 7 * 2 ^ s + 4` of
  `BitR2.three_mul_remainder_lt_of_largestSkipLateAt`, so `BitR2`'s Theorem B
  can never fire;
* `f s < 2 ^ s + 2 * s`, so `BitR2.badRun_pins_remainder` is never violated;
* `2 ^ (s+1) + 4 ≤ 4 * f s`, the right-branch window's lower clause;
* `f s ≤ 2 ^ (s+1)` — the growth hypothesis `BitR1` still has to assume;
* `f s ≤ seamSubsetTarget s`, the trivial ceiling.

So **no** consequence of those seven facts can imply
`RemainderReachesHalfPointCofinally`.  In particular the missing unconditional
bound named in the C1 brief — an upper bound at an arbitrary row that beats
`4 ^ t / 2` — would not suffice even in the strong form `ρ t ≤ 2 ^ (t+1)`:
the model obeys it.  `band_invariant` sharpens this: the whole band
`[2 ^ s + 2, 2 ^ s + 4]` is forward-invariant for the two-sided law, so the
recurrence cannot expel a trajectory even non-deterministically.

## 4.  What is left: the window-miss criterion

The one positive contribution here is a *second*, independent cofinal criterion
for `1/2 ∈ mersenneAchievementSet`: `half_mem_of_windowMissCofinally`.  It fires
exactly when the one-step defect `4 * ρ s - ρ (s+1) - 2 ^ (s+1)` leaves the
window `[4, 2 * s]`, and it is **not** subsumed by
`RemainderReachesHalfPointCofinally`: at `s = 25`, `31`, `37` the remainder is
above the half point (so `BitR2`'s criterion is silent) while the window is
missed (so this one fires).  Whether either criterion holds cofinally is open;
nothing here proves it.

## 5.  The row recurrence is blind

`rowLaw_blind_at_16` is the structural reason all of the above happens.  At
`s = 16` the two-sided row law holds, the remainder is above the half point, and
every one of `BitR1`'s, `BitR2`'s, `BitR3`'s and `BitR4`'s row-level criteria is
silent — yet row `17` is good, its skipped late rank being `14`, not the
brand-new top rank `16`.  The row recurrence only ever tracks the top rank, so
it is strictly weaker than `LargestSkipLateAt`.  Iterating that recurrence with
the ceiling classes analyzed here does not recover the skipped lower rank at
this witness row; this is not a no-go theorem for every conceivable auxiliary
invariant.

Every theorem below was checked with `lake env lean ErdosProblems/Rem/C1.lean`
(exit `0`, empty output).
-/

namespace ErdosProblems.RemC1

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## 1. The abstract obstruction: two upper bounds never collide -/

/-- **The obstruction, as a theorem.**  A solution of the forward descent law
that starts under a ceiling which quadruples per row stays under it at every
later row.  Consequently no comparison of the descent law with such a ceiling
can ever be contradictory: the C1 programme compares one upper bound with
another. -/
theorem le_of_descent_of_quadrupling {f g : ℕ → ℕ} {S : ℕ}
    (hstep : ∀ s : ℕ, S ≤ s → f (s + 1) + 2 ^ (s + 1) + 4 ≤ 4 * f s)
    (hceil : ∀ s : ℕ, S ≤ s → 4 * g s ≤ g (s + 1))
    (hbase : f S ≤ g S) :
    ∀ s : ℕ, S ≤ s → f s ≤ g s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact hbase
  | succ s hs ih =>
      have h1 := hstep s hs
      have h2 := hceil s hs
      have hj : 0 < (2 : ℕ) ^ s := Nat.two_pow_pos s
      calc f (s + 1) ≤ 4 * f s := by omega
        _ ≤ 4 * g s := by omega
        _ ≤ g (s + 1) := h2

/-- The corpus's own unconditional ceiling quadruples exactly. -/
theorem seamSubsetTarget_quadruples {s : ℕ} (hs : 1 ≤ s) :
    4 * seamSubsetTarget s ≤ seamSubsetTarget (s + 1) := by
  have hle : (2 : ℕ) ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : 2 * (s + 1) - 1 = (2 * s - 1) + 2 := by omega
  have e2 : (2 : ℕ) ^ ((2 * s - 1) + 2) = 4 * 2 ^ (2 * s - 1) := by
    rw [pow_add]; ring
  have e3 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  unfold seamSubsetTarget
  rw [e1, e2, e3]
  omega

/-- **The trivial ceiling is useless, unconditionally.**  Any sequence obeying
the forward descent law from `S` on and starting below `seamSubsetTarget`
remains below it forever.  Since `seamIntegerGreedyRemainder s ≤
seamSubsetTarget s` holds at every row anyway, the forward iteration produces
no information. -/
theorem descent_never_breaks_trivial_ceiling {f : ℕ → ℕ} {S : ℕ} (hS : 1 ≤ S)
    (hstep : ∀ s : ℕ, S ≤ s → f (s + 1) + 2 ^ (s + 1) + 4 ≤ 4 * f s)
    (hbase : f S ≤ seamSubsetTarget S) :
    ∀ s : ℕ, S ≤ s → f s ≤ seamSubsetTarget s :=
  le_of_descent_of_quadrupling hstep
    (fun s hs => seamSubsetTarget_quadruples (by omega)) hbase

/-- The same for an arbitrary quartic ceiling `K * 4 ^ s`: a constant-factor
improvement of the trivial ceiling changes nothing. -/
theorem descent_never_breaks_quartic_ceiling {f : ℕ → ℕ} {K S : ℕ}
    (hstep : ∀ s : ℕ, S ≤ s → f (s + 1) + 2 ^ (s + 1) + 4 ≤ 4 * f s)
    (hbase : f S ≤ K * 4 ^ S) :
    ∀ s : ℕ, S ≤ s → f s ≤ K * 4 ^ s :=
  le_of_descent_of_quadrupling hstep
    (fun s _ => Nat.le_of_eq (by rw [pow_succ]; ring)) hbase

/-! ## 2. The model: persistent surplus satisfies every row-level law -/

/-- The persistent-surplus model: the half point is exceeded by the constant
`c` at every row. -/
def surplusModel (c : ℕ) : ℕ → ℕ := fun s => 2 ^ s + c

/-- The model obeys `BitR1`'s two-sided row law — the exact law the forced run
imposes on `seamIntegerGreedyRemainder` — from any row `N` with `3 * c ≤ 2 * N`
on. -/
theorem surplusModel_stepLaw {c N : ℕ} (hc : 2 ≤ c) (hN : 3 * c ≤ 2 * N) :
    BitR1.StepLaw (surplusModel c) N := by
  intro s hs
  have e1 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have e2 : (2 : ℕ) ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by rw [pow_succ]; ring
  simp only [surplusModel]
  omega

/-- **The model for the listed constraints.**  The row-level inequalities
enumerated in the theorem are satisfied by `2 ^ s + c`, together with
persistent surplus. -/
theorem surplusModel_constraints {c s : ℕ} (hc : 2 ≤ c) (hs : 5 ≤ s)
    (hcs : 3 * c ≤ 2 * s) :
    2 ^ s < surplusModel c s ∧
      3 * surplusModel c s < 7 * 2 ^ s + 4 ∧
      surplusModel c s < 2 ^ s + 2 * s ∧
      2 ^ (s + 1) + 4 ≤ 4 * surplusModel c s ∧
      surplusModel c s ≤ 2 ^ (s + 1) ∧
      surplusModel c s ≤ seamSubsetTarget s := by
  have hsp : s < 2 ^ s := Nat.lt_two_pow_self
  have e1 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hbig : (2 : ℕ) ^ (s + 2) ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2 : (2 : ℕ) ^ (s + 2) = 4 * 2 ^ s := by
    rw [show s + 2 = s + 1 + 1 by omega, pow_succ, e1]; ring
  have htar : seamSubsetTarget s = 2 ^ (2 * s - 1) - 2 ^ s := rfl
  have hpow : (2 : ℕ) ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [surplusModel]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  rw [htar]
  omega

/-- **No row-level argument can refute persistent surplus.**  There is an
explicit sequence that never returns to the half point and yet satisfies the
two-sided row law, the good-row ceiling, the pin window, the right-branch
window, the growth bound `≤ 2 ^ (s+1)` and the trivial ceiling, at every row
`s ≥ 5`. -/
theorem exists_persistent_surplus_model :
    ∃ f : ℕ → ℕ, BitR1.StepLaw f 5 ∧
      ∀ s : ℕ, 5 ≤ s →
        2 ^ s < f s ∧
          3 * f s < 7 * 2 ^ s + 4 ∧
          f s < 2 ^ s + 2 * s ∧
          2 ^ (s + 1) + 4 ≤ 4 * f s ∧
          f s ≤ 2 ^ (s + 1) ∧
          f s ≤ seamSubsetTarget s :=
  ⟨surplusModel 2, surplusModel_stepLaw (by norm_num) (by norm_num),
    fun s hs => surplusModel_constraints (by norm_num) hs (by omega)⟩

/-- The model also realises the hypotheses of the abstract no-go: it is a
descent solution sitting under the trivial ceiling. -/
theorem surplusModel_descent_under_trivial_ceiling :
    ∀ s : ℕ, 5 ≤ s → surplusModel 2 s ≤ seamSubsetTarget s :=
  descent_never_breaks_trivial_ceiling (by norm_num)
    (fun s hs => (surplusModel_stepLaw (c := 2) (N := 5) (by norm_num) (by norm_num) s hs).1)
    (by norm_num [surplusModel, seamSubsetTarget])

/-- …and under an arbitrary quartic ceiling: the hypotheses of
`descent_never_breaks_quartic_ceiling` are realised too. -/
theorem surplusModel_descent_under_quartic_ceiling :
    ∀ s : ℕ, 5 ≤ s → surplusModel 2 s ≤ 1 * 4 ^ s :=
  descent_never_breaks_quartic_ceiling (K := 1) (S := 5)
    (fun s hs => (surplusModel_stepLaw (c := 2) (N := 5) (by norm_num) (by norm_num) s hs).1)
    (by norm_num [surplusModel])

/-- **The band is forward-invariant.**  From every value in
`[2 ^ s + 2, 2 ^ s + 4]` the two-sided row law permits a step into
`[2 ^ (s+1) + 2, 2 ^ (s+1) + 4]`.  So the recurrence cannot expel a trajectory
from the forced-run band, even allowing the below-pulse to be chosen
adversarially at each row. -/
theorem band_invariant {s r : ℕ} (hs : 7 ≤ s)
    (hlo : 2 ^ s + 2 ≤ r) (hhi : r ≤ 2 ^ s + 4) :
    ∃ r' : ℕ, 2 ^ (s + 1) + 2 ≤ r' ∧ r' ≤ 2 ^ (s + 1) + 4 ∧
      r' + 2 ^ (s + 1) + 4 ≤ 4 * r ∧
      4 * r ≤ r' + 2 ^ (s + 1) + 2 * s := by
  have e1 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  exact ⟨2 ^ (s + 1) + 2, by omega, by omega, by omega, by omega⟩

/-- The band-invariance hypothesis is satisfied: `r = 2 ^ 7 + 2` at `s = 7`. -/
theorem band_invariant_witness :
    ∃ r' : ℕ, 2 ^ 8 + 2 ≤ r' ∧ r' ≤ 2 ^ 8 + 4 ∧
      r' + 2 ^ 8 + 4 ≤ 4 * (2 ^ 7 + 2) ∧
      4 * (2 ^ 7 + 2) ≤ r' + 2 ^ 8 + 2 * 7 :=
  band_invariant (s := 7) (r := 2 ^ 7 + 2) (by norm_num) (by norm_num) (by norm_num)

/-! ## 3. Persistent surplus does not force the right branch -/

section Certificates

set_option maxRecDepth 8000000

/-- Row `25` carries a surplus above the half point. -/
theorem surplus_25 : 2 ^ 25 < seamIntegerGreedyRemainder 25 := by
  rw [BitR1.remOf_eq]
  decide +kernel

/-- …and at row `25` the *lower* half of the two-sided row law fails, so the
brand-new top rank is **not** selected at row `26`.  The forward growth step of
the C1 iteration is unavailable there. -/
theorem ascent_25 :
    seamIntegerGreedyRemainder 26 + 2 ^ 26 + 2 * 25 <
      4 * seamIntegerGreedyRemainder 25 := by
  simp only [BitR1.remOf_eq]
  decide +kernel

theorem surplus_31 : 2 ^ 31 < seamIntegerGreedyRemainder 31 := by
  rw [BitR1.remOf_eq]
  decide +kernel

theorem ascent_31 :
    seamIntegerGreedyRemainder 32 + 2 ^ 32 + 2 * 31 <
      4 * seamIntegerGreedyRemainder 31 := by
  simp only [BitR1.remOf_eq]
  decide +kernel

theorem surplus_37 : 2 ^ 37 < seamIntegerGreedyRemainder 37 := by
  rw [BitR1.remOf_eq]
  decide +kernel

theorem ascent_37 :
    seamIntegerGreedyRemainder 38 + 2 ^ 38 + 2 * 37 <
      4 * seamIntegerGreedyRemainder 37 := by
  simp only [BitR1.remOf_eq]
  decide +kernel

end Certificates

/-- **C1's premise fails.**  There are rows carrying a surplus above the half
point at which the row law's growth half does not hold — equivalently, at which
the successor row is good.  So "persistent surplus" does not put every row on
the right branch, and the forward iteration `a (s+1) ≥ 4 * a s - 2 * s` cannot
be run under it. -/
theorem exists_surplus_row_off_the_right_branch :
    ∃ s : ℕ, 5 ≤ s ∧ 2 ^ s < seamIntegerGreedyRemainder s ∧
      LargestSkipLateAt (s + 1) ∧
      ¬ (4 * seamIntegerGreedyRemainder s ≤
          seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 2 * s) := by
  refine ⟨25, by norm_num, surplus_25, BitR1.lateAt_26, ?_⟩
  have h := ascent_25
  norm_num at h ⊢
  omega

/-- Three such rows, so the failure is not a boundary artefact. -/
theorem three_surplus_rows_off_the_right_branch :
    (2 ^ 25 < seamIntegerGreedyRemainder 25 ∧ LargestSkipLateAt 26) ∧
      (2 ^ 31 < seamIntegerGreedyRemainder 31 ∧ LargestSkipLateAt 32) ∧
      (2 ^ 37 < seamIntegerGreedyRemainder 37 ∧ LargestSkipLateAt 38) :=
  ⟨⟨surplus_25, BitR1.lateAt_26⟩, ⟨surplus_31, BitR1.lateAt_32⟩,
    ⟨surplus_37, BitR1.lateAt_38⟩⟩

/-! ## 4. The window-miss criterion -/

/-- Cofinally many rows at which the one-step defect
`4 * ρ s - ρ (s+1) - 2 ^ (s+1)` leaves the window `[4, 2 * s]`. -/
def WindowMissCofinally : Prop :=
  ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ 3 ≤ s ∧
    ¬ (seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 4 ≤
          4 * seamIntegerGreedyRemainder s ∧
        4 * seamIntegerGreedyRemainder s ≤
          seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 2 * s)

/-- **A second cofinal criterion for `1/2 ∈ mersenneAchievementSet`.**
Independent of `BitR2.RemainderReachesHalfPointCofinally`: it fires at rows
whose remainder sits *above* the half point. -/
theorem half_mem_of_windowMissCofinally (h : WindowMissCofinally) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  rw [AngleD2.half_mem_iff_unboundedLargestSkipLate]
  intro N
  obtain ⟨s, hNs, hs3, hmiss⟩ := h N
  exact ⟨s + 1, by omega, BitR1.largestSkipLateAt_succ_of_window_miss hs3 hmiss⟩

/-- The window is missed at row `25`. -/
theorem windowMiss_25 :
    ¬ (seamIntegerGreedyRemainder (25 + 1) + 2 ^ (25 + 1) + 4 ≤
          4 * seamIntegerGreedyRemainder 25 ∧
        4 * seamIntegerGreedyRemainder 25 ≤
          seamIntegerGreedyRemainder (25 + 1) + 2 ^ (25 + 1) + 2 * 25) := by
  have h := ascent_25
  norm_num at h ⊢
  omega

/-- The window is missed at row `31`. -/
theorem windowMiss_31 :
    ¬ (seamIntegerGreedyRemainder (31 + 1) + 2 ^ (31 + 1) + 4 ≤
          4 * seamIntegerGreedyRemainder 31 ∧
        4 * seamIntegerGreedyRemainder 31 ≤
          seamIntegerGreedyRemainder (31 + 1) + 2 ^ (31 + 1) + 2 * 31) := by
  have h := ascent_31
  norm_num at h ⊢
  omega

/-- The window is missed at row `37`. -/
theorem windowMiss_37 :
    ¬ (seamIntegerGreedyRemainder (37 + 1) + 2 ^ (37 + 1) + 4 ≤
          4 * seamIntegerGreedyRemainder 37 ∧
        4 * seamIntegerGreedyRemainder 37 ≤
          seamIntegerGreedyRemainder (37 + 1) + 2 ^ (37 + 1) + 2 * 37) := by
  have h := ascent_37
  norm_num at h ⊢
  omega

/-- **The body of `WindowMissCofinally` is satisfied for every `N ≤ 37`**, so
the criterion is not vacuous at the near end.  (Whether it holds for *all* `N`
is open; nothing here proves it.) -/
theorem windowMissCofinally_witness {N : ℕ} (hN : N ≤ 37) :
    ∃ s : ℕ, N ≤ s ∧ 3 ≤ s ∧
      ¬ (seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 4 ≤
            4 * seamIntegerGreedyRemainder s ∧
          4 * seamIntegerGreedyRemainder s ≤
            seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) + 2 * s) :=
  ⟨37, hN, by norm_num, windowMiss_37⟩

/-- **The new criterion is not subsumed.**  At `s = 25, 31, 37` the criterion of
`BitR2.RemainderReachesHalfPointCofinally` is silent (the remainder is above the
half point) while the window-miss criterion fires. -/
theorem windowMiss_where_halfPoint_criterion_is_silent :
    (¬ (seamIntegerGreedyRemainder 25 ≤ 2 ^ 25)) ∧
      (¬ (seamIntegerGreedyRemainder 31 ≤ 2 ^ 31)) ∧
      (¬ (seamIntegerGreedyRemainder 37 ≤ 2 ^ 37)) :=
  ⟨by have := surplus_25; omega, by have := surplus_31; omega,
    by have := surplus_37; omega⟩

/-! ## 5. The row recurrence is strictly weaker than the truth -/

section BlindSpot

set_option maxRecDepth 8000000

/-- Row `17` is good, and *not* because of its brand-new top rank: the skipped
late rank is `14`, with `2 * 17 = 34 < 42 = 3 * 14`. -/
theorem lateAt_17 : LargestSkipLateAt 17 :=
  SkipD3.largestSkipLateAt_of_late_skip (m := 14) (by norm_num) (by norm_num)
    (by norm_num)
    (SkipD3.notMem_support_of_gb_false (by norm_num) (by norm_num) (by decide +kernel))

/-- At row `16` the two-sided row law holds (its defect is `7`, inside the
window `[4, 32]`), so `BitR1.largestSkipLateAt_succ_of_window_miss` is silent. -/
theorem rowLaw_holds_16 :
    seamIntegerGreedyRemainder 17 + 2 ^ 17 + 4 ≤
        4 * seamIntegerGreedyRemainder 16 ∧
      4 * seamIntegerGreedyRemainder 16 ≤
        seamIntegerGreedyRemainder 17 + 2 ^ 17 + 2 * 16 := by
  constructor <;> · simp only [BitR1.remOf_eq]; decide +kernel

/-- Row `16` carries a surplus, so `BitR2`'s half-point criterion is silent. -/
theorem surplus_16 : 2 ^ 16 < seamIntegerGreedyRemainder 16 := by
  rw [BitR1.remOf_eq]
  decide +kernel

end BlindSpot

/-- **The row recurrence cannot see the good row it sits next to.**  At `s = 16`
every row-level certificate the corpus owns is silent:

* the two-sided row law *holds*, so `BitR1.largestSkipLateAt_succ_of_window_miss`
  gives nothing;
* `2 ^ 16 < ρ 16`, so `BitR2.exists_largestSkipLateAt_of_remainder_le_two_pow`
  gives nothing;
* `2 ^ 15 < ρ 16`, so `BitR4.largestSkipLateAt_succ_of_remainder_le` gives
  nothing;
* `2 ^ 17 < 4 * ρ 16`, so `BitR3.largestSkipLateAt_succ_of_small_remainder`
  gives nothing;

and yet row `17` **is** good.  The witness is rank `14`, not the brand-new top
rank `16`, and the row recurrence only ever tracks the top rank.  So the whole
row-recurrence layer — the layer the C1 angle proposes to iterate — is strictly
weaker than `LargestSkipLateAt`, independently of any ceiling. -/
theorem rowLaw_blind_at_16 :
    (seamIntegerGreedyRemainder 17 + 2 ^ 17 + 4 ≤
          4 * seamIntegerGreedyRemainder 16 ∧
        4 * seamIntegerGreedyRemainder 16 ≤
          seamIntegerGreedyRemainder 17 + 2 ^ 17 + 2 * 16) ∧
      2 ^ 16 < seamIntegerGreedyRemainder 16 ∧
      2 ^ 15 < seamIntegerGreedyRemainder 16 ∧
      2 ^ 17 < 4 * seamIntegerGreedyRemainder 16 ∧
      LargestSkipLateAt 17 := by
  have h := surplus_16
  exact ⟨rowLaw_holds_16, h, by omega, by omega, lateAt_17⟩

/-! ## 6. The endpoint, restated

`RemainderReachesHalfPointCofinally` is **not** proved here, and the results of
§1–§3 say why no forward iteration of the row recurrence can prove it: the
descent law's usable half is an upper bound, its growth half is unavailable on
surplus rows, and `surplusModel 2` satisfies every row-level constraint the
corpus knows while never returning to the half point.  Any proof must import
information the row recurrence does not see — rank-level structure of
`seamGreedyWord`, or an unconditional ceiling strictly below `2 ^ s + 2`. -/

/-- The exact shape of a bound that *would* close the question, for contrast
with `surplusModel`: `ρ s ≤ 2 ^ s` at cofinally many rows.  Anything weaker by
an additive constant `≥ 2` is satisfied by the model, hence insufficient on
row-level grounds alone. -/
theorem sufficient_bound_is_sharp {c : ℕ} (hc : 2 ≤ c) {s : ℕ} (_hs : 5 ≤ s)
    (_hcs : 3 * c ≤ 2 * s) :
    ¬ (surplusModel c s ≤ 2 ^ s) := by
  simp only [surplusModel]
  omega

end ErdosProblems.RemC1
