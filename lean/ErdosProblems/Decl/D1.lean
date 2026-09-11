/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Three.T1
import ErdosProblems.Bit.Corr1

/-!
# D1 — surviving the declined step: what a stronger invariant costs

The brief for this file was:

> The plain hypothesis `R k < 2 ^ (2*s-k)` is too weak to survive a decline.
> Find a stronger invariant that IS preserved by both branches.  Natural
> candidates: `R k < 2 ^ (2*s-k) - (tail of lower binary terms of w k)`; or a
> two-sided invariant tracking `R k` relative to `w (k+1)` rather than to a pure
> power of two; or an invariant on `R k + (something)`.

**The answer is negative for both named candidates, and the negative is proved.**
The excess candidate is refuted quantitatively (§3); the two-sided candidate is
refuted structurally (§4) — a lower bound genuinely escapes `T1`'s no-go, but
only by carrying the entire decline pattern of the row inside it.  What *does*
come out of the declined step is a forced-take law (§1), and that law has two
concrete payoffs: an exactly sharp form of `C6` §5 (§2) and a sufficient
condition for one of the two side conditions of `Bit/Corr1` and `Three/T4` at
declined ranks (§5).

**`ρ s < 2 ^ (s+1)` is NOT proved here.**  Nothing below closes the declined
step in the sense the brief asked for.

## §1 — the forced-take law (PROVED, unconditional)

`weight_succ_le_of_two_pow_le`: if `2 ^ (2*s-d) ≤ R d` then
`w (d+1) ≤ R d`, so rank `d + 1` is **taken**.  Because
`w (d+1) ≤ 2 ^ (2*s-d-1) + 2 ^ (2*s-2d-1) ≤ 2 ^ (2*s-d)`, a residual at or above
C6's ceiling can never decline the next rank.

Two consequences, both unconditional:

* `residual_lt_two_pow_of_declined`: **C6's invariant holds for free at every
  rank that immediately precedes a decline.**  No induction is involved.
* `BrokenAt.not_declined_succ`: the tangency window of
  `T1.invariant_step_dichotomy` **cannot be entered twice in a row**.  Once
  C6's invariant breaks at rank `d`, rank `d+1` is forced taken.

`BrokenAt.restored` / `BrokenAt.not_restored` give the exact repair condition
(`excess < weightTail s (d+1)`), and `weightTail_fails_halving` shows why the
repair is not automatic: the tails fall by a factor of about `4` per rank, so
one rank of take cannot in general absorb the excess one decline creates.
Anti-vacuity: `brokenAt_thirteen_seven` and `thirteen_break_repairs` — at the
corpus's unique break `(s,d) = (13,7)` the break does repair, at rank `8`.

## §2 — the exact suffix sum, and a sharp form of `C6` §5 (PROVED)

`seamWeightsFrom_sum_exact`: for `a` past two thirds of the row,

    3 * (∑_{j=a}^{s-1} w j) + 3 * 2 ^ (s+1) + 4 = 3 * 2 ^ (2*s-a+1) + 4 ^ (s-a+1),

i.e. the suffix sum **exactly**, second bits included.  `RemC6`'s
`seamWeightsFrom_sum_lower` keeps only the top bits; `sum_exact_implies_C6_lower`
checks the new identity implies the old bound.  Feeding it into
`RemC6.seamIntegerGreedyRemainder_eq_of_skipsLast` gives

`remainder_lt_of_late_largest_skip_sharp`:
    `3 * ρ s < 3 * 2 ^ (s+1) + 2 * 4 ^ (s-d) + 4`   (`d` the late largest declined rank)

against `RemC6.seamIntegerGreedyRemainder_lt_of_late_largest_skip`'s
`ρ s < 2 ^ (s+1) + 4 ^ (s-d)`.  The correction shrinks from `X := 4 ^ (s-d)` to
`(2*X + 4) / 3` — strictly smaller for `d ≤ s-2` (`sharp_strictly_beats_C6`), a
saving tending to a third of `X`; and `late_largest_skip_bound_sharp` shows the new
bound is *equal* to `w d - ∑_{j>d} w j`, hence the best bound the hypothesis
"rank `d` declined, everything above taken" can ever give.  At `d = s-1` the two
coincide; the gain begins at `d = s-2`
(`remainder_lt_of_largest_skip_pred_pred`: `ρ s < 2 ^ (s+1) + 12`, versus `+16`).
Anti-vacuity: `sharp_bound_sixteen`, `remainder_sixteen_lt_sharp`,
`sharp_bound_fourteen`, off `RemC6`'s own `SeamSkipsLast` witnesses.

## §3 — the excess candidate, refuted (PROVED negative)

Any family `d ↦ 2 ^ (2*s-d) + c d` that propagates blind through the greedy step
is a `T1.IntervalCeiling`, so `T1.IntervalCeiling.four_pow_le` applies.
`correction_ge`: for `s ≥ 12` the correction at the terminal rank already
satisfies `2 ^ (2*s-7) ≤ c (s-1)` — larger than the target `2 ^ (s+1)` by the
factor `2 ^ (s-8)`.  `tailCorrected_not_intervalCeiling` instantiates this at the
brief's own candidate: `d ↦ 2 ^ (2*s-d) + weightTail s d` is not an
`IntervalCeiling`, and the *narrowed* `d ↦ 2 ^ (2*s-d) - weightTail s d` is
smaller still, hence excluded a fortiori.  Anti-vacuity: `correction_ge_trivial`.

## §4 — the two-sided candidate, and its exact price (PROVED negative)

`PairCeiling s` is the two-sided analogue of `T1.IntervalCeiling`: a family
`[lo d, hi d)` transported through the greedy step blind to the branch.  A lower
bound really does escape `T1`'s no-go — `w (d+1) ≤ lo d` *excludes the declined
branch*.  The price:

* `lo_succ_eq_zero`: as soon as `w (d+1)` lies strictly inside `[lo d, hi d)`
  (the family **splits**), the lower bound collapses to `0` at the next rank and
  never recovers (`zero_lo_forever`).
* `terminal_ge_of_splits`: a family that splits at any rank `a ≤ s-3` has
  `2 ^ (s+1) + 4 ≤ hi (s-1)` — it cannot even match `T1`'s weight ceiling.
* `branches_decided_of_terminal_lt`: hence a two-sided invariant with
  `hi (s-1) < 2 ^ (s+1) + 4` must satisfy, at every rank `d ≤ s-2`,

      `w (d+1) ≤ R d  ↔  w (d+1) ≤ lo d`,

  i.e. **its lower bound alone decides whether every rank is taken or declined.**
  The two-sided strengthening buys nothing it is not given.

Anti-vacuity: `orbit` (the exact orbit; a `PairCeiling` that never splits — the
answer-encoding family the theorem describes) and `loose` with
`loose_splitsAt_two` / `loose_terminal_ge` (a `PairCeiling` that does split).

## §5 — a side condition at declined ranks (PROVED, narrower than the side condition)

`lateEntryRemainder_eq`: `BitCorr.lateEntryRemainder s d = T1.seamResidualUpto s (d-1)`
— the two objects are the same greedy residual (proved through
`integerGreedyRemainder_seamWeights_take`).  Since
`2 ^ (2*s-d+1) = 2 ^ (2*s-(d-1))`, the side condition

    hhigh : lateEntryRemainder s d < 2 ^ (2*s-d+1)

*is* C6's invariant at rank `d-1`, and §1 delivers it:
`lateEntryRemainder_lt_two_pow_of_declined` — **`hhigh` holds unconditionally at
every declined rank `d`.**  This does not touch the second side condition
`hlow`.  That condition is now known to be false in general:
`Decl/D4.not_hlow_seven_five` and `Hlow/H1.not_hlow_of_hhigh` certify failure at
`(s,d) = (7,5)`, while `Hlow/H2` shows such a failure is a half-point hit
certificate rather than an obstruction.  Anti-vacuity: `hhigh_twenty_fifteen`
(`Bit/Corr1`'s worked row `s = 20`, one rank past its own `d = 14`, which is
taken and therefore outside the lemma's reach).

This is not a general discharge of `hhigh`: “rank `d` is declined” is a
strictly stronger hypothesis than `hhigh`, and the implication is already a
direct consequence of `RemC6.truncatedMersenneWeight_le`.  Measured at the
first late rank, `hhigh` holds on rows where the rank is not declined, so this
lemma covers strictly fewer cases than the original side condition.

## Measured, not proved

Nothing in this file is asserted without proof.  The measurement note at the end
records an independent re-scan of the facts the file leans on rhetorically
(the uniqueness of the `(13,7)` break, the forced-take law, the exact suffix-sum
identity, the sharp bound) over `s ∈ [6, 1500]`.
-/

namespace ErdosProblems.Decl.D1

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems.Three.T1

/-- The rank-`d` weight above its top bit. -/
def weightTail (s d : ℕ) : ℕ := truncatedMersenneWeight s d - 2 ^ (2 * s - d)

theorem weight_eq_top_add_tail {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ 2 * s) :
    truncatedMersenneWeight s d = 2 ^ (2 * s - d) + weightTail s d := by
  have h := RemC6.two_pow_le_truncatedMersenneWeight hd hds
  simp only [weightTail]
  omega

theorem weightTail_le {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ s) :
    weightTail s d ≤ 2 ^ (2 * s - 2 * d + 1) := by
  have h := RemC6.truncatedMersenneWeight_le hd hds
  have he : 0 < (2 : ℕ) ^ (2 * s - 2 * d) := pow_pos (by norm_num) _
  simp only [weightTail]
  omega

/-- **The forced-take lemma.**  If the residual after rank `d` is at least the
top bit `2 ^ (2 * s - d)` of the rank-`d` weight, then rank `d + 1` is taken:
the whole rank-`(d+1)` weight already fits. -/
theorem weight_succ_le_of_two_pow_le {s d : ℕ} (hd : 1 ≤ d) (hds : d + 1 ≤ s)
    (h : 2 ^ (2 * s - d) ≤ seamResidualUpto s d) :
    truncatedMersenneWeight s (d + 1) ≤ seamResidualUpto s d := by
  have hup := RemC6.truncatedMersenneWeight_le (s := s) (d := d + 1) (by omega) hds
  have hcmp : (2 : ℕ) ^ (2 * s - 2 * (d + 1) + 1) ≤ 2 ^ (2 * s - (d + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdbl : (2 : ℕ) ^ (2 * s - d) = 2 ^ (2 * s - (d + 1)) + 2 ^ (2 * s - (d + 1)) := by
    rw [show 2 * s - d = (2 * s - (d + 1)) + 1 by omega, pow_succ]; ring
  omega

/-- **Contrapositive: C6's invariant holds for free at every rank that precedes
a decline.**  No induction, no hypothesis. -/
theorem residual_lt_two_pow_of_declined {s d : ℕ} (hd : 1 ≤ d) (hds : d + 1 ≤ s)
    (hdecl : seamResidualUpto s d < truncatedMersenneWeight s (d + 1)) :
    seamResidualUpto s d < 2 ^ (2 * s - d) := by
  by_contra hc
  exact absurd (weight_succ_le_of_two_pow_le hd hds (by omega)) (by omega)

/-! ### The broken state, and what happens next -/

/-- **The broken state at rank `d`**: the residual has escaped C6's ceiling
`2 ^ (2 * s - d)` but is still trapped below the rank-`d` weight.  By
`invariant_step_dichotomy` this is the *only* way C6's invariant can fail, and by
`residual_lt_two_pow_of_declined` it can only be produced by a decline. -/
def BrokenAt (s d : ℕ) : Prop :=
  2 ^ (2 * s - d) ≤ seamResidualUpto s d ∧
    seamResidualUpto s d < truncatedMersenneWeight s d

/-- From the broken state, rank `d + 1` is **forced taken**. -/
theorem BrokenAt.taken {s d : ℕ} (hd : 1 ≤ d) (hds : d + 1 ≤ s) (h : BrokenAt s d) :
    truncatedMersenneWeight s (d + 1) ≤ seamResidualUpto s d :=
  weight_succ_le_of_two_pow_le hd hds h.1

/-- Hence **two consecutive breaks are impossible**: a break at rank `d` cannot
be followed by a decline at rank `d + 1`, so the tangency window of
`T1.invariant_step_dichotomy` cannot be entered twice in a row. -/
theorem BrokenAt.not_declined_succ {s d : ℕ} (hd : 1 ≤ d) (hds : d + 1 ≤ s)
    (h : BrokenAt s d) :
    ¬ seamResidualUpto s d < truncatedMersenneWeight s (d + 1) := by
  have := h.taken hd hds
  omega

theorem BrokenAt.residual_succ {s d : ℕ} (hd : 1 ≤ d) (hds : d + 1 ≤ s)
    (h : BrokenAt s d) :
    seamResidualUpto s (d + 1) = seamResidualUpto s d - truncatedMersenneWeight s (d + 1) := by
  rw [seamResidualUpto_succ hd, if_pos (h.taken hd hds)]

/-- The excess above the ceiling is bounded by the tail of the rank-`d` weight. -/
theorem BrokenAt.excess_lt {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ 2 * s) (h : BrokenAt s d) :
    seamResidualUpto s d - 2 ^ (2 * s - d) < weightTail s d := by
  have := weight_eq_top_add_tail (s := s) (d := d) hd hds
  have := h.1
  have := h.2
  omega

/-- **The strongest unconditional statement about the step after a break.**  The
excess is carried forward undamaged: the residual at rank `d + 1` is below the
*halved* ceiling plus the rank-`d` tail. -/
theorem BrokenAt.residual_succ_lt {s d : ℕ} (hd : 1 ≤ d) (hds : d + 1 ≤ s)
    (h : BrokenAt s d) :
    seamResidualUpto s (d + 1) < 2 ^ (2 * s - (d + 1)) + weightTail s d := by
  have hstep := h.residual_succ hd hds
  have hwd := weight_eq_top_add_tail (s := s) (d := d) hd (by omega)
  have hws := weight_eq_top_add_tail (s := s) (d := d + 1) (by omega) (by omega)
  have hdbl : (2 : ℕ) ^ (2 * s - d) = 2 ^ (2 * s - (d + 1)) + 2 ^ (2 * s - (d + 1)) := by
    rw [show 2 * s - d = (2 * s - (d + 1)) + 1 by omega, pow_succ]; ring
  have := h.2
  omega

/-- **When the break repairs itself.**  If the excess is below the *next* tail,
C6's invariant is restored one rank later.  This is the exact repair condition:
`R d < 2 ^ (2*s-d) + weightTail s (d+1)` is equivalent to
`R (d+1) < 2 ^ (2*s-d-1)` in the broken state. -/
theorem BrokenAt.restored {s d : ℕ} (hd : 1 ≤ d) (hds : d + 1 ≤ s) (h : BrokenAt s d)
    (hsmall : seamResidualUpto s d < 2 ^ (2 * s - d) + weightTail s (d + 1)) :
    seamResidualUpto s (d + 1) < 2 ^ (2 * s - (d + 1)) := by
  have hstep := h.residual_succ hd hds
  have htk := h.taken hd hds
  have hws := weight_eq_top_add_tail (s := s) (d := d + 1) (by omega) (by omega)
  have hdbl : (2 : ℕ) ^ (2 * s - d) = 2 ^ (2 * s - (d + 1)) + 2 ^ (2 * s - (d + 1)) := by
    rw [show 2 * s - d = (2 * s - (d + 1)) + 1 by omega, pow_succ]; ring
  omega

/-- Conversely the repair condition is necessary. -/
theorem BrokenAt.not_restored {s d : ℕ} (hd : 1 ≤ d) (hds : d + 1 ≤ s) (h : BrokenAt s d)
    (hbig : 2 ^ (2 * s - d) + weightTail s (d + 1) ≤ seamResidualUpto s d) :
    2 ^ (2 * s - (d + 1)) ≤ seamResidualUpto s (d + 1) := by
  have hstep := h.residual_succ hd hds
  have htk := h.taken hd hds
  have hws := weight_eq_top_add_tail (s := s) (d := d + 1) (by omega) (by omega)
  have hdbl : (2 : ℕ) ^ (2 * s - d) = 2 ^ (2 * s - (d + 1)) + 2 ^ (2 * s - (d + 1)) := by
    rw [show 2 * s - d = (2 * s - (d + 1)) + 1 by omega, pow_succ]; ring
  omega

/-! ### Anti-vacuity: the unique break of the corpus, at `s = 13`, `d = 7`

`T1.not_residualInvariant` locates the sole failure of C6's invariant over
`s ∈ [6, 3000]` at `(13, 7)`.  Everything above is exhibited there. -/

theorem brokenAt_thirteen_seven : BrokenAt 13 7 := by
  refine ⟨?_, ?_⟩
  · rw [seamResidualUpto_thirteen_seven]; norm_num
  · rw [seamResidualUpto_thirteen_seven]; norm_num [truncatedMersenneWeight]

theorem seamResidualUpto_thirteen_eight : seamResidualUpto 13 8 = 261247 := by
  norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

/-- Rank `8` is forced taken at `s = 13`, and the break repairs itself: the
residual `261247` is back below `2 ^ (2 * 13 - 8) = 262144`. -/
theorem thirteen_break_repairs :
    truncatedMersenneWeight 13 8 ≤ seamResidualUpto 13 7 ∧
      seamResidualUpto 13 8 < 2 ^ (2 * 13 - 8) := by
  refine ⟨brokenAt_thirteen_seven.taken (by norm_num) (by norm_num), ?_⟩
  rw [seamResidualUpto_thirteen_eight]; norm_num

/-- **Why the repair is not automatic.**  Restoration needs the excess to fall
below the *next* tail, and the tails shrink by a factor of about `4` per rank:
already at `s = 13`, `d = 6` one has `weightTail = 16644` while
`2 * weightTail (d+1) = 8256`.  So the one-step repair condition
`weightTail s d ≤ 2 * weightTail s (d + 1)` fails, and the excess produced by a
break is in general too large for the next rank to absorb. -/
theorem weightTail_fails_halving : ¬ weightTail 13 6 ≤ 2 * weightTail 13 7 := by
  norm_num [weightTail, truncatedMersenneWeight]

/-! ## 2. The exact tail of the weight word, and a sharpening of C6 §5

`RemC6.seamWeightsFrom_sum_lower` bounds the suffix sum from below by the sum of
the *top bits* alone, `2 ^ (2*s-a+1) - 2 ^ (s+1)`.  Past two thirds of the row
every weight is exactly two bits (`RemC6.truncatedMersenneWeight_late`), so the
suffix sum can be computed **exactly**, second bits included.  Doing so shrinks
the error term of C6's headline bound towards two thirds of its value. -/

private theorem sum_exact_aux (s : ℕ) :
    ∀ n : ℕ, 3 * n < s →
      3 * (seamWeightsFrom s (s - n)).sum + 3 * 2 ^ (s + 1) + 4
        = 3 * 2 ^ (s + n + 1) + 4 ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [Nat.sub_zero, seamWeightsFrom_eq_nil (le_refl s)]
      norm_num
  | succ n ih =>
      intro hn
      have hIH := ih (by omega)
      have hlt : s - (n + 1) < s := by omega
      have heq : s - (n + 1) + 1 = s - n := by omega
      have hw : truncatedMersenneWeight s (s - (n + 1))
          = 2 ^ (s + n + 1) + 4 ^ (n + 1) := by
        have h := RemC6.truncatedMersenneWeight_late (s := s) (d := s - (n + 1))
          (by omega) (by omega) (by omega)
        rw [h, show 2 * s - (s - (n + 1)) = s + n + 1 by omega,
          show 2 * s - 2 * (s - (n + 1)) = 2 * (n + 1) by omega, pow_mul]
        norm_num
      have hdbl : (2 : ℕ) ^ (s + (n + 1) + 1) = 2 ^ (s + n + 1) + 2 ^ (s + n + 1) := by
        rw [show s + (n + 1) + 1 = (s + n + 1) + 1 by omega, pow_succ]; ring
      have hfour : (4 : ℕ) ^ (n + 1 + 1) = 4 * 4 ^ (n + 1) := by rw [pow_succ]; ring
      rw [seamWeightsFrom_eq_cons hlt, List.sum_cons, heq, hw]
      omega

/-- **The exact suffix sum.**  For `a` past two thirds of the row,
`∑_{j = a}^{s-1} w j = 2 ^ (2*s-a+1) - 2 ^ (s+1) + (4 ^ (s-a+1) - 4) / 3`,
written without division. -/
theorem seamWeightsFrom_sum_exact {s a : ℕ} (ha : a ≤ s) (hlate : 2 * s < 3 * a) :
    3 * (seamWeightsFrom s a).sum + 3 * 2 ^ (s + 1) + 4
      = 3 * 2 ^ (2 * s - a + 1) + 4 ^ (s - a + 1) := by
  have h := sum_exact_aux s (s - a) (by omega)
  rw [show s - (s - a) = a by omega] at h
  rw [show 2 * s - a + 1 = s + (s - a) + 1 by omega]
  exact h

/-- Consistency check: the exact sum implies `RemC6.seamWeightsFrom_sum_lower`. -/
theorem sum_exact_implies_C6_lower {s a : ℕ} (ha : a ≤ s)
    (hlate : 2 * s < 3 * a) :
    2 ^ (2 * s - a + 1) ≤ (seamWeightsFrom s a).sum + 2 ^ (s + 1) := by
  have h := seamWeightsFrom_sum_exact ha hlate
  have hpos : 0 < (4 : ℕ) ^ (s - a + 1) := pow_pos (by norm_num) _
  omega

/-- **The sharpened largest-declined-rank bound.**  If `d` is the largest rank
declined by the seam greedy of row `s` and `d` is past two thirds of the row,
then `3 * ρ s < 3 * 2 ^ (s+1) + 2 * 4 ^ (s-d) + 4`, i.e.
`ρ s < 2 ^ (s+1) + (2 * 4 ^ (s-d) + 4) / 3`.

C6's `seamIntegerGreedyRemainder_lt_of_late_largest_skip` gives
`ρ s < 2 ^ (s+1) + 4 ^ (s-d)`.  The correction term drops from `4 ^ (s-d)` to
`(2 * 4 ^ (s-d) + 4) / 3`: what C6 discards, and this recovers, is the sum of the
*second* bits of the weights above `d`. -/
theorem remainder_lt_of_late_largest_skip_sharp {s d : ℕ}
    (hd : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d) (h : RemC6.SeamSkipsLast s d) :
    3 * seamIntegerGreedyRemainder s < 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 := by
  obtain ⟨R, hR1, hR2, hR3⟩ := RemC6.seamIntegerGreedyRemainder_eq_of_skipsLast hds h
  rw [RemC6.truncatedMersenneWeight_late hd hds hlate,
    show 2 * s - 2 * d = 2 * (s - d) by omega, pow_mul,
    show ((2 : ℕ) ^ 2) = 4 by norm_num] at hR1
  have hsum := seamWeightsFrom_sum_exact (s := s) (a := d + 1) (by omega) (by omega)
  rw [show 2 * s - (d + 1) + 1 = 2 * s - d by omega,
    show s - (d + 1) + 1 = s - d by omega] at hsum
  omega

/-- **The bound is sharp for its hypothesis.**  `w d` minus the exact sum of all
higher weights is *equal* to the bound, so no better estimate follows from
"rank `d` is declined and every higher rank is taken" alone. -/
theorem late_largest_skip_bound_sharp {s d : ℕ}
    (hd : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d) :
    3 * truncatedMersenneWeight s d
      = 3 * (seamWeightsFrom s (d + 1)).sum + 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 := by
  have hsum := seamWeightsFrom_sum_exact (s := s) (a := d + 1) (by omega) (by omega)
  rw [show 2 * s - (d + 1) + 1 = 2 * s - d by omega,
    show s - (d + 1) + 1 = s - d by omega] at hsum
  rw [RemC6.truncatedMersenneWeight_late hd hds hlate,
    show 2 * s - 2 * d = 2 * (s - d) by omega, pow_mul,
    show ((2 : ℕ) ^ 2) = 4 by norm_num]
  omega

/-- The terminal case `d = s - 1` reproduces C6 exactly (`ρ s < 2 ^ (s+1) + 4`);
the gain begins at `d = s - 2`. -/
theorem remainder_lt_of_largest_skip_pred_pred {s : ℕ} (hs : 7 ≤ s)
    (h : RemC6.SeamSkipsLast s (s - 2)) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 12 := by
  have hb := remainder_lt_of_late_largest_skip_sharp (s := s) (d := s - 2)
    (by omega) (by omega) (by omega) h
  rw [show s - (s - 2) = 2 by omega] at hb
  norm_num at hb
  omega

/-- **The improvement, made explicit.**  For `d ≤ s - 2` the sharpened right-hand
side is strictly below three times C6's, so `remainder_lt_of_late_largest_skip_sharp`
strictly implies `RemC6.seamIntegerGreedyRemainder_lt_of_late_largest_skip`. -/
theorem sharp_strictly_beats_C6 {s d : ℕ} (hds : d + 2 ≤ s) :
    3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 < 3 * (2 ^ (s + 1) + 2 ^ (2 * s - 2 * d)) := by
  have he : (2 : ℕ) ^ (2 * s - 2 * d) = 4 ^ (s - d) := by
    rw [show 2 * s - 2 * d = 2 * (s - d) by omega, pow_mul]; norm_num
  have hbig : (16 : ℕ) ≤ 4 ^ (s - d) := by
    calc (16 : ℕ) = 4 ^ 2 := by norm_num
    _ ≤ 4 ^ (s - d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ### Anti-vacuity for §2

`RemC6.SeamSkipsLast` is inhabited at rows `14` and `16`, both with a late
largest declined rank, so both bounds above are statements about a non-empty
hypothesis. -/

theorem sharp_bound_sixteen :
    3 * seamIntegerGreedyRemainder 16 < 3 * 2 ^ (16 + 1) + 2 * 4 ^ (16 - 14) + 4 :=
  remainder_lt_of_late_largest_skip_sharp (by norm_num) (by norm_num) (by norm_num)
    RemC6.seamSkipsLast_sixteen_fourteen

/-- Row `16`: the sharpened bound is `ρ 16 < 2 ^ 17 + 12 = 131084`, against C6's
`ρ 16 < 2 ^ 17 + 16 = 131088`.  (True value `71791`.) -/
theorem remainder_sixteen_lt_sharp : seamIntegerGreedyRemainder 16 < 2 ^ 17 + 12 := by
  have h := sharp_bound_sixteen
  norm_num at h
  omega

theorem sharp_bound_fourteen :
    3 * seamIntegerGreedyRemainder 14 < 3 * 2 ^ (14 + 1) + 2 * 4 ^ (14 - 13) + 4 :=
  remainder_lt_of_late_largest_skip_sharp (by norm_num) (by norm_num) (by norm_num)
    RemC6.seamSkipsLast_fourteen_thirteen

/-! ## 3. Correcting C6's ceiling by a rank-indexed excess is hopeless

The first candidate in the brief was `R k < 2 ^ (2*s-k) - (tail of lower binary
terms of w k)`, or more generally `R k < 2 ^ (2*s-k) ± c k`.  Any such family is
an `T1.IntervalCeiling`, so `T1.IntervalCeiling.four_pow_le` applies and fixes
how large the correction must be: **at the terminal rank it must exceed
`2 ^ (2*s-7)`**, i.e. it must be larger than the target `2 ^ (s+1)` by the factor
`2 ^ (s-8)`.  Subtracting a tail is a fortiori excluded. -/

open Three.T1 in
/-- **The correction floor.**  Whatever rank-indexed correction `c` is bolted
onto C6's ceiling, at the terminal rank it is already at least `2 ^ (2*s-7)`. -/
theorem correction_ge {s : ℕ} (hs : 12 ≤ s) (K : IntervalCeiling s) (c : ℕ)
    (hK : K.bound (s - 1) ≤ 2 ^ (s + 1) + c) :
    2 ^ (2 * s - 7) ≤ c := by
  have h := K.four_pow_le (by omega)
  have h4 : (4 : ℕ) ^ s = 128 * 2 ^ (2 * s - 7) := by
    rw [show (4 : ℕ) ^ s = 2 ^ (2 * s) by rw [pow_mul]; norm_num,
      show 2 * s = 7 + (2 * s - 7) by omega, pow_add]
    norm_num
  have hXP : 32 * 2 ^ s ≤ 2 ^ (2 * s - 7) := by
    calc 32 * (2 : ℕ) ^ s = 2 ^ (s + 5) := by rw [pow_add]; ring
    _ ≤ 2 ^ (2 * s - 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hP : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hpos : 0 < (2 : ℕ) ^ s := pow_pos (by norm_num) _
  omega

open Three.T1 in
/-- **Anti-vacuity for `correction_ge`.**  The hypothesis is inhabited: the
trivial ceiling with the trivial correction. -/
theorem correction_ge_trivial {s : ℕ} (hs : 12 ≤ s) :
    2 ^ (2 * s - 7) ≤ seamSubsetTarget s + 1 :=
  correction_ge hs (trivialCeiling s) (seamSubsetTarget s + 1) (by simp [trivialCeiling])

open Three.T1 in
/-- **The brief's candidate, refuted.**  The family
`d ↦ 2 ^ (2*s-d) + weightTail s d` — C6's ceiling widened by exactly the lower
binary terms of the rank-`d` weight, the largest widening the brief proposed —
is not an `IntervalCeiling`, because at the terminal rank its correction is `4`
and the floor is `2 ^ (2*s-7)`.  The *narrowed* family
`d ↦ 2 ^ (2*s-d) - weightTail s d` is smaller still, hence excluded a fortiori. -/
theorem tailCorrected_not_intervalCeiling {s : ℕ} (hs : 12 ≤ s) :
    ¬ ∃ K : IntervalCeiling s, K.bound = fun d => 2 ^ (2 * s - d) + weightTail s d := by
  rintro ⟨K, hK⟩
  have hterm : weightTail s (s - 1) = 4 := by
    have h := RemC6.truncatedMersenneWeight_terminal (s := s) (by omega)
    simp only [weightTail, h, show 2 * s - (s - 1) = s + 1 by omega]
    omega
  have hb : K.bound (s - 1) ≤ 2 ^ (s + 1) + 4 := by
    rw [hK]
    simp only [show 2 * s - (s - 1) = s + 1 by omega, hterm, le_refl]
  have := correction_ge hs K 4 hb
  have h16 : (2 : ℕ) ^ 4 ≤ 2 ^ (2 * s - 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h16
  omega

/-! ## 4. Two-sided invariants: the lower bound must encode the answer

The brief's second candidate was "a two-sided invariant tracking `R k` relative
to `w (k+1)` rather than to a pure power of two".  A lower bound genuinely
escapes `T1.IntervalCeiling`: knowing `w (d+1) ≤ R d` *excludes the declined
branch*, which is exactly the branch that breaks the induction.  This section
determines the price.

A `PairCeiling` is the two-sided analogue of `T1.IntervalCeiling`: it carries
`[lo d, hi d)` and must transport it through the greedy step blind to which
branch is taken. -/

open Three.T1 in
/-- A branch-blind two-sided invariant for the rank recursion of row `s`. -/
structure PairCeiling (s : ℕ) where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  start_lo : lo 2 ≤ seamResidualUpto s 2
  start_hi : seamResidualUpto s 2 < hi 2
  step : ∀ d, 2 ≤ d → d + 1 < s → ∀ r : ℕ, lo d ≤ r → r < hi d →
    lo (d + 1) ≤ greedyStep s (d + 1) r ∧ greedyStep s (d + 1) r < hi (d + 1)

namespace PairCeiling

open Three.T1

variable {s : ℕ}

/-- **Soundness.**  A `PairCeiling` really does trap the residual. -/
theorem sound (K : PairCeiling s) :
    ∀ d, 2 ≤ d → d < s → K.lo d ≤ seamResidualUpto s d ∧ seamResidualUpto s d < K.hi d := by
  intro d
  induction d with
  | zero => intro h; omega
  | succ d ih =>
      intro h2 hlt
      rcases Nat.lt_or_ge d 2 with hd | hd
      · rw [show d + 1 = 2 by omega]; exact ⟨K.start_lo, K.start_hi⟩
      · obtain ⟨h1, h2'⟩ := ih hd (by omega)
        have := K.step d hd hlt (seamResidualUpto s d) h1 h2'
        rwa [← seamResidualUpto_succ_eq_greedyStep (by omega : 1 ≤ d)] at this

/-- The family **splits** at rank `d` when the rank-`(d+1)` weight lies strictly
inside `[lo d, hi d)`: then the invariant cannot tell whether rank `d + 1` is
taken or declined. -/
def SplitsAt (K : PairCeiling s) (d : ℕ) : Prop :=
  K.lo d < truncatedMersenneWeight s (d + 1) ∧ truncatedMersenneWeight s (d + 1) < K.hi d

/-- **A split destroys the lower bound at the very next rank.** -/
theorem lo_succ_eq_zero {K : PairCeiling s} {d : ℕ} (hd : 2 ≤ d) (hds : d + 1 < s)
    (h : K.SplitsAt d) : K.lo (d + 1) = 0 := by
  obtain ⟨hlo, hhi⟩ := h
  have := (K.step d hd hds (truncatedMersenneWeight s (d + 1)) (by omega) hhi).1
  rw [greedyStep, if_pos (le_refl _), Nat.sub_self] at this
  omega

/-- A split also forces the upper bound at the next rank up to the whole weight. -/
theorem weight_le_hi_succ {K : PairCeiling s} {d : ℕ} (hd : 2 ≤ d) (hds : d + 1 < s)
    (hw : 0 < truncatedMersenneWeight s (d + 1)) (h : K.SplitsAt d) :
    truncatedMersenneWeight s (d + 1) ≤ K.hi (d + 1) := by
  obtain ⟨hlo, hhi⟩ := h
  have hr : K.lo d ≤ truncatedMersenneWeight s (d + 1) - 1 := by omega
  have hr2 : truncatedMersenneWeight s (d + 1) - 1 < K.hi d := by omega
  have := (K.step d hd hds _ hr hr2).2
  rw [greedyStep, if_neg (by omega)] at this
  omega

theorem weight_pos {d : ℕ} (hd : 1 ≤ d) (hds : d ≤ 2 * s) :
    0 < truncatedMersenneWeight s d := by
  have h := RemC6.two_pow_le_truncatedMersenneWeight (s := s) (d := d) hd hds
  have : 0 < (2 : ℕ) ^ (2 * s - d) := pow_pos (by norm_num) _
  omega

/-- **Once the lower bound is `0` it stays `0`, and the upper bound then obeys
exactly the `declined` obligation of `T1.IntervalCeiling`.** -/
theorem zero_lo_step {K : PairCeiling s} {d : ℕ} (hd : 2 ≤ d) (hds : d + 1 < s)
    (h0 : K.lo d = 0) :
    K.lo (d + 1) = 0 ∧ min (K.hi d) (truncatedMersenneWeight s (d + 1)) ≤ K.hi (d + 1) := by
  have hwpos : 0 < truncatedMersenneWeight s (d + 1) := weight_pos (by omega) (by omega)
  have hhipos : 0 < K.hi d := lt_of_le_of_lt (Nat.zero_le _) (K.sound d hd (by omega)).2
  have h1 := K.step d hd hds 0 (by omega) (by omega)
  rw [greedyStep, if_neg (by omega)] at h1
  refine ⟨by omega, ?_⟩
  rcases lt_or_ge (truncatedMersenneWeight s (d + 1)) (K.hi d) with hc | hc
  · rw [min_eq_right (le_of_lt hc)]
    exact weight_le_hi_succ hd hds hwpos ⟨by omega, hc⟩
  · rw [min_eq_left hc]
    have h2 := K.step d hd hds (K.hi d - 1) (by omega) (by omega)
    rw [greedyStep, if_neg (by omega)] at h2
    omega

theorem zero_lo_forever {K : PairCeiling s} {a : ℕ} (ha : 2 ≤ a) (h0 : K.lo a = 0) :
    ∀ d, a ≤ d → d < s → K.lo d = 0 := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => intro _; exact h0
  | succ d hd ih =>
      intro hlt
      exact (zero_lo_step (by omega) hlt (ih (by omega))).1

theorem declined_obligation {K : PairCeiling s} {a : ℕ} (ha : 2 ≤ a) (h0 : K.lo a = 0) :
    ∀ d, a ≤ d → d + 1 < s →
      min (K.hi d) (truncatedMersenneWeight s (d + 1)) ≤ K.hi (d + 1) :=
  fun d hd hds => (zero_lo_step (by omega) hds (zero_lo_forever ha h0 d hd (by omega))).2

/-- **The price of a split.**  If a two-sided invariant splits at any rank
`a ≤ s - 3`, its terminal bound is at least `2 ^ (s+1) + 4`: it cannot even match
the (measured) weight ceiling of `T1`, let alone reach `2 ^ (s+1)`. -/
theorem terminal_ge_of_splits {K : PairCeiling s} {a : ℕ} (ha : 2 ≤ a) (has : a + 3 ≤ s)
    (h : K.SplitsAt a) :
    2 ^ (s + 1) + 4 ≤ K.hi (s - 1) := by
  have hwpos : 0 < truncatedMersenneWeight s (a + 1) := weight_pos (by omega) (by omega)
  have h0 : K.lo (a + 1) = 0 := lo_succ_eq_zero ha (by omega) h
  have hw : truncatedMersenneWeight s (a + 1) ≤ K.hi (a + 1) :=
    weight_le_hi_succ ha (by omega) hwpos h
  have hlow : (2 : ℕ) ^ (2 * s - (a + 1)) ≤ truncatedMersenneWeight s (a + 1) :=
    RemC6.two_pow_le_truncatedMersenneWeight (by omega) (by omega)
  have hbig : (2 : ℕ) ^ (s + 2) ≤ 2 ^ (2 * s - (a + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hterm := declined_floor_terminal (s := s) (a := a + 1) (B := K.hi)
    (by omega) (by omega) (by omega) (declined_obligation (by omega) h0)
  have e2 : (2 : ℕ) ^ (s + 2) = 4 * 2 ^ s := by rw [pow_add]; ring
  have e1 : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hpos : (4 : ℕ) ≤ 2 ^ s := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [min_eq_right (by omega)] at hterm
  exact hterm

/-- Contrapositive. -/
theorem not_splitsAt_of_terminal_lt {K : PairCeiling s}
    (hterm : K.hi (s - 1) < 2 ^ (s + 1) + 4) :
    ∀ a, 2 ≤ a → a + 3 ≤ s → ¬ K.SplitsAt a := by
  intro a ha has h
  have := terminal_ge_of_splits ha has h
  omega

/-- **What a non-split costs.**  Where the invariant does not split, its own data
already decides the branch: rank `d + 1` is taken **iff** the lower bound alone
says so.  No reference to the residual is needed. -/
theorem branch_decided {K : PairCeiling s} {d : ℕ} (hd : 2 ≤ d) (hds : d < s)
    (hns : ¬ K.SplitsAt d) :
    truncatedMersenneWeight s (d + 1) ≤ seamResidualUpto s d
      ↔ truncatedMersenneWeight s (d + 1) ≤ K.lo d := by
  obtain ⟨hl, hh⟩ := K.sound d hd hds
  rw [SplitsAt, not_and_or, not_lt, not_lt] at hns
  constructor
  · intro _
    rcases hns with hc | hc
    · exact hc
    · omega
  · intro h; omega

/-- **The dichotomy, assembled.**  A two-sided invariant whose terminal bound
beats `2 ^ (s+1) + 4` must decide, from its own lower bound alone, whether every
rank up to `s - 2` is taken or declined.  The lower bound does escape
`T1.IntervalCeiling` — but only by carrying the decline pattern of row `s`
inside it. -/
theorem branches_decided_of_terminal_lt {K : PairCeiling s}
    (hterm : K.hi (s - 1) < 2 ^ (s + 1) + 4) :
    ∀ d, 2 ≤ d → d + 3 ≤ s →
      (truncatedMersenneWeight s (d + 1) ≤ seamResidualUpto s d
        ↔ truncatedMersenneWeight s (d + 1) ≤ K.lo d) :=
  fun d hd hds =>
    branch_decided hd (by omega) (not_splitsAt_of_terminal_lt hterm d hd hds)

/-! ### Anti-vacuity for §4 -/

/-- The **exact orbit** is a `PairCeiling`, and it never splits.  So the
non-splitting class of `branches_decided_of_terminal_lt` is inhabited — by
precisely the family that already contains the answer. -/
def orbit (s : ℕ) : PairCeiling s where
  lo := fun d => seamResidualUpto s d
  hi := fun d => seamResidualUpto s d + 1
  start_lo := le_refl _
  start_hi := Nat.lt_succ_self _
  step := by
    intro d hd hds r h1 h2
    have hr : r = seamResidualUpto s d := by omega
    subst hr
    rw [← seamResidualUpto_succ_eq_greedyStep (by omega : 1 ≤ d)]
    exact ⟨le_refl _, Nat.lt_succ_self _⟩

theorem orbit_never_splits (s d : ℕ) : ¬ (orbit s).SplitsAt d := by
  rintro ⟨h1, h2⟩
  simp only [orbit] at h1 h2
  omega

/-- A `PairCeiling` that **does** split: the trivial two-sided family.  So
`terminal_ge_of_splits` is not vacuous either. -/
def loose (s : ℕ) : PairCeiling s where
  lo := fun _ => 0
  hi := fun _ => seamSubsetTarget s + 1
  start_lo := Nat.zero_le _
  start_hi := by
    have : seamResidualUpto s 2 ≤ seamSubsetTarget s := by
      simp only [seamResidualUpto, seamResidual]
      split <;> omega
    omega
  step := by
    intro d hd hds r _ h2
    refine ⟨Nat.zero_le _, ?_⟩
    rw [greedyStep]
    split <;> omega

theorem loose_splitsAt_two {s : ℕ} (hs : 6 ≤ s) : (loose s).SplitsAt 2 := by
  have hwpos : 0 < truncatedMersenneWeight s 3 := weight_pos (by omega) (by omega)
  have hle : truncatedMersenneWeight s 3 ≤ seamResidualUpto s 2 := weight_three_le_residual hs
  have htar : seamResidualUpto s 2 ≤ seamSubsetTarget s := by
    simp only [seamResidualUpto, seamResidual]
    split <;> omega
  refine ⟨?_, ?_⟩
  · show (0 : ℕ) < truncatedMersenneWeight s 3
    exact hwpos
  · show truncatedMersenneWeight s 3 < seamSubsetTarget s + 1
    omega

theorem loose_terminal_ge {s : ℕ} (hs : 6 ≤ s) :
    2 ^ (s + 1) + 4 ≤ (loose s).hi (s - 1) :=
  terminal_ge_of_splits (by norm_num) (by omega) (loose_splitsAt_two hs)

end PairCeiling


/-! ## 5. A side condition of `Bit/Corr1` and `Three/T4`, discharged

`Bit/Corr1` and `Three/T4` carry two side conditions at a late rank `d` of row
`s`.  The first is

    hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1).

`lateEntryRemainder s d` is, by definition, the greedy residual after ranks
`2, …, d-1` — i.e. exactly `T1.seamResidualUpto s (d-1)` — and
`2 ^ (2*s-d+1) = 2 ^ (2*s-(d-1))` is exactly C6's ceiling at rank `d-1`.  So
`hhigh` *is* C6's invariant one rank early, and §1's forced-take lemma gives it
for free whenever rank `d` is declined. -/

/-- `(seamWeightsFrom s a).take (k+1)` peels one weight off the end. -/
theorem take_succ_seamWeightsFrom (s : ℕ) :
    ∀ k a : ℕ, a + k < s →
      (seamWeightsFrom s a).take (k + 1)
        = (seamWeightsFrom s a).take k ++ [truncatedMersenneWeight s (a + k)] := by
  intro k
  induction k with
  | zero =>
      intro a ha
      rw [seamWeightsFrom_eq_cons (by omega : a < s)]
      simp
  | succ k ih =>
      intro a ha
      rw [seamWeightsFrom_eq_cons (by omega : a < s), List.take_succ_cons,
        List.take_succ_cons, ih (a + 1) (by omega)]
      simp only [List.cons_append, show a + 1 + k = a + (k + 1) by omega]

/-- **The prefix greedy is `T1.seamResidual`.** -/
theorem integerGreedyRemainder_seamWeights_take (s : ℕ) :
    ∀ k, k + 2 ≤ s →
      integerGreedyRemainder ((seamWeights s).take k) (seamSubsetTarget s)
        = seamResidual s k := by
  intro k
  induction k with
  | zero => intro _; simp [seamResidual, RemC6.integerGreedyRemainder_nil]
  | succ k ih =>
      intro hk
      have hsplit := take_succ_seamWeightsFrom s k 2 (by omega)
      have hIH := ih (by omega)
      show integerGreedyRemainder ((seamWeightsFrom s 2).take (k + 1)) _ = _
      rw [hsplit, RemC6.integerGreedyRemainder_append]
      show integerGreedyRemainder [truncatedMersenneWeight s (2 + k)]
            (integerGreedyRemainder ((seamWeights s).take k) (seamSubsetTarget s)) = _
      rw [hIH, RemC6.integerGreedyRemainder_cons, RemC6.integerGreedyRemainder_nil,
        show 2 + k = k + 2 by omega]
      rfl

/-- **The bridge.**  `Bit/Corr1`'s entering remainder is `T1`'s rank residual. -/
theorem lateEntryRemainder_eq {s d : ℕ} (hd : 2 ≤ d) (hds : d ≤ s) :
    BitCorr.lateEntryRemainder s d = seamResidualUpto s (d - 1) := by
  have hdef : BitCorr.lateEntryRemainder s d
      = integerGreedyRemainder ((seamWeights s).take (d - 2)) (seamSubsetTarget s) := rfl
  rw [hdef, integerGreedyRemainder_seamWeights_take s (d - 2) (by omega)]
  simp only [seamResidualUpto, show d - 1 - 1 = d - 2 by omega]

/-- **`hhigh` is free at a declined rank.**  If the actual greedy run of row `s`
declines rank `d`, the first side condition of `Bit/Corr1` and `Three/T4` holds
at `(s, d)` unconditionally.  No induction, no measurement. -/
theorem lateEntryRemainder_lt_two_pow_of_declined {s d : ℕ} (hd : 2 ≤ d) (hds : d ≤ s)
    (h : BitCorr.lateEntryRemainder s d < truncatedMersenneWeight s d) :
    BitCorr.lateEntryRemainder s d < 2 ^ (2 * s - d + 1) := by
  rw [lateEntryRemainder_eq hd hds] at h ⊢
  have hstep := residual_lt_two_pow_of_declined (s := s) (d := d - 1) (by omega) (by omega)
    (by rw [show d - 1 + 1 = d by omega]; exact h)
  rwa [show 2 * s - (d - 1) = 2 * s - d + 1 by omega] at hstep

/-! ### Anti-vacuity for §5

`Bit/Corr1`'s worked row is `s = 20`, `d = 14`, where rank `14` is *taken*
(`lateEntryRemainder 20 14 = 67662313 ≥ w = 67112960`), so the lemma above does
not apply there and `Corr1` verifies `hhigh` numerically.  One rank later it does
apply: rank `15` of row `20` is declined. -/

theorem lateEntryRemainder_twenty_fifteen : BitCorr.lateEntryRemainder 20 15 = 549353 := by
  rw [lateEntryRemainder_eq (by norm_num) (by norm_num)]
  norm_num [seamResidualUpto, seamResidual, truncatedMersenneWeight, seamSubsetTarget]

theorem declined_twenty_fifteen :
    BitCorr.lateEntryRemainder 20 15 < truncatedMersenneWeight 20 15 := by
  rw [lateEntryRemainder_twenty_fifteen]
  norm_num [truncatedMersenneWeight]

theorem hhigh_twenty_fifteen :
    BitCorr.lateEntryRemainder 20 15 < 2 ^ (2 * 20 - 15 + 1) :=
  lateEntryRemainder_lt_two_pow_of_declined (by norm_num) (by norm_num) declined_twenty_fifteen

/-!
## Measurement note (not a theorem — recorded for the record)

Reproducing the corpus definitions from scratch (`truncatedMersenneWeight s d =
4 ^ s / (2 ^ d - 1)`, `seamSubsetTarget s = 2 ^ (2*s-1) - 2 ^ s`, the descending
greedy over ranks `2, …, s-1`) and scanning `s ∈ [6, 1500]`, every rank
`d ∈ [2, s-1]`:

* **C6's ceiling** `R d < 2 ^ (2*s-d)` fails at exactly one pair, `(s,d) = (13,7)`,
  with `R 7 = 524419` against `2 ^ 19 = 524288`.  This independently reconfirms
  `T1.not_residualInvariant` and the failure set `T1` reports; it is the whole
  failure set over the scanned range, not a summary statistic.
* **The forced-take law of §1** (`R d ≥ 2 ^ (2*s-d)` ⟹ rank `d+1` taken) has no
  violations.  It is proved above, so this is only a consistency check on the
  transcription.
* **The exact suffix-sum identity of §2** holds at every late `a` for every
  `s ∈ [6, 120]`, and at the first late `a` for every `s ∈ [6, 1500]`.
* **The sharpened bound of §2** holds at every row whose largest declined rank
  `m` is late (`2*s < 3*m`).  The three rows in `[6, 1500]` where `m` is *not*
  late are `s = 11, 12, 13`, all with `m = 7`; the hypothesis of
  `remainder_lt_of_late_largest_skip_sharp` genuinely excludes them.
* The distribution of `s - m` over `[6, 1500]` is
  `1:718, 2:367, 3:191, 4:100, 5:53, 6:30, 7:16, 8:9, 9:5, 10:2, 11:2, 12:1, 13:1`
  — geometric with ratio about `1/2`, maximum `13`.  So the correction term
  `4 ^ (s-m)` of §2 is `O(1)` for most rows but is not bounded uniformly, which
  is exactly why §2 does not yield `ρ s < 2 ^ (s+1)`.
* `ρ s < 2 ^ (s+1)` holds at every `s ∈ [6, 1500]`, and the weight ceiling
  `R d < w d` has no failures there.  Both remain **MEASURED, not proved** — this
  file does not change that.

## What is not proved

* The declined step of the rank induction is **not** closed.  §3 and §4 prove
  that the two strengthenings the brief proposed cannot close it.
* `ρ s < 2 ^ (s+1)` is **not** proved unconditionally.  §2 proves it only with an
  additive `(2 * 4 ^ (s-m) + 4) / 3`, `m` the largest declined rank, and the
  scan above shows `s - m` is unbounded.
* The second side condition of `Bit/Corr1` / `Three/T4`,
  `hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s+1)`, is untouched.
-/


end ErdosProblems.Decl.D1
