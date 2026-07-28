/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Three.T1
import ErdosProblems.Three.T4

/-!
# D3 — the single-rank side condition at the first late rank is the conclusion

`ErdosProblems/Three/T4.lean` proves `ρ s < 2 ^ (s+1)` for
`ρ s := seamIntegerGreedyRemainder s`, conditional on the two `BitCorr` side
conditions at a late rank `d` of row `s`:

* `hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1)`
* `hlow  : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)`.

`ErdosProblems/Three/T1.lean` refutes the `∀ d` form of `hhigh` (sole failure
`(s,d) = (13,7)`) and shows no branch-blind interval induction on the rank
recursion can reach `2 ^ (s+1)` (`T1.IntervalCeiling.four_pow_le`).  The brief for
this file was to attack the **single-rank** form directly, at the first late rank
`d₀ = ⌊2s/3⌋ + 1`.

The single-rank form is not refuted — it holds at every row of `[6,3000]`
(measured; §7).  But it is **not a weaker statement than the conclusion**, and
that is what is proved here.

## What is proved

**§1  The first late rank.**  `firstLate s = 2 * s / 3 + 1` is the least `d` with
`2 * s < 3 * d` (`firstLate_late`, `firstLate_least`).

**§2  The glue.**  `lateEntryRemainder_eq_seamResidualUpto`:
`BitCorr`'s entering capacity is exactly `T1`'s rank residual,
`lateEntryRemainder s d = T1.seamResidualUpto s (d - 1)`, for `2 ≤ d ≤ s`.  Hence
`hhigh_iff_residualInvariant`: `hhigh` at rank `d` *is* `T1`'s residual invariant
at the single rank `d - 1`.  The proof goes through `lateEntryRemainder_succ`,
which puts the entering capacity into the rank-by-rank greedy recursion.

Consequence, made concrete in §6: `T1`'s sole counterexample `(13,7)` is `hhigh`
failing at rank `d = 8` of row `13` (`Concrete.not_hhigh_thirteen_eight`), and
rank `8` **is not late** at `s = 13` (`2 * 13 = 26 ≥ 24 = 3 * 8`), indeed
`8 < firstLate 13 = 9`.  So the refutation of the `∀ d` form says nothing at all
about the single-rank form; that is why the two coexist.

**§3  The two structural closures, and the step they cannot cross.**

* `hhigh_of_declined` — **`hhigh` is free at every declined rank.**  If the greedy
  refuses rank `d`, the entering capacity is below the whole rank-`d` weight, and
  `RemC6.truncatedMersenneWeight_le` puts that weight below `2 ^ (2*s-d+1)`.  No
  induction, no measurement, no lateness needed.
* `hhigh_succ_of_taken`, `hhigh_of_taken_run` — `hhigh` propagates forward across
  a taken rank, hence across any run of taken ranks.
* The one step neither covers is *declined at `e`, then rank `e+1`*: there one
  knows only `lateEntryRemainder s (e+1) < truncatedMersenneWeight s e`, which
  exceeds `2 ^ (2*s-e)` by the weight's own lower binary terms.  That is exactly
  `T1.residual_lt_of_declined`, restated in these coordinates.

`seamRemainder_lt_two_pow_succ_of_declined` is the payoff: **at a declined late
rank, `T4`'s `ρ s < 2 ^ (s+1)` needs only `hlow`.**  (Sharper than
`RemC6.seamIntegerGreedyRemainder_lt_three_mul_two_pow`, which gives `3 * 2 ^ s`
from a *largest* late declined rank; and independent of it — no maximality is
used.)

**§4  The master inequality.**  `lateEntryRemainder_add_two_pow_le`: for
`2 ≤ d ≤ s`,

    lateEntryRemainder s d + 2 ^ (s+1)
        ≤ ρ s + 2 ^ (2*s-d+1) + 2 ^ (2*s-2*d+2).

The greedy cannot consume more than the weights it is offered
(`integerGreedyRemainder_ge`), and the weights from rank `d` upwards sum to at
most `2 ^ (2*s-d+1) - 2 ^ (s+1) + 2 ^ (2*s-2*d+2)` (`seamWeightsFrom_sum_upper`,
the companion of `RemC6.seamWeightsFrom_sum_lower`).  Hence

* `hhigh_of_seamRemainder_lt` — `ρ s + 2 ^ (2*s-2*d+2) < 2 ^ (s+1)` **implies**
  `hhigh` at rank `d`;
* `two_pow_le_seamRemainder_of_not_hhigh` — contrapositively, a failure of
  `hhigh` at rank `d` forces `2 ^ (s+1) ≤ ρ s + 2 ^ (2*s-2*d+2)`.

**§5  At the first late rank: the sandwich.**  At `d = firstLate s` the
second-order term is only `2 ^ (⌊2s/3⌋+2)` (`two_pow_firstLate_error_le`), so

* `hhigh_firstLate_of_seamRemainder_lt` :
  `ρ s + 2 ^ (⌊2s/3⌋+2) < 2 ^ (s+1) → hhigh at firstLate s`;
* `seamRemainder_ge_of_not_hhigh_firstLate` :
  `¬ hhigh at firstLate s → 2 ^ (s+1) ≤ ρ s + 2 ^ (⌊2s/3⌋+2)`;
* `hhigh_firstLate_sandwich` puts this beside `T4`'s implication in the other
  direction.

**This is a sharp negative, and it is the result of the file.**  `hhigh` at the
first late rank is not a technical side condition sitting below the conclusion:
under `hlow` it is *equivalent* to `ρ s < 2 ^ (s+1)`, to within the additive
`2 ^ (⌊2s/3⌋+2)` — a relative margin of `2 ^ (⌊2s/3⌋+1-s)`, i.e. `2 ^ (-s/3)`.
Consequently **no argument can discharge `hhigh` at the first late rank without
already proving `ρ s < 2 ^ (s+1)`**, and `T4`'s conditional bound cannot be made
unconditional along this route.  Combined with `T1`'s interval-ceiling no-go, the
declined step is closed off at the rank layer from both sides: branch-blind
inductions are `Ω(4 ^ s)`, and the branch-aware single-rank hypothesis is the
conclusion itself.

The one thing §3 does buy is the case split: at a **declined** late rank `hhigh`
is free, so the residual hard case is exactly the rows where every late rank is
taken — and those are precisely the rows with no late skipped rank, i.e. the rows
where `LargestSkipLateAt s` fails anyway.

**§6  Certificates.**  Row `13` (the row that refutes the `∀ d` form) is
admissible at its first late rank `9` — `Concrete.admissible_thirteen` — and both
halves of the sandwich fire there (`Concrete.sandwich_thirteen`); in particular
`Concrete.hhigh_thirteen_derived` obtains `hhigh` at `(13,9)` from §5 rather than
by evaluating it.  Row `14` supplies a declined late rank `13`, giving `hhigh` for
free and then `ρ 14 < 2 ^ 15` from `hlow` alone
(`Concrete.seamRemainder_fourteen_lt`).  Row `13` also supplies a non-empty taken
run `9,10,11` for `hhigh_of_taken_run`.  Row `7` shows the hypotheses are not
universal: `hlow` **fails** there at the first late rank
(`Concrete.not_hlow_seven`) while `hhigh` holds (`Concrete.hhigh_seven`), so the
two side conditions are independent and `hhigh_firstLate_sandwich` has a genuinely
non-trivial hypothesis.

## §7  What is measured, not proved

Independent re-implementation of `truncatedMersenneWeight`, `seamSubsetTarget`,
`seamWeights`, `integerGreedyBits`, `weightedBoolSum`, `integerGreedyRemainder`,
`earlyWeights`, `lateEntryRemainder` and `lateCorrection`, in two separate codes —
a direct residual recursion, and a list transcription of `Corr1`'s definitions —
which agree at **every** `(s,d)` with `6 ≤ s ≤ 219`, `2 ≤ d ≤ s`.  Cross-validated
against three values the corpus certifies by `decide +kernel`:
`lateEntryRemainder 20 14 = 67662313` (`BitCorr.Concrete`),
`lateEntryRemainder 14 10 = 392` and `lateEntryRemainder 12 9 = 63264` (`T4`).

Scan of `s ∈ [6, 3000]` (2995 rows), exact failure sets:

* **`hhigh` at the first late rank `d₀`: the failure set is EMPTY.**  Not "small"
  — empty.  The largest observed ratio `lateEntryRemainder s d₀ / 2 ^ (2*s-d₀+1)`
  is `0.9998869` at `(s, d₀) = (1703, 1136)`, so the margin is genuinely thin.
* **`hlow` at `d₀`: failure set `{7}`** — exactly one row, `s = 7`, where
  `lateCorrection 7 5 = 20 > 7 = 263 % 2 ^ 8`.  Proved: `Concrete.not_hlow_seven`.
* `T1`'s `∀ d` form: failure set `{(13,7)}`, reproducing `T1.not_residualInvariant`
  independently.  In `BitCorr` coordinates that is `hhigh` failing at `d = 8`,
  which is below the late zone of row `13`.
* `T1`'s `WeightCeilingAt` (`seamResidualUpto s d < truncatedMersenneWeight s d`):
  failure set EMPTY over the same range, reproducing `T1`'s measurement.
* `ρ s < 2 ^ (s+1)`: failure set EMPTY; the largest observed `ρ s / 2 ^ (s+1)` is
  `0.9999435` at `s = 1135`.
* **The sufficient condition of §5, `ρ s + 2 ^ (⌊2s/3⌋+2) < 2 ^ (s+1)`, holds at
  all 2995 rows.**  So at every row of the range, `hhigh` at `d₀` is *derivable*
  from `ρ s < 2 ^ (s+1)` by `hhigh_firstLate_of_seamRemainder_lt` — which is the
  quantitative form of the circularity, and the reason the failure set above is
  empty.
* Hit density `ρ s ≤ 2 ^ s`: `1495 / 2995 = 0.49917`, flat, matching `RemC6`.
* The largest declined rank is late at all but three rows (`s = 11, 12, 13`, where
  it is `7`), and is `≥ (s+1)/2` at every row of the range.

## What is NOT proved

1. `hhigh` at the first late rank is **not** proved for general `s`.  §5 shows why
   it cannot be, by anything short of the conclusion.
2. `hlow` is false in general: `Decl/D4.not_hlow_seven_five` and
   `Hlow/H1.not_hlow_of_hhigh` prove its failure at `(s,d) = (7,5)`.
   `Hlow/H2` proves that such a failure is a half-point hit certificate.
3. Nothing here bears on the cofinality of `LargestSkipLateAt`, so **Erdős #257's
   `1/2` question is untouched by this file.**  Even a proof of
   `ρ s < 2 ^ (s+1)` would not settle it — `RemC1`'s surplus model satisfies that
   bound and never hits `2 ^ s`.

Checked with `lake env lean ErdosProblems/Decl/D3.lean` (exit `0`, empty output).
No `sorry`, no `axiom`, no `native_decide`; every theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`.
-/

namespace ErdosProblems.DeclD3

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy Erdos249257.BitCorr

/-! ## 1. The first late rank -/

/-- The least rank `d` with `2 * s < 3 * d`: the first rank of the late zone. -/
def firstLate (s : ℕ) : ℕ := 2 * s / 3 + 1

theorem firstLate_late (s : ℕ) : 2 * s < 3 * firstLate s := by
  unfold firstLate; omega

theorem firstLate_least {s d : ℕ} (h : 2 * s < 3 * d) : firstLate s ≤ d := by
  unfold firstLate; omega

theorem two_le_firstLate {s : ℕ} (hs : 3 ≤ s) : 2 ≤ firstLate s := by
  unfold firstLate; omega

theorem firstLate_lt {s : ℕ} (hs : 4 ≤ s) : firstLate s < s := by
  unfold firstLate; omega

theorem firstLate_thirteen : firstLate 13 = 9 := by unfold firstLate; norm_num

theorem firstLate_twelve : firstLate 12 = 9 := by unfold firstLate; norm_num

theorem firstLate_fourteen : firstLate 14 = 10 := by unfold firstLate; norm_num

theorem firstLate_twenty : firstLate 20 = 14 := by unfold firstLate; norm_num

/-! ## 2. The entering remainder obeys the rank recursion -/

theorem seamWeightsFrom_take_succ (s : ℕ) :
    ∀ m a : ℕ, a + m < s →
      (seamWeightsFrom s a).take (m + 1)
        = (seamWeightsFrom s a).take m ++ [truncatedMersenneWeight s (a + m)] := by
  intro m
  induction m with
  | zero =>
      intro a ha
      rw [seamWeightsFrom_eq_cons (by omega : a < s)]
      simp
  | succ m ih =>
      intro a ha
      have hIH := ih (a + 1) (by omega)
      rw [show a + 1 + m = a + (m + 1) by omega] at hIH
      rw [seamWeightsFrom_eq_cons (by omega : a < s), List.take_succ_cons,
        List.take_succ_cons, hIH, List.cons_append]

theorem earlyWeights_succ {s d : ℕ} (h2 : 2 ≤ d) (hds : d < s) :
    earlyWeights s (d + 1) = earlyWeights s d ++ [truncatedMersenneWeight s d] := by
  have h := seamWeightsFrom_take_succ s (d - 2) 2 (by omega)
  rw [show 2 + (d - 2) = d by omega] at h
  show (seamWeights s).take (d + 1 - 2) = (seamWeights s).take (d - 2) ++ _
  rw [show d + 1 - 2 = (d - 2) + 1 by omega]
  exact h

theorem lateEntryRemainder_eq_greedy (s d : ℕ) :
    lateEntryRemainder s d = integerGreedyRemainder (earlyWeights s d) (seamSubsetTarget s) :=
  rfl

/-- The entering remainder satisfies the rank-by-rank greedy recursion. -/
theorem lateEntryRemainder_succ {s d : ℕ} (h2 : 2 ≤ d) (hds : d < s) :
    lateEntryRemainder s (d + 1)
      = if truncatedMersenneWeight s d ≤ lateEntryRemainder s d then
          lateEntryRemainder s d - truncatedMersenneWeight s d
        else lateEntryRemainder s d := by
  rw [lateEntryRemainder_eq_greedy, earlyWeights_succ h2 hds,
    RemC6.integerGreedyRemainder_append, RemC6.integerGreedyRemainder_cons,
    RemC6.integerGreedyRemainder_nil, ← lateEntryRemainder_eq_greedy]

theorem lateEntryRemainder_two (s : ℕ) : lateEntryRemainder s 2 = seamSubsetTarget s := by
  show integerGreedyRemainder ((seamWeights s).take (2 - 2)) (seamSubsetTarget s) = _
  norm_num [RemC6.integerGreedyRemainder_nil]

/-- **The glue.**  `BitCorr`'s entering remainder at rank `d` is exactly `T1`'s
rank residual after the ranks `2, …, d-1` have been offered. -/
theorem lateEntryRemainder_eq_seamResidualUpto {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s) :
    lateEntryRemainder s d = Three.T1.seamResidualUpto s (d - 1) := by
  induction d, h2 using Nat.le_induction with
  | base => rw [lateEntryRemainder_two, Three.T1.seamResidualUpto_one]
  | succ d h2 ih =>
      have hds' : d < s := by omega
      have hIH := ih (by omega)
      rw [lateEntryRemainder_succ h2 hds', hIH,
        show d + 1 - 1 = (d - 1) + 1 by omega,
        Three.T1.seamResidualUpto_succ (by omega : 1 ≤ d - 1),
        show d - 1 + 1 = d by omega]

/-- `hhigh` at rank `d` is literally `T1`'s residual invariant at the single
rank `d - 1`. -/
theorem hhigh_iff_residualInvariant {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s) :
    lateEntryRemainder s d < 2 ^ (2 * s - d + 1) ↔
      Three.T1.seamResidualUpto s (d - 1) < 2 ^ (2 * s - (d - 1)) := by
  rw [lateEntryRemainder_eq_seamResidualUpto h2 hds, show 2 * s - d + 1 = 2 * s - (d - 1) by omega]

/-! ## 3. Two unconditional closures of `hhigh` -/

/-- **`hhigh` is free at every declined rank.**  If the greedy refuses rank `d`
then the capacity entering rank `d` is below the whole rank-`d` weight, and the
weight itself is below `2 ^ (2 * s - d + 1)`.  No induction, no measurement. -/
theorem hhigh_of_declined {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ s)
    (hdecl : lateEntryRemainder s d < truncatedMersenneWeight s d) :
    lateEntryRemainder s d < 2 ^ (2 * s - d + 1) := by
  have hup := RemC6.truncatedMersenneWeight_le hd hds
  have h1 : (2 : ℕ) ^ (2 * s - 2 * d + 1) ≤ 2 ^ (2 * s - d) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℕ) ^ (2 * s - d + 1) = 2 ^ (2 * s - d) + 2 ^ (2 * s - d) := by
    rw [pow_succ]; ring
  omega

/-- **`hhigh` propagates across a taken rank.**  This is `T1.residual_lt_of_taken`
in the `BitCorr` coordinates: the halving of the ceiling is exactly paid for by
the top bit of the accepted weight. -/
theorem hhigh_succ_of_taken {s d : ℕ} (h2 : 2 ≤ d) (hds : d < s)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1))
    (htaken : truncatedMersenneWeight s d ≤ lateEntryRemainder s d) :
    lateEntryRemainder s (d + 1) < 2 ^ (2 * s - (d + 1) + 1) := by
  have hlow := RemC6.two_pow_le_truncatedMersenneWeight (s := s) (d := d) (by omega) (by omega)
  have hdbl : (2 : ℕ) ^ (2 * s - d + 1) = 2 ^ (2 * s - d) + 2 ^ (2 * s - d) := by
    rw [pow_succ]; ring
  have hexp : 2 * s - (d + 1) + 1 = 2 * s - d := by omega
  rw [lateEntryRemainder_succ h2 hds, if_pos htaken, hexp]
  omega

/-- **`hhigh` propagates across a whole run of taken ranks.**  Together with
`hhigh_of_declined` these are the only two closures the greedy step law offers,
and the one step they cannot cross is *decline, then move on*: after a decline at
rank `e` one knows only `lateEntryRemainder s (e+1) < truncatedMersenneWeight s e`,
which exceeds `2 ^ (2*s-e)` by the lower binary terms of the weight
(`T1.residual_lt_of_declined`).  That is the located gap, in these coordinates. -/
theorem hhigh_of_taken_run {s a : ℕ} (h2 : 2 ≤ a)
    (hhigh : lateEntryRemainder s a < 2 ^ (2 * s - a + 1)) :
    ∀ d : ℕ, a ≤ d → d ≤ s →
      (∀ e : ℕ, a ≤ e → e < d → truncatedMersenneWeight s e ≤ lateEntryRemainder s e) →
      lateEntryRemainder s d < 2 ^ (2 * s - d + 1) := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => intro _ _; exact hhigh
  | succ d hd ih =>
      intro hds htaken
      have hIH := ih (by omega) (fun e he hed => htaken e he (by omega))
      exact hhigh_succ_of_taken (by omega) (by omega) hIH (htaken d hd (by omega))

/-! ## 4. The master inequality: `hhigh` is the conclusion in disguise -/

/-- The greedy cannot consume more than the total of the weights it is offered. -/
theorem integerGreedyRemainder_ge (ws : List ℕ) (C : ℕ) :
    C ≤ integerGreedyRemainder ws C + ws.sum := by
  have h1 := weightedBoolSum_le_sum ws (integerGreedyBits ws C)
  have h2 := integerGreedyBits_admissible ws C
  show C ≤ C - weightedBoolSum ws (integerGreedyBits ws C) + ws.sum
  omega

private theorem seamWeightsFrom_sum_upper_aux (s : ℕ) :
    ∀ n d : ℕ, 1 ≤ d → d ≤ s → s - d ≤ n →
      (seamWeightsFrom s d).sum + 2 ^ (s + 1)
        ≤ 2 ^ (2 * s - d + 1) + 2 ^ (2 * s - 2 * d + 2) := by
  intro n
  induction n with
  | zero =>
      intro d hd hds hn
      have hde : d = s := by omega
      subst hde
      rw [seamWeightsFrom_eq_nil (le_refl _), show 2 * d - d + 1 = d + 1 by omega,
        show 2 * d - 2 * d + 2 = 2 by omega]
      norm_num
  | succ n ih =>
      intro d hd hds hn
      rcases Nat.lt_or_ge d s with hlt | hge
      · have hIH := ih (d + 1) (by omega) (by omega) (by omega)
        rw [show 2 * s - (d + 1) + 1 = 2 * s - d by omega,
          show 2 * s - 2 * (d + 1) + 2 = 2 * s - 2 * d by omega] at hIH
        have hw := RemC6.truncatedMersenneWeight_le hd hds
        have p1 : 0 < (2 : ℕ) ^ (2 * s - d) := Nat.two_pow_pos _
        have p2 : 0 < (2 : ℕ) ^ (2 * s - 2 * d) := Nat.two_pow_pos _
        have e3 : (2 : ℕ) ^ (2 * s - d + 1) = 2 ^ (2 * s - d) + 2 ^ (2 * s - d) := by
          rw [pow_succ]; ring
        have e4 : (2 : ℕ) ^ (2 * s - 2 * d + 2)
            = 2 ^ (2 * s - 2 * d) + 2 ^ (2 * s - 2 * d)
              + (2 ^ (2 * s - 2 * d) + 2 ^ (2 * s - 2 * d)) := by
          rw [pow_add]; ring
        have e5 : (2 : ℕ) ^ (2 * s - 2 * d + 1) = 2 ^ (2 * s - 2 * d) + 2 ^ (2 * s - 2 * d) := by
          rw [pow_succ]; ring
        rw [seamWeightsFrom_eq_cons hlt, List.sum_cons]
        omega
      · have hde : d = s := by omega
        subst hde
        rw [seamWeightsFrom_eq_nil (le_refl _), show 2 * d - d + 1 = d + 1 by omega,
          show 2 * d - 2 * d + 2 = 2 by omega]
        norm_num

/-- The seam weights from rank `d` upwards sum to at most
`2 ^ (2*s-d+1) - 2 ^ (s+1) + 2 ^ (2*s-2*d+2)`.  Companion to
`RemC6.seamWeightsFrom_sum_lower`. -/
theorem seamWeightsFrom_sum_upper {s d : ℕ} (hd : 1 ≤ d) (hds : d ≤ s) :
    (seamWeightsFrom s d).sum + 2 ^ (s + 1)
      ≤ 2 ^ (2 * s - d + 1) + 2 ^ (2 * s - 2 * d + 2) :=
  seamWeightsFrom_sum_upper_aux s (s - d) d hd hds (le_refl _)

/-- **The master inequality.**  The capacity entering the late rank `d` exceeds
the final remainder `ρ s` by at most the total of the weights still to come, and
that total is `2 ^ (2*s-d+1) - 2 ^ (s+1)` up to the second-order term
`2 ^ (2*s-2*d+2)`. -/
theorem lateEntryRemainder_add_two_pow_le {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s) :
    lateEntryRemainder s d + 2 ^ (s + 1)
      ≤ seamIntegerGreedyRemainder s + 2 ^ (2 * s - d + 1) + 2 ^ (2 * s - 2 * d + 2) := by
  have hbridge := ThreeT4.seamIntegerGreedyRemainder_eq_lateGreedy (s := s) (d := d) h2
  have hge := integerGreedyRemainder_ge (seamWeightsFrom s d) (lateEntryRemainder s d)
  rw [← hbridge] at hge
  have hsum := seamWeightsFrom_sum_upper (s := s) (d := d) (by omega) hds
  omega

/-- **`hhigh` follows from the conclusion.**  If `ρ s` is below `2 ^ (s+1)` by
more than the second-order term, the side condition `hhigh` holds at rank `d`. -/
theorem hhigh_of_seamRemainder_lt {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s)
    (h : seamIntegerGreedyRemainder s + 2 ^ (2 * s - 2 * d + 2) < 2 ^ (s + 1)) :
    lateEntryRemainder s d < 2 ^ (2 * s - d + 1) := by
  have := lateEntryRemainder_add_two_pow_le h2 hds
  omega

/-- The contrapositive: a failure of `hhigh` at rank `d` pins `ρ s` to within
`2 ^ (2*s-2*d+2)` of `2 ^ (s+1)`. -/
theorem two_pow_le_seamRemainder_of_not_hhigh {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s)
    (hbad : ¬ lateEntryRemainder s d < 2 ^ (2 * s - d + 1)) :
    2 ^ (s + 1) ≤ seamIntegerGreedyRemainder s + 2 ^ (2 * s - 2 * d + 2) := by
  by_contra hc
  exact hbad (hhigh_of_seamRemainder_lt h2 hds (by omega))

/-! ## 5. At the first late rank -/

theorem firstLate_le {s : ℕ} (hs : 3 ≤ s) : firstLate s ≤ s := by
  unfold firstLate; omega

/-- The second-order term at the first late rank is only `2 ^ (⌊2s/3⌋ + 2)`. -/
theorem two_pow_firstLate_error_le (s : ℕ) :
    (2 : ℕ) ^ (2 * s - 2 * firstLate s + 2) ≤ 2 ^ (2 * s / 3 + 2) :=
  Nat.pow_le_pow_right (by norm_num) (by unfold firstLate; omega)

/-- **`hhigh` at the first late rank is implied by the conclusion.**  If `ρ s`
undershoots `2 ^ (s+1)` by more than `2 ^ (⌊2s/3⌋+2)` — an exponentially small
fraction of `2 ^ (s+1)` — then the `BitCorr`/`T4` side condition `hhigh` holds at
the first late rank. -/
theorem hhigh_firstLate_of_seamRemainder_lt {s : ℕ} (hs : 3 ≤ s)
    (h : seamIntegerGreedyRemainder s + 2 ^ (2 * s / 3 + 2) < 2 ^ (s + 1)) :
    lateEntryRemainder s (firstLate s) < 2 ^ (2 * s - firstLate s + 1) := by
  refine hhigh_of_seamRemainder_lt (two_le_firstLate hs) (firstLate_le hs) ?_
  have := two_pow_firstLate_error_le s
  omega

/-- **The contrapositive, and the point of this file.**  A failure of `hhigh` at
the first late rank forces `ρ s` into the top `2 ^ (⌊2s/3⌋+2)` of the interval
`[0, 2 ^ (s+1))` — i.e. within a relative `2 ^ (⌊2s/3⌋+1-s)` of the very bound
that `T4` derives *from* `hhigh`. -/
theorem seamRemainder_ge_of_not_hhigh_firstLate {s : ℕ} (hs : 3 ≤ s)
    (hbad : ¬ lateEntryRemainder s (firstLate s) < 2 ^ (2 * s - firstLate s + 1)) :
    2 ^ (s + 1) ≤ seamIntegerGreedyRemainder s + 2 ^ (2 * s / 3 + 2) := by
  by_contra hc
  exact hbad (hhigh_firstLate_of_seamRemainder_lt hs (by omega))

/-- **The sandwich.**  Under `hlow`, the side condition `hhigh` at the first late
rank and the conclusion `ρ s < 2 ^ (s+1)` imply each other, up to the additive
`2 ^ (⌊2s/3⌋+2)`.  So `hhigh` is not a technical hypothesis weaker than the
conclusion: it *is* the conclusion, to within an exponentially small margin. -/
theorem hhigh_firstLate_sandwich {s : ℕ} (hs : 3 ≤ s)
    (hlow : lateCorrection s (firstLate s)
      ≤ lateEntryRemainder s (firstLate s) % 2 ^ (s + 1)) :
    (seamIntegerGreedyRemainder s + 2 ^ (2 * s / 3 + 2) < 2 ^ (s + 1) →
        lateEntryRemainder s (firstLate s) < 2 ^ (2 * s - firstLate s + 1)) ∧
      (lateEntryRemainder s (firstLate s) < 2 ^ (2 * s - firstLate s + 1) →
        seamIntegerGreedyRemainder s < 2 ^ (s + 1)) := by
  refine ⟨fun h => hhigh_firstLate_of_seamRemainder_lt hs h, fun hhigh => ?_⟩
  exact ThreeT4.seamRemainder_lt_two_pow_succ (two_le_firstLate hs) (firstLate_late s) hhigh hlow

/-- **What `hhigh_of_declined` buys.**  At a *declined* late rank the `T4` bound
`ρ s < 2 ^ (s+1)` needs only the low-block condition `hlow`; `hhigh` is proved,
not assumed.  Compare `RemC6.seamIntegerGreedyRemainder_lt_three_mul_two_pow`,
which gives `3 * 2 ^ s` from a *largest* late declined rank. -/
theorem seamRemainder_lt_two_pow_succ_of_declined {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s)
    (hlate : 2 * s < 3 * d)
    (hdecl : lateEntryRemainder s d < truncatedMersenneWeight s d)
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) :=
  ThreeT4.seamRemainder_lt_two_pow_succ h2 hlate
    (hhigh_of_declined (by omega) hds hdecl) hlow

/-! ## 6. Certificates -/

namespace Concrete

theorem seamWeights_thirteen :
    seamWeights 13 =
      [22369621, 9586980, 4473924, 2164802, 1065220, 528416, 263172, 131328,
        65600, 32784, 16388] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_nil (by norm_num)]
  simp only [truncatedMersenneWeight]
  decide +kernel

/-- The capacity entering the first late rank of row `13`. -/
theorem lateEntryRemainder_thirteen_nine : lateEntryRemainder 13 9 = 261247 := by
  unfold lateEntryRemainder earlyWeights
  rw [seamWeights_thirteen]
  simp only [seamSubsetTarget]
  decide +kernel

/-- The capacity entering rank `8` of row `13` — the rank at which `T1`'s
`∀ d` invariant fails. -/
theorem lateEntryRemainder_thirteen_eight : lateEntryRemainder 13 8 = 524419 := by
  unfold lateEntryRemainder earlyWeights
  rw [seamWeights_thirteen]
  simp only [seamSubsetTarget]
  decide +kernel

/-- **`hhigh` fails at rank `8` of row `13`** — this is `T1.not_residualInvariant`
transported into the `BitCorr` coordinates. -/
theorem not_hhigh_thirteen_eight :
    ¬ lateEntryRemainder 13 8 < 2 ^ (2 * 13 - 8 + 1) := by
  rw [lateEntryRemainder_thirteen_eight]
  norm_num

/-- **…and rank `8` is not in the late zone of row `13`.**  So the sole failure of
`T1`'s `∀ d` invariant over `s ∈ [6,3000]` is not a failure of the single-rank
form at all: it sits strictly below the first late rank `firstLate 13 = 9`. -/
theorem eight_not_late_thirteen : ¬ (2 * 13 < 3 * 8) := by norm_num

theorem eight_lt_firstLate_thirteen : 8 < firstLate 13 := by
  rw [firstLate_thirteen]; norm_num

/-- **`hhigh` holds at the first late rank of row `13`.** -/
theorem hhigh_thirteen :
    lateEntryRemainder 13 (firstLate 13) < 2 ^ (2 * 13 - firstLate 13 + 1) := by
  rw [firstLate_thirteen, lateEntryRemainder_thirteen_nine]
  norm_num

theorem lateCorrection_thirteen_nine : lateCorrection 13 9 = 340 := by
  rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_zero (by norm_num)]
  decide +kernel

theorem hlow_thirteen :
    lateCorrection 13 (firstLate 13)
      ≤ lateEntryRemainder 13 (firstLate 13) % 2 ^ (13 + 1) := by
  rw [firstLate_thirteen, lateEntryRemainder_thirteen_nine, lateCorrection_thirteen_nine]
  decide +kernel

/-- **Anti-vacuity for `hhigh_firstLate_of_seamRemainder_lt`.**  At row `13` the
sufficient condition holds: `ρ 13 = 15147` (from `T1`) and
`15147 + 2 ^ 10 = 16171 < 16384 = 2 ^ 14`.  So `hhigh` at the first late rank of
row `13` is *derived*, not computed — at the very row whose rank `8` refutes the
`∀ d` form. -/
theorem seamRemainder_thirteen_small :
    seamIntegerGreedyRemainder 13 + 2 ^ (2 * 13 / 3 + 2) < 2 ^ (13 + 1) := by
  rw [Three.T1.seamIntegerGreedyRemainder_thirteen]
  norm_num

theorem hhigh_thirteen_derived :
    lateEntryRemainder 13 (firstLate 13) < 2 ^ (2 * 13 - firstLate 13 + 1) :=
  hhigh_firstLate_of_seamRemainder_lt (by norm_num) seamRemainder_thirteen_small

/-- Both halves of the sandwich fire at row `13`. -/
theorem sandwich_thirteen :
    (seamIntegerGreedyRemainder 13 + 2 ^ (2 * 13 / 3 + 2) < 2 ^ (13 + 1) →
        lateEntryRemainder 13 (firstLate 13) < 2 ^ (2 * 13 - firstLate 13 + 1)) ∧
      (lateEntryRemainder 13 (firstLate 13) < 2 ^ (2 * 13 - firstLate 13 + 1) →
        seamIntegerGreedyRemainder 13 < 2 ^ (13 + 1)) :=
  hhigh_firstLate_sandwich (by norm_num) hlow_thirteen

/-- `LateEntryAdmissible 13 9`: the row that refutes the `∀ d` form is admissible
for all of `T4` at its first late rank. -/
theorem admissible_thirteen : ThreeT4.LateEntryAdmissible 13 9 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [lateEntryRemainder_thirteen_nine]; norm_num
  · rw [lateEntryRemainder_thirteen_nine, lateCorrection_thirteen_nine]
    decide +kernel

/-! ### A non-empty taken run: anti-vacuity for `hhigh_of_taken_run` -/

theorem lateEntryRemainder_thirteen_ten : lateEntryRemainder 13 10 = 129919 := by
  unfold lateEntryRemainder earlyWeights
  rw [seamWeights_thirteen]
  simp only [seamSubsetTarget]
  decide +kernel

theorem lateEntryRemainder_thirteen_eleven : lateEntryRemainder 13 11 = 64319 := by
  unfold lateEntryRemainder earlyWeights
  rw [seamWeights_thirteen]
  simp only [seamSubsetTarget]
  decide +kernel

theorem lateEntryRemainder_thirteen_twelve : lateEntryRemainder 13 12 = 31535 := by
  unfold lateEntryRemainder earlyWeights
  rw [seamWeights_thirteen]
  simp only [seamSubsetTarget]
  decide +kernel

/-- Ranks `9, 10, 11` of row `13` are all taken: a genuinely non-empty run. -/
theorem taken_run_thirteen :
    ∀ e : ℕ, 9 ≤ e → e < 12 →
      truncatedMersenneWeight 13 e ≤ lateEntryRemainder 13 e := by
  intro e h1 h2
  interval_cases e
  · rw [lateEntryRemainder_thirteen_nine]
    simp only [truncatedMersenneWeight]
    decide +kernel
  · rw [lateEntryRemainder_thirteen_ten]
    simp only [truncatedMersenneWeight]
    decide +kernel
  · rw [lateEntryRemainder_thirteen_eleven]
    simp only [truncatedMersenneWeight]
    decide +kernel

/-- **Anti-vacuity for `hhigh_of_taken_run`.**  `hhigh` at the first late rank `9`
of row `13` is carried across the run `9, 10, 11` to rank `12`. -/
theorem hhigh_thirteen_twelve :
    lateEntryRemainder 13 12 < 2 ^ (2 * 13 - 12 + 1) :=
  hhigh_of_taken_run (a := 9) (by norm_num)
    (by rw [lateEntryRemainder_thirteen_nine]; norm_num) 12 (by norm_num) (by norm_num)
    taken_run_thirteen

/-! ### A declined late rank: `hhigh` for free -/

theorem lateEntryRemainder_fourteen_thirteen : lateEntryRemainder 14 13 = 392 := by
  unfold lateEntryRemainder earlyWeights
  rw [ThreeT4.Concrete.seamWeights_fourteen]
  simp only [seamSubsetTarget]
  decide +kernel

theorem truncatedMersenneWeight_fourteen_thirteen :
    truncatedMersenneWeight 14 13 = 32772 := by
  simp only [truncatedMersenneWeight]
  decide +kernel

/-- Rank `13` of row `14` is declined, and it is late. -/
theorem declined_fourteen_thirteen :
    lateEntryRemainder 14 13 < truncatedMersenneWeight 14 13 := by
  rw [lateEntryRemainder_fourteen_thirteen, truncatedMersenneWeight_fourteen_thirteen]
  norm_num

theorem lateCorrection_fourteen_thirteen : lateCorrection 14 13 = 4 := by
  rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_zero (by norm_num)]
  decide +kernel

/-- **`hhigh` derived from the decline alone**, with no measurement and no
induction. -/
theorem hhigh_fourteen_thirteen :
    lateEntryRemainder 14 13 < 2 ^ (2 * 14 - 13 + 1) :=
  hhigh_of_declined (by norm_num) (by norm_num) declined_fourteen_thirteen

/-- The full `T4` bound at row `14` from the decline plus `hlow` only. -/
theorem seamRemainder_fourteen_lt :
    seamIntegerGreedyRemainder 14 < 2 ^ (14 + 1) := by
  refine seamRemainder_lt_two_pow_succ_of_declined (d := 13) (by norm_num) (by norm_num)
    (by norm_num) declined_fourteen_thirteen ?_
  rw [lateEntryRemainder_fourteen_thirteen, lateCorrection_fourteen_thirteen]
  decide +kernel

/-! ### Row `7`: `hlow` is not universal

Row `7` is the sole row of `[6,3000]` at which the *other* side condition fails
at the first late rank.  So `hhigh_firstLate_sandwich` has a genuinely
non-trivial hypothesis, and the file does not pretend otherwise. -/

theorem seamWeights_seven : seamWeights 7 = [5461, 2340, 1092, 528, 260] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_nil (by norm_num)]
  simp only [truncatedMersenneWeight]
  decide +kernel

theorem firstLate_seven : firstLate 7 = 5 := by unfold firstLate; norm_num

theorem lateEntryRemainder_seven_five : lateEntryRemainder 7 5 = 263 := by
  unfold lateEntryRemainder earlyWeights
  rw [seamWeights_seven]
  simp only [seamSubsetTarget]
  decide +kernel

theorem lateCorrection_seven_five : lateCorrection 7 5 = 20 := by
  rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_zero (by norm_num)]
  decide +kernel

/-- **`hlow` fails at the first late rank of row `7`.** -/
theorem not_hlow_seven :
    ¬ lateCorrection 7 (firstLate 7)
        ≤ lateEntryRemainder 7 (firstLate 7) % 2 ^ (7 + 1) := by
  rw [firstLate_seven, lateEntryRemainder_seven_five, lateCorrection_seven_five]
  decide +kernel

/-- …while `hhigh` still holds there.  The two side conditions are independent. -/
theorem hhigh_seven :
    lateEntryRemainder 7 (firstLate 7) < 2 ^ (2 * 7 - firstLate 7 + 1) := by
  rw [firstLate_seven, lateEntryRemainder_seven_five]
  norm_num

end Concrete

end ErdosProblems.DeclD3
