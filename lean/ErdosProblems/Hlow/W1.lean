/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.HalfCylinderIntegerGreedy

/-!
# W1 — the one place arithmetic enters the row recursion: the pulse is a divisor count

Scratch support for the W1 analysis.  Two things are proved.

## 1. `wordPulse s b ≤ divisorPulseBudget s`

`HalfCylinderIntegerGreedy.wordPulse_le` bounds the row's pulse by `2 * (s - 2)`,
i.e. by `2` per rank.  But `rowPulse s d = [d ∣ 2*s+2] + 2 * [d ∣ 2*s+1]` is zero
at every rank that divides neither `2*s+1` nor `2*s+2`, so the proved budget is a
**divisor count of the two integers `2*s+1` and `2*s+2`**, not a linear function
of `s`.  `divisorPulseBudget_le_card_divisors` puts it under
`τ(2*s+2) + 2*τ(2*s+1)`.  The familiar subpolynomial growth description for the
divisor function is background number theory, not a theorem proved in this
file.

This term is indexed by the arithmetic of `s`, not only by the recursion step,
so it is data not represented in the rank/row no-gos
(`Three.T1.IntervalCeiling.four_pow_le`, `RemC1.le_of_descent_of_quadrupling`)
do not cover.

Size of the gain, MEASURED by an independent replication of `seamWeights`,
`seamSubsetTarget` and `integerGreedyBits` (agreeing with the corpus's certified
`ρ 7 = 3`, `ρ 13 = 15147`, `ρ 14 = 392`, `ρ 20 = 549353`):

* the **selected** pulse `wordPulse s (seamGreedyWord s)` over `s ∈ [5, 1600]`
  has min `1`, max `28`, mean `6.2`;
* `divisorPulseBudget s` over `s ∈ [5, 40000]` has max `121`, mean `12.9`;
* the corpus bound `2 * (s - 2)` is `1196` at `s = 600` and `79996` at
  `s = 40000`.

`budget_thirty` is a kernel-checked example: at `s = 30` the
corpus allows `56` and the truth is `1`.

## 2. `surplus_lt_two_of_window`

The abstract engine of the route.  A run of right branches obeys
`σ (t+1) + 4 + p t = 4 * σ t` in the surplus coordinate `σ s = ρ s - 2 ^ s`
(`BitR2.surplus_step`), and `BitR4.remainder_ge_of_half_not_mem` says the
negative branch of `#257` forces `2 ≤ σ s` from some row on.  `surplus_pinned`
solves the run exactly over a window of `K` rows,

    `4 ^ K * σ s = σ (s + K) + ∑_{k < K} 4 ^ (K-1-k) * (p (s+k) + 4)`,

so `σ s` is pinned by the next `K` pulses and one ceiling — no forward
propagation, no induction on a bound.  Contrapositive
(`surplus_lt_two_of_window`): a window whose weighted pulse sum plus the ceiling
stays under `2 * 4 ^ K` forces `σ s < 2`, i.e. `ρ s ≤ 2 ^ s + 1`, which is the
hypothesis of `BitR4.half_mem_of_remainder_dips_strong`.

`persistent_surplus_is_exactly_tight` records that `RemC1.surplusModel 2` — the
model that defeats every row-level argument — realises the window sum as
*exactly* `2 * 4 ^ K`.  The criterion is therefore sharp against the known
obstruction, and firing it needs strictly better pulse information than
`divisorPulseBudget` alone gives.

## Anti-vacuity, and one honest failure of it

* `wordPulse_le_divisorPulseBudget` is exhibited on the genuine object at
  `s = 30`, `s = 12` and `s = 5`, and `budget_lt_corpus_bound_thirty` shows the
  gain is real there.
* `surplus_pinned`'s hypothesis is exhibited by `surplusModel`-style data in
  `persistent_surplus_is_exactly_tight` (`σ ≡ 2`, `p ≡ 2`, every `K`).
* `surplus_lt_two_of_window`'s hypotheses are exhibited **only on a finite
  window** (`window_witness`), and this is not a defect of the witness: a
  sequence obeying the step law at every `t ≥ S` in `ℕ` automatically satisfies
  `2 ≤ σ t` (`two_le_of_stepLaw`), so no globally consistent instance can fire
  the criterion.  That is the content of the criterion, not a gap in it — the
  same situation `BitR2` records for `badRun_pins_remainder`.

## What this file does NOT do

It does not close `#257`.  For the following finite computation, write
`B(s) = divisorPulseBudget s` and `W(s) = ∑_{k ≥ 0} (B(s+k) + 4) / 4 ^ (k+1)`,
the infinite-window comparison would require `W(s) < 2`.  An independently
truncated computation over `s ∈ [5, 40000]` found that `W` never drops below
`2`; its minimum is `2.0233` (at
`s = 6`), it is under `2.5` at nine rows, under `3` at seventy-two, and its mean
is `8.77`.  With the *selected* pulses in place of the budget the same quantity
does drop below `2`, at `20` rows of `[5, 1578]`
(`5, 6, 9, 12, 15, 18, 21, 33, 36, 42, 54, 57, 60, 102, 123, 165, 315, 546, 630,
1113`).  That finite list does not imply a cofinal supply.  The missing input is
a proved lower bound on
the number of *declined* divisor ranks; measured, about half of the divisor
ranks are declined (`mean 6.2` selected against `mean 12.9` available).

## MEASURED, not proved: what the hit event actually is

Independently re-run (exact rationals, no floating point).  Let `A` be the
support of the *real* greedy of `1/2` in the Mersenne system —
`Erdos249257.greedyMersenneSupport (1/2)`, driven by
`greedyMersenneRemainder (1/2)` against `mersenneWeight` — and let
`hit s` mean `seamIntegerGreedyRemainder s ≤ 2 ^ s`, the hypothesis of
`BitR2.half_mem_of_remainderReachesHalfPointCofinally`.  Then over the whole of
`s ∈ [5, 900]`:

    hit s  ⟺  s ∈ A          (0 mismatches out of 896)

and on every hit row the seam greedy's support is *exactly* `A ∩ [2, s)`, while
on every non-hit row it is not.  On the hit rows the scaled comparison margin of
the real greedy reproduces the integer remainder to a bounded additive error:

    ρ s = 4 ^ s * (greedyMersenneRemainder (1/2) (s-1) - mersenneWeight s) + c s,
    c s ∈ (1, 3)   for every hit row of [5, 200].

On the tested hit rows this identifies `ρ s` with a scaled real-greedy state up
to the displayed bounded correction.  It is a measurement, not a proved global
identity.  The observed hit density is `0.481` on `[5,900]`; no limiting density
or probability law is proved.  The correspondence cannot persist after a fatal
rank, because `greedyMersenneFatalAt_add` forces every later rank to be taken
while no later row is a hit.  This file does not formalize an equivalence
between extending the measured correspondence and resolving `#257`.

Checked with `lake env lean ErdosProblems/Hlow/W1.lean` (exit `0`, empty
output).  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace ErdosProblems.HlowW1

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## 1. The pulse budget is a divisor count -/

/-- The total pulse the row can possibly emit, over *all* ranks. -/
def divisorPulseBudget (s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (s - 2), rowPulse s (i + 2)

/-- **The sharpened pulse bound.**  Every Boolean row word emits at most the
row's divisor budget.  Compare `wordPulse_le : wordPulse s b ≤ 2 * (s - 2)`. -/
theorem wordPulse_le_divisorPulseBudget (s : ℕ) (b : ℕ → Bool) :
    wordPulse s b ≤ divisorPulseBudget s := by
  unfold wordPulse divisorPulseBudget
  refine Finset.sum_le_sum ?_
  intro i _
  by_cases hb : b (i + 2) = true
  · simp [hb]
  · simp [hb]

/-- The budget in divisor-count form: the ranks below `s` dividing `2*s+2`,
counted once, plus those dividing `2*s+1`, counted twice. -/
theorem divisorPulseBudget_eq_card (s : ℕ) :
    divisorPulseBudget s =
      ((Finset.Ico 2 s).filter (fun d => d ∣ 2 * s + 2)).card +
        2 * ((Finset.Ico 2 s).filter (fun d => d ∣ 2 * s + 1)).card := by
  have hre :
      divisorPulseBudget s = ∑ d ∈ Finset.Ico 2 s, rowPulse s d := by
    unfold divisorPulseBudget
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])
  rw [hre]
  simp only [rowPulse]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  · rw [Finset.card_filter]
  · congr 1
    rw [Finset.card_filter]

/-- Hence the budget is under a plain divisor count of the two integers
`2*s+2` and `2*s+1`.  This Lean statement does not prove an asymptotic estimate
for the divisor function. -/
theorem divisorPulseBudget_le_card_divisors (s : ℕ) :
    divisorPulseBudget s ≤
      (2 * s + 2).divisors.card + 2 * (2 * s + 1).divisors.card := by
  rw [divisorPulseBudget_eq_card s]
  have h1 : ((Finset.Ico 2 s).filter (fun d => d ∣ 2 * s + 2)).card ≤
      (2 * s + 2).divisors.card := by
    refine Finset.card_le_card ?_
    intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.mem_divisors.mpr ⟨hd.2, by omega⟩
  have h2 : ((Finset.Ico 2 s).filter (fun d => d ∣ 2 * s + 1)).card ≤
      (2 * s + 1).divisors.card := by
    refine Finset.card_le_card ?_
    intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.mem_divisors.mpr ⟨hd.2, by omega⟩
  omega

/-! ### Anti-vacuity for §1: the budget on the genuine object -/

section Witness

set_option maxRecDepth 4000

/-- At `s = 30` the whole row can emit **one** unit of pulse: `2*30+1 = 61` is
prime and `2*30+2 = 62 = 2 * 31` has only the rank `2` below `30`. -/
theorem budget_thirty : divisorPulseBudget 30 = 1 := by
  decide +kernel

/-- The corpus bound at the same row is `56`. -/
theorem budget_lt_corpus_bound_thirty :
    divisorPulseBudget 30 < 2 * (30 - 2) := by
  rw [budget_thirty]
  norm_num

/-- Consequently *every* row-`30` word — in particular the seam greedy's own —
has pulse at most `1`, where `wordPulse_le` allows `56`. -/
theorem wordPulse_thirty_le_one (b : ℕ → Bool) : wordPulse 30 b ≤ 1 := by
  have h := wordPulse_le_divisorPulseBudget 30 b
  rw [budget_thirty] at h
  exact h

/-- A row where the budget is not degenerate, so the bound is not always `1`:
`2*12+2 = 26` contributes ranks `2, 13`-but-`13 > 12`, and `2*12+1 = 25`
contributes rank `5` twice. -/
theorem budget_twelve : divisorPulseBudget 12 = 3 := by
  decide +kernel

/-- And a small row, to show the two counted channels really do both fire:
`2*5+2 = 12` has ranks `2, 3, 4` below `5`. -/
theorem budget_five : divisorPulseBudget 5 = 3 := by
  decide +kernel

end Witness

/-! ## 2. A right-branch run is solved, not propagated -/

/-- **The window identity.**  Over any window on which the surplus obeys the
right-branch law, `σ s` is determined by the window's pulses and the surplus at
the far end.  There is no forward propagation of a bound here, and hence nothing
for `RemC1.le_of_descent_of_quadrupling` to neutralise. -/
theorem surplus_pinned {σ p : ℕ → ℕ} {s : ℕ} :
    ∀ K : ℕ, (∀ t, s ≤ t → t < s + K → σ (t + 1) + 4 + p t = 4 * σ t) →
      4 ^ K * σ s =
        σ (s + K) + ∑ k ∈ Finset.range K, 4 ^ (K - 1 - k) * (p (s + k) + 4) := by
  intro K
  induction K with
  | zero => intro _; simp
  | succ K ih =>
      intro hstep
      have ihK : 4 ^ K * σ s =
          σ (s + K) + ∑ k ∈ Finset.range K, 4 ^ (K - 1 - k) * (p (s + k) + 4) :=
        ih (fun t ht ht' => hstep t ht (by omega))
      have hlast : σ (s + K + 1) + 4 + p (s + K) = 4 * σ (s + K) :=
        hstep (s + K) (by omega) (by omega)
      have hshift :
          (∑ k ∈ Finset.range K, 4 ^ (K + 1 - 1 - k) * (p (s + k) + 4)) =
            4 * ∑ k ∈ Finset.range K, 4 ^ (K - 1 - k) * (p (s + k) + 4) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hkK : k < K := Finset.mem_range.mp hk
        have : K + 1 - 1 - k = (K - 1 - k) + 1 := by omega
        rw [this, pow_succ]
        ring
      have hpow : (4 : ℕ) ^ (K + 1) * σ s = 4 * (4 ^ K * σ s) := by
        rw [pow_succ]; ring
      rw [hpow, ihK, Finset.sum_range_succ, hshift,
        show K + 1 - 1 - K = 0 by omega, pow_zero, one_mul,
        show s + (K + 1) = s + K + 1 by omega]
      omega

/-- **The criterion.**  If the window's weighted pulse sum, plus any ceiling on
the surplus at the far end, stays below `2 * 4 ^ K`, then `σ s < 2`.  Under
`BitR4.remainder_ge_of_half_not_mem` that contradicts the negative branch, so a
single such window at cofinally many rows answers `#257`'s `1/2` question. -/
theorem surplus_lt_two_of_window {σ p : ℕ → ℕ} {s K B : ℕ}
    (hstep : ∀ t, s ≤ t → t < s + K → σ (t + 1) + 4 + p t = 4 * σ t)
    (hB : σ (s + K) ≤ B)
    (hwin : B + ∑ k ∈ Finset.range K, 4 ^ (K - 1 - k) * (p (s + k) + 4)
      < 2 * 4 ^ K) :
    σ s < 2 := by
  have hid := surplus_pinned K hstep
  have hpos : 0 < (4 : ℕ) ^ K := pow_pos (by norm_num) K
  have hlt : 4 ^ K * σ s < 4 ^ K * 2 := by omega
  exact Nat.lt_of_mul_lt_mul_left hlt

/-! ### Anti-vacuity for §2 -/

/-- The step law over `ℕ`, held at every later row, already forces `2 ≤ σ`.
So the criterion above can only ever fire on a *finite* window; there is no
globally consistent instance, and that is exactly its content. -/
theorem two_le_of_stepLaw {σ p : ℕ → ℕ} {S : ℕ}
    (hstep : ∀ t, S ≤ t → σ (t + 1) + 4 + p t = 4 * σ t) (s : ℕ) (hs : S ≤ s) :
    2 ≤ σ s := by
  by_contra hlt
  have h0 := hstep s hs
  have h1 := hstep (s + 1) (by omega)
  omega

/-- A one-row window: surplus `1` at the base, `0` one row later, no pulse. -/
def witnessSurplus : ℕ → ℕ := fun t => if t = 0 then 1 else 0

/-- `surplus_lt_two_of_window` fires on it, pinning `witnessSurplus 0 = 1 < 2`. -/
theorem window_witness : witnessSurplus 0 < 2 := by
  refine surplus_lt_two_of_window (σ := witnessSurplus) (p := fun _ => 0)
    (s := 0) (K := 1) (B := 0) ?_ ?_ ?_
  · intro t _ ht'
    have htz : t = 0 := by omega
    subst htz
    norm_num [witnessSurplus]
  · norm_num [witnessSurplus]
  · norm_num

/-- **The criterion is exactly sharp against the known obstruction.**  For
`RemC1.surplusModel 2` — surplus `2` at every row, pulse `2` at every row, which
satisfies every row-level constraint the corpus proves — the window sum is
*exactly* `2 * 4 ^ K` at every horizon `K`.  So `surplus_lt_two_of_window`
misses by nothing, and firing it needs strictly sharper pulse data than any
uniform bound supplies. -/
theorem persistent_surplus_is_exactly_tight (K : ℕ) :
    2 + ∑ k ∈ Finset.range K, 4 ^ (K - 1 - k) * ((2 : ℕ) + 4) = 2 * 4 ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hshift :
          (∑ k ∈ Finset.range K, 4 ^ (K + 1 - 1 - k) * ((2 : ℕ) + 4)) =
            4 * ∑ k ∈ Finset.range K, 4 ^ (K - 1 - k) * ((2 : ℕ) + 4) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hkK : k < K := Finset.mem_range.mp hk
        have he : K + 1 - 1 - k = (K - 1 - k) + 1 := by omega
        rw [he, pow_succ]
        ring
      rw [Finset.sum_range_succ, hshift, show K + 1 - 1 - K = 0 by omega,
        pow_zero, one_mul,
        show (2 : ℕ) * 4 ^ (K + 1) = 4 * (2 * 4 ^ K) by rw [pow_succ]; ring]
      omega

end ErdosProblems.HlowW1
