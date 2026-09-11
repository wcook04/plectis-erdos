/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.Corr1
import ErdosProblems.Bit.R2
import ErdosProblems.Rem.C6

/-!
# T4 — beneath the row layer: one bit of one integer decides the row

`RemC1.rowLaw_blind_at_16` is the reason the row recurrence cannot settle Erdős
`#257`'s `1/2` question: the recurrence tracks only the *top* rank, so it is
strictly weaker than `LargestSkipLateAt`, and at `s = 16` every row-level
criterion in the corpus is silent while row `17` is nonetheless good via its
skipped rank `14`.  This file therefore works one level down, at the **rank
layer**, using `BitCorr.mem_seamGreedySupport_iff_testBit`: a late rank `e` of
row `s` is skipped exactly when bit `2 * s - e` of the entering remainder
`lateEntryRemainder s d` is clear.

Everything below is stated relative to the two side conditions `BitCorr` already
isolates at a late rank `d` of row `s` — packaged here as
`LateEntryAdmissible s d`:

* `hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1)`
* `hlow  : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)`.

Neither is discharged in this file.  Later files settle their status
differently: `Decl/D1` proves `hhigh` at every declined rank, whereas
`Decl/D4` and `Hlow/H1` refute `hlow` at `(s,d) = (7,5)` while `hhigh` holds.
`Hlow/H2` proves that an `hlow` failure is itself a half-point hit certificate.
Thus `hlow` is false as a universal side condition; it is not an open lemma
whose proof would complete this route.

## What is proved

**§2, the trapping lemma (`lateGreedy_trapped`).**  Run the descending integer
greedy over the late seam weights from an admissible capacity `C`.  Then

    C % 2 ^ (s+1) - lateCorrection s d
        ≤ integerGreedyRemainder (seamWeightsFrom s d) C
        ≤ C % 2 ^ (s+1).

The late greedy consumes the *entire* high part of the capacity exactly, whether
or not any late rank is skipped, and what survives is the low `s + 1` bits minus
the `4 ^ k` budget of the ranks that were taken.  This is proved, not assumed:
the induction closes because `BitCorr.mod_sub_of_le_mod` forbids a borrow out of
the low block.

**§4, the consequence for `ρ s := seamIntegerGreedyRemainder s`.**
`seamRemainder_bounds` transports the trapping lemma along
`seamIntegerGreedyRemainder_eq_lateGreedy`, giving the two-sided

    R % 2 ^ (s+1) - lateCorrection s d ≤ ρ s ≤ R % 2 ^ (s+1),
        R := lateEntryRemainder s d,

and hence `seamRemainder_lt_two_pow_succ : ρ s < 2 ^ (s+1)` at *every* admissible
row.  This is the conditional bound suggested by the invariant that `RemC6`
reported as measured.  `Three/T1.not_residualInvariant` later refutes that
universal measured invariant at `(s,d) = (13,7)`.  The induction closes here because
it is run inside the late zone only, where the weights are two-bit, instead of
from rank `2`.  Against `RemC6.seamIntegerGreedyRemainder_lt_three_mul_two_pow`
(`ρ s < 3 * 2 ^ s`) it is sharper by a factor `3/2`, but the real difference is
the hypothesis: `RemC6` needs a *late largest declined rank*, which is precisely
`LargestSkipLateAt s` — the thing one is trying to produce — whereas §4 needs no
declined rank at all and therefore also covers the bad rows, where every late
rank is taken.

**§6, the rank-layer criterion.**  Read the bits of `R` in the closed window
`[s, 2*s-d]`.

* `largestSkipLateAt_of_zeroBit` — a clear bit at `j ∈ (s, 2*s-d]` *is* a skipped
  late rank `e = 2*s-j`, hence `LargestSkipLateAt s`.  The top rank `s-1` is
  never mentioned; neither is the row recurrence.
* `seamRemainder_lt_two_pow_of_testBit_false` — a clear bit at `j = s` gives
  `ρ s < 2 ^ s`.  Bit `s` is the one position no rank tests (the rank with
  `2*s-e = s` would be `e = s`, outside the word), and it is decisive precisely
  because the late greedy consumes the high part exactly.
* `exists_largestSkipLateAt_of_zeroBit_window` — either way, a single clear bit
  anywhere in `[s, 2*s-d]` yields a late largest false rank at some row of
  `[s, 2*s+1]` (the second branch through `BitR2`'s Theorem A).

Contrapositively, `testBit_true_of_badRun`: if a run of bad rows covers
`[s, 2*s+1]`, then `R` carries a **solid block of `s - d + 1` one-bits** from
the half point `s` up to the ceiling bit `2*s - d`.  With `d` the first late rank
that is about `s / 3` consecutive ones, i.e. a set of relative measure
`2 ^ (d - s - 1)` inside the interval `hhigh` confines `R` to.

**§7, the reductions.**  `half_mem_of_halfPointBitClearCofinally` and the weaker
`half_mem_of_windowBitClearCofinally`: if the bit-clear condition holds at
arbitrarily large admissible rows then `1/2 ∈ mersenneAchievementSet`.  The
`#257` question is thereby reduced to a statement about **a single bit of a
single explicitly computable integer per row**.

**§8, certificates.**  `admissible_fourteen`, `admissible_twenty` (the latter
reusing `BitCorr.Concrete.actual_hypotheses_hold`) discharge
`LateEntryAdmissible` on the genuine object, and both criteria then fire:
`seamRemainder_fourteen_lt`, `largestSkipLateAt_fourteen'`,
`seamRemainder_twenty_lt`.  Row `12` is the sharpness certificate: its window
`[12,15]` is solidly one, and `not_largestSkipLateAt_twelve` proves — from the
same bit reading, again with no row recurrence — that row `12` has no late
largest false rank at all.  So the hypothesis is neither vacuous nor universal.

## What is measured, not proved

Independent computation of the corpus's own greedy over rows `6 … 800`
(795 rows carrying a late rank):

* `hhigh` holds at **all 795** rows; the largest observed ratio
  `lateEntryRemainder s d₀ / 2 ^ (2*s-d₀+1)` is `0.9976` at `s = 65`.
* `hlow` holds at **794** rows; the sole failure is `s = 7`.  This failure was
  later proved at `(7,5)` by `DeclD4.Seven.not_hlow_seven_five`; it is not an
  open numerical exception.
* The exact identity `ρ s = R % 2 ^ (s+1) - ∑_{e taken} 4 ^ (s-e)` holds at all
  795 rows.  (§4 proves the two-sided *bound*; the identity itself is measured.)
* The criterion of §6 is measured to be an **equivalence**:
  `ρ s ≤ 2 ^ s ⟺ bit s of R is clear` at all 795 rows, with no failure in either
  direction.  Only the direction `⟸` is proved here
  (`seamRemainder_lt_two_pow_of_testBit_false`); the direction `⟹` is *not*
  proved — the two-sided bound only yields
  `two_pow_le_seamRemainder_add_of_testBit_true`, which is weaker by
  `lateCorrection s d`.
* Bit `s` of `R` is clear at `388 / 795 = 0.48805` of rows, with geometric gaps
  and a maximum gap of `10`.  This matches the `0.49967` hit density `RemC6`
  reports over `[5,6000]` and the `50.4 %` `RemC3` reports over `[3,4500]`.

## What is not proved

1. **The theorems in this file are conditional on `hhigh` and `hlow`.**
   Subsequent files prove `hhigh` at declined ranks and refute universal
   `hlow` at `(7,5)`.  The natural induction proposed for `hhigh` —
   `R_k < 2 ^ (2*s-k)` propagates to `k+1` — closes on *taken* ranks
   (`R_{k+1} = R_k - w_{k+1} < 2 ^ (2*s-k) - 2 ^ (2*s-k-1) = 2 ^ (2*s-k-1)`) and
   fails on *declined* ranks, where all one knows is `R_k < w_{k+1}`, and
   `w_{k+1}` exceeds `2 ^ (2*s-k-1)` by its own lower binary terms.  That is the
   precise location of the gap.
2. **Cofinality of the bit-clear condition is not proved.**  Nothing here shows
   that bit `s` of `lateEntryRemainder s d₀` is clear infinitely often, nor that
   the window carries a clear bit infinitely often.  Consequently
   `BitR2.RemainderReachesHalfPointCofinally` is **not** established and
   **Erdős #257's `1/2` question is not resolved by this file.**  What is
   established here is a sufficient bit-level criterion about one explicit
   integer per row, conditional on the two side conditions.  Since `hlow`
   fails at `(7,5)`, this is not an unconditional equivalence for all rows;
   `Hlow/H2` treats that failure directly as a hit certificate.
3. **The long bad-run antecedent is not observed in the checked range.**
   `testBit_true_of_badRun` requires `s + 2` consecutive bad rows on
   `[s, 2*s+1]`.  Direct evaluation on rows `4 … 300` finds only the bad rows
   `5, 11, 12, 13`, with maximum consecutive run length `3`; hence no `s ≥ 5`
   in that range instantiates the theorem.  It is a conditional contrapositive,
   not evidence that such long runs occur.

Checked with `lake env lean ErdosProblems/Three/T4.lean` (exit `0`, empty
output).  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace ErdosProblems.ThreeT4

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open Erdos249257.BitCorr

/-! ## 1. Two bit facts about the block `[2 ^ n, 2 ^ (n+1))` -/

/-- A clear bit `n` confines the whole low `n+1` block below `2 ^ n`. -/
theorem mod_two_pow_succ_lt_of_testBit_false {x n : ℕ}
    (hb : Nat.testBit x n = false) :
    x % 2 ^ (n + 1) < 2 ^ n := by
  have hdiv : x % 2 ^ (n + 1) / 2 ^ n = x / 2 ^ n % 2 := by
    rw [show (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 by rw [pow_succ]]
    exact Nat.mod_mul_right_div_self _ _ _
  have hb' : x / 2 ^ n % 2 = 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    simp only [decide_eq_false_iff_not] at hb
    omega
  have hz : x % 2 ^ (n + 1) / 2 ^ n = 0 := by rw [hdiv, hb']
  have hpos : 0 < (2 : ℕ) ^ n := Nat.two_pow_pos n
  rcases Nat.div_eq_zero_iff.mp hz with h | h
  · omega
  · exact h

/-- A set bit `n` puts the low `n+1` block at or above `2 ^ n`. -/
theorem two_pow_le_mod_two_pow_succ_of_testBit_true {x n : ℕ}
    (hb : Nat.testBit x n = true) :
    2 ^ n ≤ x % 2 ^ (n + 1) := by
  have hdiv : x % 2 ^ (n + 1) / 2 ^ n = x / 2 ^ n % 2 := by
    rw [show (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 by rw [pow_succ]]
    exact Nat.mod_mul_right_div_self _ _ _
  have hb' : x / 2 ^ n % 2 = 1 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    simpa using hb
  have hone : 1 ≤ x % 2 ^ (n + 1) / 2 ^ n := by rw [hdiv, hb']
  have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos n)).mp hone
  omega

/-! ## 2. The late zone traps the greedy remainder inside the low block -/

/-- **The trapping lemma.**  Run the descending integer greedy over the late
seam weights `seamWeightsFrom s d` starting from a capacity `C` that satisfies
the two `BitCorr` side conditions.  Then the final remainder is squeezed
between `C % 2 ^ (s+1) - lateCorrection s d` and `C % 2 ^ (s+1)`: the whole
high part of `C` is consumed exactly, and what survives is the low `s+1` bits
minus the `4 ^ k` correction budget of the ranks that were taken. -/
theorem lateGreedy_trapped {s d C : ℕ}
    (hlate : 2 * s < 3 * d)
    (hhigh : C < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ C % 2 ^ (s + 1)) :
    integerGreedyRemainder (seamWeightsFrom s d) C ≤ C % 2 ^ (s + 1) ∧
      C % 2 ^ (s + 1) ≤
        integerGreedyRemainder (seamWeightsFrom s d) C + lateCorrection s d := by
  by_cases hds : d < s
  · have hd2 : 2 ≤ d := by omega
    have hn : s + 1 ≤ 2 * s - d := by omega
    have hexp : 2 * s - (d + 1) + 1 = 2 * s - d := by omega
    have hpow : (2 : ℕ) ^ (2 * s - d + 1) = 2 ^ (2 * s - d) * 2 := by rw [pow_succ]
    have hw :=
      truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank hd2 hds hlate
    have hmodmod : C % 2 ^ (2 * s - d) % 2 ^ (s + 1) = C % 2 ^ (s + 1) :=
      Nat.mod_mod_of_dvd C (pow_dvd_pow 2 hn)
    have hmodlt : C % 2 ^ (2 * s - d) < 2 ^ (2 * s - d) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hcorr := lateCorrection_eq_cons (s := s) (d := d) hds
    -- `omega` cannot atomise `4 ^ (s - d)`; name it.
    set F : ℕ := 4 ^ (s - d) with hFdef
    have hpos : 0 < F := by rw [hFdef]; positivity
    have h4low : F ≤ C % 2 ^ (s + 1) := by omega
    rw [seamWeightsFrom_eq_cons hds, ErdosProblems.RemC6.integerGreedyRemainder_cons, hw]
    by_cases htb : Nat.testBit C (2 * s - d) = true
    · have hge2 : 2 ^ (2 * s - d) ≤ C := Nat.ge_two_pow_of_testBit htb
      have hsplit : C = 2 ^ (2 * s - d) + C % 2 ^ (2 * s - d) := by
        rw [Nat.mod_eq_sub_mod hge2, Nat.mod_eq_of_lt (by omega)]
        omega
      have hmodle : C % 2 ^ (s + 1) ≤ C % 2 ^ (2 * s - d) := by
        rw [← hmodmod]
        exact Nat.mod_le _ _
      have h4m : F ≤ C % 2 ^ (2 * s - d) % 2 ^ (s + 1) := by
        rw [hmodmod]; exact h4low
      have h4f : F ≤ C % 2 ^ (2 * s - d) := le_trans h4m (Nat.mod_le _ _)
      rw [if_pos (by omega)]
      have hCval : C - (2 ^ (2 * s - d) + F) = C % 2 ^ (2 * s - d) - F := by omega
      have hnewmod :
          (C % 2 ^ (2 * s - d) - F) % 2 ^ (s + 1) + F = C % 2 ^ (s + 1) := by
        rw [mod_sub_of_le_mod (Nat.two_pow_pos _) h4m, hmodmod]
        exact Nat.sub_add_cancel h4low
      have hrec :=
        lateGreedy_trapped (s := s) (d := d + 1)
          (C := C % 2 ^ (2 * s - d) - F) (by omega)
          (by rw [hexp]; exact lt_of_le_of_lt (Nat.sub_le _ _) hmodlt)
          (by omega)
      rw [hCval]
      omega
    · have htbf : Nat.testBit C (2 * s - d) = false := by simpa using htb
      have hClt : C < 2 ^ (2 * s - d) := by
        by_contra hcon
        rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
          (by omega) (by omega)] at htbf
        exact Bool.noConfusion htbf
      rw [if_neg (by omega)]
      have hsucc := lateCorrection_succ_le s d
      have hrec :=
        lateGreedy_trapped (s := s) (d := d + 1) (C := C) (by omega)
          (by rw [hexp]; omega) (le_trans hsucc hlow)
      omega
  · have hcle : C < 2 ^ (s + 1) :=
      lt_of_lt_of_le hhigh (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [seamWeightsFrom_eq_nil (by omega), ErdosProblems.RemC6.integerGreedyRemainder_nil,
      Nat.mod_eq_of_lt hcle]
    omega
termination_by s - d
decreasing_by all_goals omega

/-! ## 3. Bridge: the seam remainder is the late-zone greedy remainder -/

/-- The corpus's own `seamIntegerGreedyRemainder` is exactly the descending
greedy over the late weights, started at `lateEntryRemainder s d`. -/
theorem seamIntegerGreedyRemainder_eq_lateGreedy {s d : ℕ} (h2 : 2 ≤ d) :
    seamIntegerGreedyRemainder s =
      integerGreedyRemainder (seamWeightsFrom s d) (lateEntryRemainder s d) := by
  show integerGreedyRemainder (seamWeights s) (seamSubsetTarget s) = _
  conv_lhs => rw [seamWeights_eq_take_append h2]
  rw [ErdosProblems.RemC6.integerGreedyRemainder_append]
  rfl

/-! ## 4. The master two-sided bound on `ρ s` -/

/-- **`ρ s` is the low `s+1` bits of the late-entry remainder, up to the
correction budget.**  Both side conditions are `BitCorr`'s, at one late rank. -/
theorem seamRemainder_bounds {s d : ℕ} (h2 : 2 ≤ d) (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)) :
    seamIntegerGreedyRemainder s ≤ lateEntryRemainder s d % 2 ^ (s + 1) ∧
      lateEntryRemainder s d % 2 ^ (s + 1) ≤
        seamIntegerGreedyRemainder s + lateCorrection s d := by
  rw [seamIntegerGreedyRemainder_eq_lateGreedy h2]
  exact lateGreedy_trapped hlate hhigh hlow

/-- **The invariant `C6` wanted.**  At any row carrying a late rank with the two
side conditions, `ρ s < 2 ^ (s + 1)` — with no hypothesis about *which* ranks are
skipped, and in particular at the rows where every late rank is taken.  Compare
`RemC6.seamIntegerGreedyRemainder_lt_three_mul_two_pow`, which needs a late
largest declined rank and gives `3 * 2 ^ s`. -/
theorem seamRemainder_lt_two_pow_succ {s d : ℕ} (h2 : 2 ≤ d) (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) :=
  lt_of_le_of_lt (seamRemainder_bounds h2 hlate hhigh hlow).1
    (Nat.mod_lt _ (Nat.two_pow_pos _))

/-! ## 5. Sharpening the correction budget below the half point -/

/-- In the late zone the whole `4 ^ k` correction budget is below `2 ^ s`, not
merely below `2 ^ (s+1)` as in `BitCorr.lateCorrection_lt_two_pow`. -/
theorem lateCorrection_lt_two_pow_of_late {s d : ℕ} (hs : 4 ≤ s) (hds : d ≤ s)
    (hlate : 2 * s < 3 * d) :
    lateCorrection s d < 2 ^ s := by
  have hclosed := three_mul_lateCorrection_add_four (s := s) (d := d) hds
  have hfour : (4 : ℕ) ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  rw [hfour] at hclosed
  have hmono : (2 : ℕ) ^ (2 * (s - d) + 2) ≤ 2 ^ s :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsplit : (2 : ℕ) ^ (2 * (s - d) + 2) = 4 * 2 ^ (2 * (s - d)) := by
    rw [pow_add]; ring
  omega

/-! ## 6. The rank-layer criterion: one clear bit decides the row -/

/-- **A clear bit strictly above the half point is a skipped late rank.**  This
is the criterion the brief asks for: it never mentions the top rank `s - 1`, and
it never consults the row recurrence.  Reading a single zero bit of the entering
remainder, anywhere in the window `(s, 2*s-d]`, produces `LargestSkipLateAt s`
via `SkipD3.largestSkipLateAt_of_late_skip`. -/
theorem largestSkipLateAt_of_zeroBit {s d j : ℕ}
    (h2 : 2 ≤ d) (hds : d ≤ s) (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))
    (hj1 : s + 1 ≤ j) (hj2 : j ≤ 2 * s - d)
    (hbit : Nat.testBit (lateEntryRemainder s d) j = false) :
    LargestSkipLateAt s := by
  have hjd : j + d ≤ 2 * s := by omega
  have hde : d ≤ 2 * s - j := by omega
  have hes : 2 * s - j < s := by omega
  have hback : 2 * s - (2 * s - j) = j := by omega
  have hnot : 2 * s - j ∉ seamWordSupport (seamGreedyWord s) := by
    rw [mem_seamGreedySupport_iff_testBit h2 hds hlate hhigh hlow hde hes, hback,
      hbit]
    simp
  exact SkipD3.largestSkipLateAt_of_late_skip (by omega) hes (by omega) hnot

/-- **A clear bit exactly at the half point puts `ρ s` below `2 ^ s`.**  Bit `s`
is the one position of the entering remainder that no late rank tests — the rank
`e` with `2 * s - e = s` would be `e = s`, outside the word.  It is nonetheless
decisive, because the late greedy consumes the entire high part exactly. -/
theorem seamRemainder_lt_two_pow_of_testBit_false {s d : ℕ} (h2 : 2 ≤ d)
    (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))
    (hbit : Nat.testBit (lateEntryRemainder s d) s = false) :
    seamIntegerGreedyRemainder s < 2 ^ s :=
  lt_of_le_of_lt (seamRemainder_bounds h2 hlate hhigh hlow).1
    (mod_two_pow_succ_lt_of_testBit_false hbit)

/-- The partial converse that the two-sided bound actually delivers: a set bit
`s` keeps `ρ s` within the correction budget of the half point.  It does **not**
give `2 ^ s < ρ s`; see the measurement note. -/
theorem two_pow_le_seamRemainder_add_of_testBit_true {s d : ℕ} (h2 : 2 ≤ d)
    (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))
    (hbit : Nat.testBit (lateEntryRemainder s d) s = true) :
    2 ^ s ≤ seamIntegerGreedyRemainder s + lateCorrection s d :=
  le_trans (two_pow_le_mod_two_pow_succ_of_testBit_true hbit)
    (seamRemainder_bounds h2 hlate hhigh hlow).2

/-- **The window dichotomy.**  A single clear bit anywhere in the closed window
`[s, 2*s-d]` of the entering remainder produces a late largest false rank at some
row of `[s, 2*s+1]`.  The two halves are genuinely different mechanisms: bits
above `s` fire at row `s` itself through the rank layer; bit `s` fires through
`BitR2`'s Theorem A at a later row. -/
theorem exists_largestSkipLateAt_of_zeroBit_window {s d j : ℕ}
    (hs : 5 ≤ s) (h2 : 2 ≤ d) (hds : d ≤ s) (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))
    (hj1 : s ≤ j) (hj2 : j ≤ 2 * s - d)
    (hbit : Nat.testBit (lateEntryRemainder s d) j = false) :
    ∃ t : ℕ, s ≤ t ∧ t ≤ 2 * s + 1 ∧ LargestSkipLateAt t := by
  rcases Nat.eq_or_lt_of_le hj1 with hje | hjlt
  · have hbit' : Nat.testBit (lateEntryRemainder s d) s = false := by
      rw [← hje] at hbit; exact hbit
    have hrem : seamIntegerGreedyRemainder s ≤ 2 ^ s :=
      le_of_lt (seamRemainder_lt_two_pow_of_testBit_false h2 hlate hhigh hlow hbit')
    obtain ⟨t, ht1, ht2, ht3⟩ :=
      ErdosProblems.BitR2.exists_largestSkipLateAt_of_remainder_le_two_pow hs hrem
    exact ⟨t, by omega, by omega, ht3⟩
  · exact ⟨s, le_rfl, by omega,
      largestSkipLateAt_of_zeroBit h2 hds hlate hhigh hlow (by omega) hj2 hbit⟩

/-! ### The contrapositive: a bad row is a solid block of one-bits -/

/-- **Rigidity at a single bad row.**  If row `s` has no late largest false rank
then every bit of the entering remainder strictly between the half point and the
ceiling is set. -/
theorem testBit_true_of_not_largestSkipLateAt {s d : ℕ}
    (h2 : 2 ≤ d) (hds : d ≤ s) (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))
    (hbad : ¬ LargestSkipLateAt s) :
    ∀ j : ℕ, s + 1 ≤ j → j ≤ 2 * s - d →
      Nat.testBit (lateEntryRemainder s d) j = true := by
  intro j hj1 hj2
  by_contra hb
  exact hbad
    (largestSkipLateAt_of_zeroBit h2 hds hlate hhigh hlow hj1 hj2 (by simpa using hb))

/-- **Rigidity across a bad run.**  If *no* row of `[s, 2*s+1]` has a late
largest false rank then the entering remainder of row `s` carries a solid block
of `s - d + 1` one-bits, from the half point `s` all the way up to the ceiling
bit `2 * s - d`.  For `d` the first late rank this is about `s / 3` consecutive
ones: a set of relative measure `2 ^ (d - s - 1)` inside the interval that
`hhigh` confines the remainder to. -/
theorem testBit_true_of_badRun {s d : ℕ} (hs : 5 ≤ s)
    (h2 : 2 ≤ d) (hds : d ≤ s) (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))
    (hbad : ∀ t : ℕ, s ≤ t → t ≤ 2 * s + 1 → ¬ LargestSkipLateAt t) :
    ∀ j : ℕ, s ≤ j → j ≤ 2 * s - d →
      Nat.testBit (lateEntryRemainder s d) j = true := by
  intro j hj1 hj2
  by_contra hb
  obtain ⟨t, ht1, ht2, ht3⟩ :=
    exists_largestSkipLateAt_of_zeroBit_window hs h2 hds hlate hhigh hlow hj1 hj2
      (by simpa using hb)
  exact hbad t ht1 ht2 ht3

/-- The top bit of the window, made explicit: a bad row is pinned into the upper
half of the interval `hhigh` allows. -/
theorem two_pow_le_lateEntryRemainder_of_not_largestSkipLateAt {s d : ℕ}
    (h2 : 2 ≤ d) (hds : d < s) (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))
    (hbad : ¬ LargestSkipLateAt s) :
    2 ^ (2 * s - d) ≤ lateEntryRemainder s d :=
  Nat.ge_two_pow_of_testBit
    (testBit_true_of_not_largestSkipLateAt h2 (by omega) hlate hhigh hlow hbad
      (2 * s - d) (by omega) le_rfl)

/-! ## 7. The cofinal reductions -/

/-- The two `BitCorr` side conditions at a late rank `d` of row `s`. -/
def LateEntryAdmissible (s d : ℕ) : Prop :=
  2 ≤ d ∧ d ≤ s ∧ 2 * s < 3 * d ∧
    lateEntryRemainder s d < 2 ^ (2 * s - d + 1) ∧
    lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)

/-- Bit `s` of the entering remainder is clear at arbitrarily large rows. -/
def HalfPointBitClearCofinally : Prop :=
  ∀ N : ℕ, ∃ s d : ℕ, N ≤ s ∧ 5 ≤ s ∧ LateEntryAdmissible s d ∧
    Nat.testBit (lateEntryRemainder s d) s = false

/-- Some bit of the entering remainder in the closed window `[s, 2*s-d]` is
clear at arbitrarily large rows. -/
def WindowBitClearCofinally : Prop :=
  ∀ N : ℕ, ∃ s d j : ℕ, N ≤ s ∧ 5 ≤ s ∧ LateEntryAdmissible s d ∧
    s ≤ j ∧ j ≤ 2 * s - d ∧ Nat.testBit (lateEntryRemainder s d) j = false

theorem remainderReachesHalfPointCofinally_of_halfPointBitClear
    (h : HalfPointBitClearCofinally) :
    ErdosProblems.BitR2.RemainderReachesHalfPointCofinally := by
  intro N
  obtain ⟨s, d, hNs, hs5, ⟨h2, hds, hlate, hhigh, hlow⟩, hbit⟩ := h N
  exact ⟨s, hNs, hs5,
    le_of_lt (seamRemainder_lt_two_pow_of_testBit_false h2 hlate hhigh hlow hbit)⟩

/-- **Reduction 1.**  If bit `s` of the entering remainder is clear at
arbitrarily large admissible rows, Erdős #257's `1/2` question is answered
positively. -/
theorem half_mem_of_halfPointBitClearCofinally (h : HalfPointBitClearCofinally) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  ErdosProblems.BitR2.half_mem_of_remainderReachesHalfPointCofinally
    (remainderReachesHalfPointCofinally_of_halfPointBitClear h)

/-- **Reduction 2, the weaker hypothesis.**  It is enough that *some* bit of the
window `[s, 2*s-d]` is clear cofinally often — the position may vary with the
row, and no control over which rank is skipped is needed. -/
theorem half_mem_of_windowBitClearCofinally (h : WindowBitClearCofinally) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  rw [AngleD2.half_mem_iff_unboundedLargestSkipLate]
  intro N
  obtain ⟨s, d, j, hNs, hs5, ⟨h2, hds, hlate, hhigh, hlow⟩, hj1, hj2, hbit⟩ := h N
  obtain ⟨t, ht1, _, ht3⟩ :=
    exists_largestSkipLateAt_of_zeroBit_window hs5 h2 hds hlate hhigh hlow hj1 hj2 hbit
  exact ⟨t, by omega, ht3⟩

/-! ## 8. Non-vacuity, and the sharpness of the criterion -/

namespace Concrete

/-- The twelve seam weights at `s = 14`, from the corpus definition
`truncatedMersenneWeight s d = 4 ^ s / (2 ^ d - 1)`. -/
theorem seamWeights_fourteen :
    seamWeights 14 =
      [89478485, 38347922, 17895697, 8659208, 4260880, 2113665, 1052688,
        525314, 262400, 131136, 65552, 32772] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_nil (by norm_num)]
  simp only [truncatedMersenneWeight]
  decide +kernel

theorem lateCorrection_fourteen_ten : lateCorrection 14 10 = 340 := by
  rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_zero (by norm_num)]
  decide +kernel

/-- The genuine remainder entering the late zone at `s = 14`. -/
theorem lateEntryRemainder_fourteen_ten : lateEntryRemainder 14 10 = 392 := by
  unfold lateEntryRemainder earlyWeights
  rw [seamWeights_fourteen]
  simp only [seamSubsetTarget]
  decide +kernel

/-- **Anti-vacuity, row 14.**  `10` is a late rank of row `14` and both side
conditions hold for the actual entering remainder. -/
theorem admissible_fourteen : LateEntryAdmissible 14 10 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [lateEntryRemainder_fourteen_ten]; norm_num
  · rw [lateEntryRemainder_fourteen_ten, lateCorrection_fourteen_ten]
    decide +kernel

theorem testBit_fourteen_halfPoint :
    Nat.testBit (lateEntryRemainder 14 10) 14 = false := by
  rw [lateEntryRemainder_fourteen_ten]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

theorem testBit_fourteen_fifteen :
    Nat.testBit (lateEntryRemainder 14 10) 15 = false := by
  rw [lateEntryRemainder_fourteen_ten]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

/-- **The half-point criterion fires at row 14**, from one clear bit.  The *fact*
is not new — `RemC6.seamIntegerGreedyRemainder_fourteen_le_two_pow` has it, by
evaluating the whole greedy — the point is that here it is read off bit `14` of
`392` with no evaluation of `ρ 14` at all. -/
theorem seamRemainder_fourteen_lt : seamIntegerGreedyRemainder 14 < 2 ^ 14 :=
  seamRemainder_lt_two_pow_of_testBit_false (by norm_num) (by norm_num)
    admissible_fourteen.2.2.2.1 admissible_fourteen.2.2.2.2
    testBit_fourteen_halfPoint

/-- **The rank criterion fires at row 14**, from a different clear bit, without
ever naming the top rank.  Again the fact is the corpus's
`largestSkipLateAt_fourteen`; the route is what is new — bit `15` of `392`. -/
theorem largestSkipLateAt_fourteen' : LargestSkipLateAt 14 :=
  largestSkipLateAt_of_zeroBit (by norm_num) (by norm_num) (by norm_num)
    admissible_fourteen.2.2.2.1 admissible_fourteen.2.2.2.2
    (by norm_num) (by norm_num) testBit_fourteen_fifteen

/-! ### Row 20: the criterion on `BitCorr`'s own certified remainder -/

/-- **Anti-vacuity, row 20**, reusing `BitCorr.Concrete.actual_hypotheses_hold`. -/
theorem admissible_twenty : LateEntryAdmissible 20 14 :=
  ⟨by norm_num, by norm_num, by norm_num,
    BitCorr.Concrete.actual_hypotheses_hold.1,
    BitCorr.Concrete.actual_hypotheses_hold.2⟩

theorem testBit_twenty_halfPoint :
    Nat.testBit (lateEntryRemainder 20 14) 20 = false := by
  rw [BitCorr.Concrete.lateEntryRemainder_twenty_fourteen]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

theorem seamRemainder_twenty_lt : seamIntegerGreedyRemainder 20 < 2 ^ 20 :=
  seamRemainder_lt_two_pow_of_testBit_false (by norm_num) (by norm_num)
    admissible_twenty.2.2.2.1 admissible_twenty.2.2.2.2 testBit_twenty_halfPoint

/-! ### Row 12: the criterion is sharp, not merely sufficient

Row `12` is a row where the window `[12, 15]` of the entering remainder is
*solidly one*.  Both conclusions then genuinely fail: `ρ 12 = 5836 > 2 ^ 12` and
`¬ LargestSkipLateAt 12`.  So the hypothesis of §6–§7 is not something that
holds at every row, and the criterion is calibrated exactly. -/

theorem seamWeights_twelve :
    seamWeights 12 =
      [5592405, 2396745, 1118481, 541200, 266305, 132104, 65793, 32832,
        16400, 8196] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_nil (by norm_num)]
  simp only [truncatedMersenneWeight]
  decide +kernel

theorem lateCorrection_twelve_nine : lateCorrection 12 9 = 84 := by
  rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_cons (by norm_num), lateCorrection_eq_zero (by norm_num)]
  decide +kernel

theorem lateEntryRemainder_twelve_nine : lateEntryRemainder 12 9 = 63264 := by
  unfold lateEntryRemainder earlyWeights
  rw [seamWeights_twelve]
  simp only [seamSubsetTarget]
  decide +kernel

theorem admissible_twelve : LateEntryAdmissible 12 9 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [lateEntryRemainder_twelve_nine]; norm_num
  · rw [lateEntryRemainder_twelve_nine, lateCorrection_twelve_nine]
    decide +kernel

/-- Every bit of the window `[12, 15]` is set at row `12`. -/
theorem testBit_twelve_window :
    ∀ j : ℕ, 12 ≤ j → j ≤ 15 →
      Nat.testBit (lateEntryRemainder 12 9) j = true := by
  intro j h1 h2
  rw [lateEntryRemainder_twelve_nine]
  interval_cases j <;>
    (simp only [Nat.testBit_eq_decide_div_mod_eq]; decide +kernel)

/-- **Sharpness.**  Row `12` has no late largest false rank at all — proved from
the same bit reading, with no appeal to the row recurrence. -/
theorem not_largestSkipLateAt_twelve : ¬ LargestSkipLateAt 12 := by
  rintro ⟨m, ⟨hm2, hms, hnot, _⟩, hlate⟩
  have h9 : 9 ≤ m := by omega
  apply hnot
  rw [mem_seamGreedySupport_iff_testBit (s := 12) (d := 9) (e := m)
      (by norm_num) (by norm_num) (by norm_num)
      admissible_twelve.2.2.2.1 admissible_twelve.2.2.2.2 h9 hms]
  have hj1 : 12 ≤ 2 * 12 - m := by omega
  have hj2 : 2 * 12 - m ≤ 15 := by omega
  exact testBit_twelve_window _ hj1 hj2

end Concrete

end ErdosProblems.ThreeT4
