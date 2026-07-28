/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Three.T1
import ErdosProblems.Three.T4

/-!
# D4 — `hlow` is the wrong side condition, and it is not the obstruction

`ErdosProblems/Three/T4.lean` proves `ρ s < 2 ^ (s + 1)` conditionally on two
side conditions at a late rank `d` of row `s`, both inherited from
`ErdosProblems/Bit/Corr1.lean`:

* `hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1)`
* `hlow  : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1)`.

The brief for this file was to attack `hlow`.  Three things are established.

**1.  `hlow` is FALSE.**  Not open — false, with an explicit counterexample.  At
`s = 7`, at the *first* late rank `d = 5`, the genuine entering remainder is
`lateEntryRemainder 7 5 = 263`, its low block is `263 % 2 ^ 8 = 7`, and the
correction budget is `lateCorrection 7 5 = 20 > 7`.  See `not_hlow_seven_five`
and `not_lateEntryAdmissible_seven_five`.  Meanwhile `hhigh` *holds* at that very
rank (`hhigh_seven_five : 263 < 2 ^ 10`), so the two conditions are genuinely
independent and `hlow` is the one that breaks.

The failure is a failure of the *route*, not of the conclusion: `ρ 7 = 3 < 2 ^ 7`
(`seamIntegerGreedyRemainder_seven`), so row `7` is in fact a half-point hit.
This is the same phenomenon `ErdosProblems/Three/T1.lean` found for `C6`'s
residual invariant.

Row `7` is nevertheless recoverable, by moving `d` up one: `LateEntryAdmissible
7 6` **holds** (`admissible_seven_six`).  So `hlow` is not a property of the row;
it is a property of the *choice of late rank*, and the first late rank is not the
right choice.

**2.  `hlow` can be deleted from the chain outright**, at an additive cost.
`lateGreedy_lt_of_high` runs the late greedy under `hhigh` alone and proves

    integerGreedyRemainder (seamWeightsFrom s d) C < 2 ^ (s + 1) + 4 ^ (s - d),

whence `seamRemainder_lt_two_pow_succ_add`:

    ρ s < 2 ^ (s + 1) + 4 ^ (s - d)      (hhigh only, no `hlow`)

and, since `2 * (s - d) < d ≤ s` in the late zone, the clean corollary
`seamRemainder_lt_of_high : ρ s < 2 ^ (s + 1) + 2 ^ (s - 1) < 3 * 2 ^ s`.  This
is the whole of `T4 §4` minus the constant.  The induction closes because in the
late zone the *declined* branch loses only the single term `4 ^ (s - d)`, not a
whole binary tail — which is exactly why the same induction fails at early ranks
(`T1.residual_lt_of_declined`).

The additive term is **not an artefact of the arbitrary-capacity induction**:
`sharpness_seven_five` exhibits a capacity satisfying `hhigh` whose
late-greedy remainder is `267 ≥ 2 ^ 8`.  That capacity is `527`, not the genuine
entering remainder `lateEntryRemainder 7 5 = 263`.  The theorem therefore shows
that this argument cannot remove the slack for arbitrary capacities; it does
not refute an implication specialised to genuine entering remainders.

**3.  The right low-side condition is `bitCorrection`, not `lateCorrection`.**
`lateCorrection s d` charges the greedy for *every* late rank.  Only the ranks it
actually takes need paying for, and in the late zone those are read off the bits
of the entering capacity (`BitCorr.integerGreedyBits_seamWeightsFrom_eq_lateBitWord`).
`bitCorrection s C d` sums `4 ^ (s - e)` over the late ranks `e` with bit
`2 * s - e` of `C` set.  Then

* `bitCorrection_le_lateCorrection` — it is never larger, so `hlow` implies it
  (`bitAdmissible_of_lateEntryAdmissible`);
* `lateGreedy_eq_mod_sub_bitCorrection` — the **exact identity**
  `integerGreedyRemainder (seamWeightsFrom s d) C = C % 2 ^ (s+1) − bitCorrection s C d`
  under `hhigh` together with `bitCorrection s C d ≤ C % 2 ^ (s + 1)`.  T4 states
  only a two-sided *bound*, under the stronger `hlow`, and records the identity
  itself as measured-not-proved; both are strengthened here;
* `seamRemainder_lt_two_pow_succ'`, `seamRemainder_lt_two_pow_of_testBit_false'`,
  `seamRemainder_bounds'`, `two_pow_le_seamRemainder_add_of_testBit_true'` — T4
  §4 and §6's conclusions, re-proved on the weaker hypothesis;
* `bitLow_seven_five` — the weaker condition **holds at the row where `hlow`
  fails**, and `seamRemainder_seven_lt` re-derives `ρ 7 < 2 ^ 7` there through
  the repaired route, at the first late rank.

**4.  `hhigh` is `RemC6`'s residual ceiling, verbatim** (§5).  This is proved,
not asserted: `lateEntryRemainder_eq_seamResidualUpto` identifies the entering
remainder with `T1.seamResidualUpto s (d - 1)`, and `hhigh_iff_seamResidualUpto`
then reads `hhigh` as `T1.ResidualInvariant` at the single rank `d - 1`.
`hhigh_thirteen_nine` shows why `T1.not_residualInvariant` does not refute it:
`T1`'s counterexample is at rank `7` of row `13`, the first late rank is `9`, and
the tangency self-corrects at rank `8` (`524419 ↦ 261247 < 2 ^ 18`).

## Verdict on the brief's question

`hlow` is not the remaining obstruction in this route.  It is refutable as
stated (§1), removable at a cost of `4 ^ (s - d)` (§2), and repairable at its
known failure by charging only the ranks the greedy takes (§3).  The remaining
hypothesis is `hhigh`: §4 identifies it with `RemC6`'s residual invariant at
the single rank `d - 1`.  The cited terminal-rank theorem
`T1.IntervalCeiling.two_pow_lt` alone does not establish the corresponding
no-go at this earlier rank.  The adversarial verifier
`Decl/verify/D4.lean` supplies the correctly scoped theorem
`no_intervalCeiling_certifies_hhigh`.  This rules out that interval-ceiling
method, not every possible proof of `hhigh`.

## Measured, not proved

Reproducing the corpus definitions verbatim — including `bitCorrection` exactly
as defined in §4 — and scanning `s ∈ [6, 2200]` at the first late rank
`d₀ s = 2 * s / 3 + 1`:

* `hhigh` holds at **every** row of `[6, 2200]`: the failure set is **empty**.
  (It fails at `s = 5`, the corpus's known degenerate row, which is excluded
  throughout.)
* `hlow` fails at **exactly one** row of `[6, 2200]`, namely `s = 7`.  The
  failure set is `{7}`, not a maximum-ratio statistic.  That single failure is
  the theorem `not_hlow_seven_five` below.
* `bitCorrection s (lateEntryRemainder s d₀) d₀ ≤ lateEntryRemainder s d₀ % 2 ^ (s+1)`
  — the §4 condition — holds at **every** row of `[6, 2200]`, `s = 7` included:
  empty failure set.
* The exact identity
  `ρ s = lateEntryRemainder s d₀ % 2 ^ (s+1) − bitCorrection s (lateEntryRemainder s d₀) d₀`
  holds at every row of `[6, 2200]`: empty failure set.  (§4 proves it under the
  same condition, so this is a consistency check on the hypothesis, not on the
  theorem.)
* The sufficient condition of §2 (`hlow_of_testBit`: some bit of the entering
  remainder lies in the window `[2 * (s - d₀) + 1, s]`) fails at **exactly two**
  rows of `[6, 2200]`: `s = 7` and `s = 14`.  At `s = 14` it fails while `hlow`
  still holds, by the thin margin `392 ≥ 340`; that row is T4's own certificate
  row.  So §2 does not subsume §1's counterexample analysis, and is reported here
  with its exact failure set rather than a summary.

None of the above is used in any proof below.

Nothing here proves cofinality of anything, and **Erdős #257 is not resolved by
this file.**  In particular `seamRemainder_lt_two_pow_succ_add` — the one
genuinely unconditional-in-`hlow` bound — is *not* a resolution of anything: it
is still conditional on `hhigh`, and even the exact `ρ s < 2 ^ (s + 1)` would
not settle `#257`, since `RemC1`'s surplus model satisfies `ρ s ≤ 2 ^ (s + 1)`
at every row and never reaches the half point.

Checked with `lake env lean ErdosProblems/Decl/D4.lean` (exit `0`, empty output).
No `sorry`, no `axiom`, no `native_decide`.
-/

namespace ErdosProblems.DeclD4

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open Erdos249257.BitCorr

/-! ## 0. Low-block plumbing -/

/-- Truncating to fewer bits can only shrink the residue. -/
theorem mod_two_pow_le_mod_two_pow (x : ℕ) {j n : ℕ} (h : j ≤ n) :
    x % 2 ^ j ≤ x % 2 ^ n := by
  have hdvd : (2 : ℕ) ^ j ∣ 2 ^ n := pow_dvd_pow 2 h
  have := Nat.mod_mod_of_dvd x hdvd
  calc x % 2 ^ j = x % 2 ^ n % 2 ^ j := this.symm
    _ ≤ x % 2 ^ n := Nat.mod_le _ _

/-- A set bit anywhere at or below the half point puts the whole low block at or
above that bit's value. -/
theorem two_pow_le_mod_two_pow_succ_of_testBit {C j s : ℕ} (hjs : j ≤ s)
    (hbit : Nat.testBit C j = true) :
    2 ^ j ≤ C % 2 ^ (s + 1) :=
  le_trans (ThreeT4.two_pow_le_mod_two_pow_succ_of_testBit_true hbit)
    (mod_two_pow_le_mod_two_pow C (by omega))

/-! ## 1. `hlow` is false: the counterexample at row `7`

The whole of this section is computation on the corpus's own definitions.  `7` is
the smallest row at which the correction budget outruns the low block of the
genuine entering remainder, and — by the scan recorded in the header — the only
one below `2000`. -/

namespace Seven

/-- The five seam weights of row `7`, from `truncatedMersenneWeight s d = 4 ^ s / (2 ^ d - 1)`. -/
theorem seamWeights_seven : seamWeights 7 = [5461, 2340, 1092, 528, 260] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_nil (by norm_num)]
  simp only [truncatedMersenneWeight]
  decide +kernel

/-- `5` really is the first late rank of row `7`. -/
theorem five_is_first_late : 2 * 7 < 3 * 5 ∧ ¬ (2 * 7 < 3 * 4) := ⟨by norm_num, by norm_num⟩

theorem lateEntryRemainder_seven_five : lateEntryRemainder 7 5 = 263 := by
  unfold lateEntryRemainder earlyWeights
  rw [seamWeights_seven]
  simp only [seamSubsetTarget]
  decide +kernel

theorem lateCorrection_seven_five : lateCorrection 7 5 = 20 := by
  rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_zero (by norm_num)]
  decide +kernel

/-- **`hhigh` holds at row `7`, rank `5`.**  So the failure below is not a
degenerate row on which everything collapses. -/
theorem hhigh_seven_five : lateEntryRemainder 7 5 < 2 ^ (2 * 7 - 5 + 1) := by
  rw [lateEntryRemainder_seven_five]; norm_num

/-- **The refutation.**  The low block of the genuine entering remainder of row
`7` is `7`, and the correction budget the greedy is charged for is `20`.  So
`hlow` is false — the `T4` side condition does not hold at the first late rank of
every row. -/
theorem not_hlow_seven_five :
    ¬ (lateCorrection 7 5 ≤ lateEntryRemainder 7 5 % 2 ^ (7 + 1)) := by
  rw [lateEntryRemainder_seven_five, lateCorrection_seven_five]
  decide +kernel

/-- The failure by the numbers: `20 = 7 + 13`, so `hlow` misses by `13` out of a
low block of `256`. -/
theorem hlow_seven_five_deficit :
    lateEntryRemainder 7 5 % 2 ^ (7 + 1) + 13 = lateCorrection 7 5 := by
  rw [lateEntryRemainder_seven_five, lateCorrection_seven_five]
  decide +kernel

/-- Consequently `T4`'s admissibility predicate fails at the first late rank of
row `7`. -/
theorem not_lateEntryAdmissible_seven_five : ¬ ThreeT4.LateEntryAdmissible 7 5 := by
  rintro ⟨-, -, -, -, hlow⟩
  exact not_hlow_seven_five hlow

/-! ### The conclusion survives, and the row is recovered at the next rank -/

theorem seamIntegerGreedyRemainder_seven : seamIntegerGreedyRemainder 7 = 3 := by
  show integerGreedyRemainder (seamWeights 7) (seamSubsetTarget 7) = 3
  rw [seamWeights_seven]
  simp only [seamSubsetTarget]
  decide +kernel

/-- **The conclusion `T4` wanted is true at row `7` anyway** — in fact row `7` is
a half-point *hit*.  `hlow` is a false route to a true statement, exactly as
`T1.not_residualInvariant` found for `C6`'s residual invariant. -/
theorem seven_is_a_hit : seamIntegerGreedyRemainder 7 ≤ 2 ^ 7 := by
  rw [seamIntegerGreedyRemainder_seven]; norm_num

theorem lateEntryRemainder_seven_six : lateEntryRemainder 7 6 = 263 := by
  unfold lateEntryRemainder earlyWeights
  rw [seamWeights_seven]
  simp only [seamSubsetTarget]
  decide +kernel

theorem lateCorrection_seven_six : lateCorrection 7 6 = 4 := by
  rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_zero (by norm_num)]
  decide +kernel

/-- **Row `7` is admissible after all — at rank `6`.**  Rank `5` is declined by
the greedy, so it carries no correction, yet `lateCorrection` charges `16` for
it; dropping it from the budget leaves `4 ≤ 7`.  `hlow` is therefore a property
of the *choice of late rank*, not of the row, and the first late rank is the
worst choice. -/
theorem admissible_seven_six : ThreeT4.LateEntryAdmissible 7 6 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [lateEntryRemainder_seven_six]; norm_num
  · rw [lateEntryRemainder_seven_six, lateCorrection_seven_six]
    decide +kernel

/-- The two facts side by side: the same row, the same entering remainder, the
same `hhigh`; only the rank moves, and `hlow` flips. -/
theorem hlow_is_rank_dependent :
    ¬ ThreeT4.LateEntryAdmissible 7 5 ∧ ThreeT4.LateEntryAdmissible 7 6 :=
  ⟨not_lateEntryAdmissible_seven_five, admissible_seven_six⟩

end Seven

/-! ## 2. When `hlow` is free: a single set bit pays for the whole budget

The budget is `lateCorrection s d = (4 ^ (s - d + 1) - 4) / 3 < 2 ^ (2 * (s - d) + 1)`.
So any set bit of the capacity at a position in the window
`[2 * (s - d) + 1, s]` discharges `hlow` immediately.  In the late zone that
window has about `s / 3` positions. -/

/-- The correction budget is below the first power of two above `2 * 4 ^ (s - d)`. -/
theorem lateCorrection_lt_two_pow_two_mul {s d : ℕ} (hds : d ≤ s) :
    lateCorrection s d < 2 ^ (2 * (s - d) + 1) := by
  have hclosed := three_mul_lateCorrection_add_four (s := s) (d := d) hds
  have hfour : (4 : ℕ) ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  have hsplit : (2 : ℕ) ^ (2 * (s - d) + 1) = 2 * 2 ^ (2 * (s - d)) := by
    rw [pow_succ]; ring
  omega

/-- **`hlow` from one bit.**  A set bit of the capacity anywhere in the window
`[2 * (s - d) + 1, s]` discharges the whole correction budget. -/
theorem hlow_of_testBit {s d j C : ℕ} (hds : d ≤ s)
    (hj1 : 2 * (s - d) + 1 ≤ j) (hj2 : j ≤ s)
    (hbit : Nat.testBit C j = true) :
    lateCorrection s d ≤ C % 2 ^ (s + 1) := by
  have h1 : (2 : ℕ) ^ (2 * (s - d) + 1) ≤ 2 ^ j :=
    Nat.pow_le_pow_right (by norm_num) hj1
  have h2 : (2 : ℕ) ^ j ≤ C % 2 ^ (s + 1) :=
    two_pow_le_mod_two_pow_succ_of_testBit hj2 hbit
  have h3 := lateCorrection_lt_two_pow_two_mul (s := s) (d := d) hds
  omega

/-- In the late zone the window `[2 * (s - d) + 1, s]` is non-empty: `2 * s < 3 * d`
forces `2 * (s - d) < d ≤ s`. -/
theorem window_nonempty {s d : ℕ} (hds : d ≤ s) (hlate : 2 * s < 3 * d) :
    2 * (s - d) + 1 ≤ s := by omega

/-- **A bad row pays for itself.**  If bit `s` of the capacity is set — the
condition under which `T4`'s half-point criterion says nothing — then `hlow`
holds automatically.  So `hlow` can only ever fail on rows whose entering
remainder has bit `s` clear, i.e. on the rows `T4` wants to call hits. -/
theorem hlow_of_testBit_halfPoint {s d C : ℕ} (hds : d ≤ s)
    (hlate : 2 * s < 3 * d) (hbit : Nat.testBit C s = true) :
    lateCorrection s d ≤ C % 2 ^ (s + 1) :=
  hlow_of_testBit hds (window_nonempty hds hlate) le_rfl hbit

/-- The contrapositive, as a rigidity statement: where `hlow` fails, an entire
block of about `s / 3` bits of the capacity is clear. -/
theorem testBit_false_of_not_hlow {s d C : ℕ} (hds : d ≤ s)
    (hfail : ¬ lateCorrection s d ≤ C % 2 ^ (s + 1)) :
    ∀ j : ℕ, 2 * (s - d) + 1 ≤ j → j ≤ s → Nat.testBit C j = false := by
  intro j hj1 hj2
  by_contra hb
  exact hfail (hlow_of_testBit hds hj1 hj2 (by simpa using hb))

/-- **Anti-vacuity for §2.**  `BitCorr`'s own certified capacity at `s = 20`,
`lateEntryRemainder 20 14 = 67662313`, has bit `20` *clear* — so the half-point
form `hlow_of_testBit_halfPoint` does not apply, and this is a row where `T4`
concludes `ρ 20 < 2 ^ 20`.  `hlow` is nevertheless free, from bit `19`, which
lies in the window `[2 * (20 - 14) + 1, 20] = [13, 20]`. -/
theorem hlow_twenty_fourteen_from_bit :
    lateCorrection 20 14 ≤ lateEntryRemainder 20 14 % 2 ^ (20 + 1) := by
  refine hlow_of_testBit (j := 19) (by norm_num) (by norm_num) (by norm_num) ?_
  rw [BitCorr.Concrete.lateEntryRemainder_twenty_fourteen]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

/-! ## 3. Deleting `hlow`: what `hhigh` alone buys

In the late zone every weight is `2 ^ (2 * s - e) + 4 ^ (s - e)` — a leading bit
plus a *single* correction, not a binary tail.  That is precisely what
`T1.residual_lt_of_declined` lacks at early ranks, and it is enough to make the
one-step interval induction close, at the price of carrying the correction as a
constant additive slack. -/

/-- **The late greedy under `hhigh` alone.**  No low-side condition of any kind:
running the descending greedy over the late weights from a capacity confined by
`hhigh` (with slack `K` at least one correction) ends below `2 ^ (s + 1) + K`.

The taken branch pays for the halving out of the leading bit and *gains*
`4 ^ (s - d)` of slack; the declined branch loses at most `4 ^ (s - d) ≤ K`.
Both branches therefore preserve the same constant `K`. -/
theorem lateGreedy_lt_of_high {s d K C : ℕ} (hd2 : 2 ≤ d) (hlate : 2 * s < 3 * d)
    (hK : 4 ^ (s - d) ≤ K) (hC : C < 2 ^ (2 * s - d + 1) + K) :
    integerGreedyRemainder (seamWeightsFrom s d) C < 2 ^ (s + 1) + K := by
  by_cases hds : d < s
  · have hw := truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank hd2 hds hlate
    have hexp : 2 * s - (d + 1) + 1 = 2 * s - d := by omega
    have hpow : (2 : ℕ) ^ (2 * s - d + 1) = 2 * 2 ^ (2 * s - d) := by rw [pow_succ]; ring
    have hK' : (4 : ℕ) ^ (s - (d + 1)) ≤ K :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hK
    have hFpos : 0 < (4 : ℕ) ^ (s - d) := by positivity
    rw [hpow] at hC
    rw [seamWeightsFrom_eq_cons hds, ErdosProblems.RemC6.integerGreedyRemainder_cons, hw]
    by_cases htake : 2 ^ (2 * s - d) + 4 ^ (s - d) ≤ C
    · rw [if_pos htake]
      exact lateGreedy_lt_of_high (d := d + 1) (by omega) (by omega) hK'
        (by rw [hexp]; omega)
    · rw [if_neg htake]
      exact lateGreedy_lt_of_high (d := d + 1) (by omega) (by omega) hK'
        (by rw [hexp]; omega)
  · rw [seamWeightsFrom_eq_nil (by omega), ErdosProblems.RemC6.integerGreedyRemainder_nil]
    have : (2 : ℕ) ^ (2 * s - d + 1) ≤ 2 ^ (s + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
termination_by s - d
decreasing_by all_goals omega

/-- **`ρ s` bounded with no low-side condition at all.**  Compare
`ThreeT4.seamRemainder_lt_two_pow_succ`, which reaches `2 ^ (s + 1)` but needs
`hlow` as well. -/
theorem seamRemainder_lt_two_pow_succ_add {s d : ℕ} (h2 : 2 ≤ d) (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1)) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 4 ^ (s - d) := by
  rw [ThreeT4.seamIntegerGreedyRemainder_eq_lateGreedy h2]
  exact lateGreedy_lt_of_high h2 hlate le_rfl (lt_of_lt_of_le hhigh (Nat.le_add_right _ _))

/-- The same, with the additive term folded away: in the late zone
`2 * (s - d) < d ≤ s`, so the slack is at most `2 ^ (s - 1)` and
`ρ s < 3 * 2 ^ s` follows from `hhigh` alone. -/
theorem seamRemainder_lt_of_high {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s)
    (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1)) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 2 ^ (s - 1) := by
  have hmain := seamRemainder_lt_two_pow_succ_add h2 hlate hhigh
  have hfour : (4 : ℕ) ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  have hmono : (2 : ℕ) ^ (2 * (s - d)) ≤ 2 ^ (s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem seamRemainder_lt_three_mul_two_pow_of_high {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s)
    (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1)) :
    seamIntegerGreedyRemainder s < 3 * 2 ^ s := by
  have hmain := seamRemainder_lt_of_high h2 hds hlate hhigh
  have h1 : (2 : ℕ) ^ (s - 1) ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2' : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  omega

/-! ### The additive term is real: `hhigh` alone cannot reach `2 ^ (s + 1)`

A capacity one below the leading late weight declines that rank and then takes
every remaining one, ending strictly above `2 ^ (s + 1)`.  So no strengthening of
the *argument* of §3 can remove the slack: a low-side condition is genuinely
needed for the exact constant, and this is the precise sense in which `hlow`
(or `bitCorrection`, §4) is not eliminable. -/

theorem seamWeightsFrom_seven_five : seamWeightsFrom 7 5 = [528, 260] := by
  rw [seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_nil (by norm_num)]
  simp only [truncatedMersenneWeight]
  decide +kernel

/-- **Sharpness.**  The capacity `527` satisfies `hhigh` at `(s, d) = (7, 5)`,
yet the late greedy leaves `267 > 2 ^ 8 = 2 ^ (s + 1)`.  It sits inside the slack
`4 ^ (s - d) = 16` that `lateGreedy_lt_of_high` allows, and it fails `hlow`
(`527 % 2 ^ 8 = 15 < 20`), as it must. -/
theorem sharpness_seven_five :
    (527 : ℕ) < 2 ^ (2 * 7 - 5 + 1) ∧
      integerGreedyRemainder (seamWeightsFrom 7 5) 527 = 267 ∧
        2 ^ (7 + 1) ≤ 267 ∧
        (267 : ℕ) < 2 ^ (7 + 1) + 4 ^ (7 - 5) ∧
        ¬ (lateCorrection 7 5 ≤ 527 % 2 ^ (7 + 1)) := by
  refine ⟨by norm_num, ?_, by norm_num, by norm_num, ?_⟩
  · rw [seamWeightsFrom_seven_five]; decide +kernel
  · rw [Seven.lateCorrection_seven_five]; decide +kernel

/-! ## 4. The right low-side condition: charge only the ranks that are taken

`lateCorrection s d` charges `4 ^ (s - e)` for every late rank `e ≥ d`.  The
greedy only pays for the ranks it *takes*, and by
`BitCorr.integerGreedyBits_seamWeightsFrom_eq_lateBitWord` those are exactly the
ranks whose bit `2 * s - e` of the entering capacity is set.  `bitCorrection`
charges for those alone. -/

/-- The correction actually incurred: `∑ 4 ^ (s - e)` over the late ranks
`e ∈ [d, s)` whose bit `2 * s - e` of `C` is set. -/
def bitCorrection (s C : ℕ) : ℕ → ℕ
  | d =>
      if h : d < s then
        (if Nat.testBit C (2 * s - d) then 4 ^ (s - d) else 0) + bitCorrection s C (d + 1)
      else 0
termination_by d => s - d
decreasing_by omega

theorem bitCorrection_eq_zero {s C d : ℕ} (h : s ≤ d) : bitCorrection s C d = 0 := by
  rw [bitCorrection]
  simp [Nat.not_lt.mpr h]

theorem bitCorrection_eq_cons {s C d : ℕ} (h : d < s) :
    bitCorrection s C d =
      (if Nat.testBit C (2 * s - d) then 4 ^ (s - d) else 0) + bitCorrection s C (d + 1) := by
  rw [bitCorrection]
  simp [h]

/-- **`hlow` implies the weaker condition.**  Charging only the taken ranks never
charges more. -/
theorem bitCorrection_le_lateCorrection (s C d : ℕ) :
    bitCorrection s C d ≤ lateCorrection s d := by
  by_cases hds : d < s
  · rw [bitCorrection_eq_cons hds, lateCorrection_eq_cons hds]
    have ih := bitCorrection_le_lateCorrection s C (d + 1)
    have hFpos : 0 < (4 : ℕ) ^ (s - d) := by positivity
    split <;> omega
  · rw [bitCorrection_eq_zero (by omega)]
    exact Nat.zero_le _
termination_by s - d
decreasing_by omega

/-- Two capacities agreeing on the tested bits carry the same correction. -/
theorem bitCorrection_congr {s C C' : ℕ} (d : ℕ)
    (hbits : ∀ e : ℕ, d ≤ e → e < s →
      Nat.testBit C' (2 * s - e) = Nat.testBit C (2 * s - e)) :
    bitCorrection s C' d = bitCorrection s C d := by
  by_cases hds : d < s
  · rw [bitCorrection_eq_cons hds, bitCorrection_eq_cons hds, hbits d le_rfl hds,
      bitCorrection_congr (s := s) (C := C) (C' := C') (d + 1)
        (fun e he hes => hbits e (by omega) hes)]
  · rw [bitCorrection_eq_zero (by omega), bitCorrection_eq_zero (by omega)]
termination_by s - d
decreasing_by omega

/-- **The exact late-greedy identity, on the weaker hypothesis.**  `T4` records

    ρ s = R % 2 ^ (s+1) − ∑_{e taken} 4 ^ (s-e)

as *measured, not proved* (it proves only the two-sided bound, and under `hlow`).
Here it is proved, and under `bitCorrection` rather than `lateCorrection`: the
late greedy consumes the whole high part of the capacity exactly, and what
survives is the low `s + 1` bits minus the corrections of the ranks it took.

The induction closes because a declined rank now costs nothing at all, so the
budget never over-charges. -/
theorem lateGreedy_eq_mod_sub_bitCorrection {s d C : ℕ}
    (hlate : 2 * s < 3 * d)
    (hhigh : C < 2 ^ (2 * s - d + 1))
    (hpay : bitCorrection s C d ≤ C % 2 ^ (s + 1)) :
    integerGreedyRemainder (seamWeightsFrom s d) C
      = C % 2 ^ (s + 1) - bitCorrection s C d := by
  by_cases hds : d < s
  · have hd2 : 2 ≤ d := by omega
    have hn : s + 1 ≤ 2 * s - d := by omega
    have hexp : 2 * s - (d + 1) + 1 = 2 * s - d := by omega
    have hpow : (2 : ℕ) ^ (2 * s - d + 1) = 2 ^ (2 * s - d) * 2 := by rw [pow_succ]
    have hw := truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank hd2 hds hlate
    have hmodmod : C % 2 ^ (2 * s - d) % 2 ^ (s + 1) = C % 2 ^ (s + 1) :=
      Nat.mod_mod_of_dvd C (pow_dvd_pow 2 hn)
    have hmodlt : C % 2 ^ (2 * s - d) < 2 ^ (2 * s - d) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hcons := bitCorrection_eq_cons (s := s) (C := C) (d := d) hds
    set F : ℕ := 4 ^ (s - d) with hFdef
    have hpos : 0 < F := by rw [hFdef]; positivity
    rw [seamWeightsFrom_eq_cons hds, ErdosProblems.RemC6.integerGreedyRemainder_cons, hw]
    by_cases htb : Nat.testBit C (2 * s - d) = true
    · rw [if_pos htb] at hcons
      have hFlow : F ≤ C % 2 ^ (s + 1) := by omega
      have hge2 : 2 ^ (2 * s - d) ≤ C := Nat.ge_two_pow_of_testBit htb
      have hsplit : C = 2 ^ (2 * s - d) + C % 2 ^ (2 * s - d) := by
        rw [Nat.mod_eq_sub_mod hge2, Nat.mod_eq_of_lt (by omega)]
        omega
      have h4m : F ≤ C % 2 ^ (2 * s - d) % 2 ^ (s + 1) := by rw [hmodmod]; exact hFlow
      have h4f : F ≤ C % 2 ^ (2 * s - d) := le_trans h4m (Nat.mod_le _ _)
      rw [if_pos (by omega)]
      have hCval : C - (2 ^ (2 * s - d) + F) = C % 2 ^ (2 * s - d) - F := by omega
      have hnewmod : (C % 2 ^ (2 * s - d) - F) % 2 ^ (s + 1) = C % 2 ^ (s + 1) - F := by
        rw [mod_sub_of_le_mod (Nat.two_pow_pos _) h4m, hmodmod]
      have hbits : ∀ e : ℕ, d + 1 ≤ e → e < s →
          Nat.testBit (C % 2 ^ (2 * s - d) - F) (2 * s - e) = Nat.testBit C (2 * s - e) := by
        intro e he hes
        have hj1 : s + 1 ≤ 2 * s - e := by omega
        have hj2 : 2 * s - e < 2 * s - d := by omega
        rw [testBit_sub_of_le_mod h4m hj1]
        simp [Nat.testBit_mod_two_pow, hj2]
      have hbc : bitCorrection s (C % 2 ^ (2 * s - d) - F) (d + 1)
          = bitCorrection s C (d + 1) := bitCorrection_congr (d + 1) hbits
      have hrec :=
        lateGreedy_eq_mod_sub_bitCorrection (s := s) (d := d + 1)
          (C := C % 2 ^ (2 * s - d) - F) (by omega)
          (by rw [hexp]; exact lt_of_le_of_lt (Nat.sub_le _ _) hmodlt)
          (by rw [hnewmod, hbc]; omega)
      rw [hnewmod, hbc] at hrec
      rw [hCval]
      omega
    · have htbf : Nat.testBit C (2 * s - d) = false := by simpa using htb
      rw [if_neg (by simp [htbf]), Nat.zero_add] at hcons
      have hClt : C < 2 ^ (2 * s - d) := by
        by_contra hcon
        rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) (by omega)] at htbf
        exact Bool.noConfusion htbf
      rw [if_neg (by omega), hcons]
      exact lateGreedy_eq_mod_sub_bitCorrection (s := s) (d := d + 1) (C := C) (by omega)
        (by rw [hexp]; omega) (by omega)
  · have hcle : C < 2 ^ (s + 1) :=
      lt_of_lt_of_le hhigh (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [seamWeightsFrom_eq_nil (by omega), ErdosProblems.RemC6.integerGreedyRemainder_nil,
      Nat.mod_eq_of_lt hcle, bitCorrection_eq_zero (by omega)]
    omega
termination_by s - d
decreasing_by all_goals omega

/-- The upper half of the trapping bound, which is what every downstream
consequence uses. -/
theorem lateGreedy_le_mod_of_bitCorrection {s d C : ℕ}
    (hlate : 2 * s < 3 * d)
    (hhigh : C < 2 ^ (2 * s - d + 1))
    (hpay : bitCorrection s C d ≤ C % 2 ^ (s + 1)) :
    integerGreedyRemainder (seamWeightsFrom s d) C ≤ C % 2 ^ (s + 1) := by
  rw [lateGreedy_eq_mod_sub_bitCorrection hlate hhigh hpay]
  exact Nat.sub_le _ _

/-- The lower half, in `T4`'s own shape: the surviving remainder is within the
*whole* budget of the low block, because the taken budget never exceeds it. -/
theorem mod_le_lateGreedy_add {s d C : ℕ}
    (hlate : 2 * s < 3 * d)
    (hhigh : C < 2 ^ (2 * s - d + 1))
    (hpay : bitCorrection s C d ≤ C % 2 ^ (s + 1)) :
    C % 2 ^ (s + 1) ≤ integerGreedyRemainder (seamWeightsFrom s d) C + lateCorrection s d := by
  have hid := lateGreedy_eq_mod_sub_bitCorrection hlate hhigh hpay
  have hle := bitCorrection_le_lateCorrection s C d
  omega

/-! ### `T4`'s conclusions, re-proved on the weaker hypothesis -/

/-- The weaker admissibility predicate: `hhigh` plus the *taken-rank* budget. -/
def BitAdmissible (s d : ℕ) : Prop :=
  2 ≤ d ∧ d ≤ s ∧ 2 * s < 3 * d ∧
    lateEntryRemainder s d < 2 ^ (2 * s - d + 1) ∧
    bitCorrection s (lateEntryRemainder s d) d ≤ lateEntryRemainder s d % 2 ^ (s + 1)

/-- `T4`'s `LateEntryAdmissible` implies the weaker predicate. -/
theorem bitAdmissible_of_lateEntryAdmissible {s d : ℕ}
    (h : ThreeT4.LateEntryAdmissible s d) : BitAdmissible s d :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    le_trans (bitCorrection_le_lateCorrection _ _ _) h.2.2.2.2⟩

theorem seamRemainder_le_mod {s d : ℕ} (h : BitAdmissible s d) :
    seamIntegerGreedyRemainder s ≤ lateEntryRemainder s d % 2 ^ (s + 1) := by
  obtain ⟨h2, -, hlate, hhigh, hpay⟩ := h
  rw [ThreeT4.seamIntegerGreedyRemainder_eq_lateGreedy h2]
  exact lateGreedy_le_mod_of_bitCorrection hlate hhigh hpay

/-- **`T4 §4` on the weaker hypothesis.** -/
theorem seamRemainder_lt_two_pow_succ' {s d : ℕ} (h : BitAdmissible s d) :
    seamIntegerGreedyRemainder s < 2 ^ (s + 1) :=
  lt_of_le_of_lt (seamRemainder_le_mod h) (Nat.mod_lt _ (Nat.two_pow_pos _))

/-- **`T4 §6`'s half-point criterion on the weaker hypothesis.** -/
theorem seamRemainder_lt_two_pow_of_testBit_false' {s d : ℕ} (h : BitAdmissible s d)
    (hbit : Nat.testBit (lateEntryRemainder s d) s = false) :
    seamIntegerGreedyRemainder s < 2 ^ s :=
  lt_of_le_of_lt (seamRemainder_le_mod h)
    (ThreeT4.mod_two_pow_succ_lt_of_testBit_false hbit)

/-- **The reduction, restated.**  If bit `s` of the entering remainder is clear at
arbitrarily large `BitAdmissible` rows then Erdős #257's `1/2` question is
answered positively.  This is `ThreeT4.half_mem_of_halfPointBitClearCofinally`
with the hypothesis weakened. -/
theorem half_mem_of_bitAdmissible_halfPointBitClearCofinally
    (h : ∀ N : ℕ, ∃ s d : ℕ, N ≤ s ∧ 5 ≤ s ∧ BitAdmissible s d ∧
      Nat.testBit (lateEntryRemainder s d) s = false) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  refine ErdosProblems.BitR2.half_mem_of_remainderReachesHalfPointCofinally ?_
  intro N
  obtain ⟨s, d, hNs, hs5, hadm, hbit⟩ := h N
  exact ⟨s, hNs, hs5, le_of_lt (seamRemainder_lt_two_pow_of_testBit_false' hadm hbit)⟩

/-! ### The repair certificate: row `7`, where `hlow` failed -/

namespace Seven

/-- The taken-rank budget at row `7`, rank `5`: rank `5` is declined (bit `9` of
`263` is clear) and rank `6` is taken (bit `8` is set), so only `4 ^ 1 = 4` is
charged, against `lateCorrection 7 5 = 20`. -/
theorem bitCorrection_seven_five : bitCorrection 7 263 5 = 4 := by
  rw [bitCorrection_eq_cons (by norm_num), bitCorrection_eq_cons (by norm_num),
    bitCorrection_eq_zero (by norm_num)]
  norm_num only
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

/-- **The repair.**  The weaker condition holds at the first late rank of row
`7`, where `hlow` fails. -/
theorem bitLow_seven_five :
    bitCorrection 7 (lateEntryRemainder 7 5) 5 ≤ lateEntryRemainder 7 5 % 2 ^ (7 + 1) := by
  rw [lateEntryRemainder_seven_five, bitCorrection_seven_five]
  decide +kernel

theorem bitAdmissible_seven_five : BitAdmissible 7 5 :=
  ⟨by norm_num, by norm_num, by norm_num, hhigh_seven_five, bitLow_seven_five⟩

theorem testBit_seven_halfPoint : Nat.testBit (lateEntryRemainder 7 5) 7 = false := by
  rw [lateEntryRemainder_seven_five]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

/-- **The route is repaired.**  `ρ 7 < 2 ^ 7` now follows from one clear bit of
the entering remainder at the *first* late rank — the rank at which `T4`'s
hypothesis is false — through `bitCorrection` instead of `lateCorrection`. -/
theorem seamRemainder_seven_lt : seamIntegerGreedyRemainder 7 < 2 ^ 7 :=
  seamRemainder_lt_two_pow_of_testBit_false' bitAdmissible_seven_five testBit_seven_halfPoint

/-- The three conditions at `(7, 5)` side by side: `hhigh` holds, `hlow` fails,
the taken-rank budget holds. -/
theorem separation_at_seven_five :
    lateEntryRemainder 7 5 < 2 ^ (2 * 7 - 5 + 1) ∧
      ¬ (lateCorrection 7 5 ≤ lateEntryRemainder 7 5 % 2 ^ (7 + 1)) ∧
      bitCorrection 7 (lateEntryRemainder 7 5) 5 ≤ lateEntryRemainder 7 5 % 2 ^ (7 + 1) :=
  ⟨hhigh_seven_five, not_hlow_seven_five, bitLow_seven_five⟩

end Seven

/-- **The exact identity for `ρ s`.**  `T4` records this as measured, not proved. -/
theorem seamRemainder_eq_mod_sub {s d : ℕ} (h : BitAdmissible s d) :
    seamIntegerGreedyRemainder s =
      lateEntryRemainder s d % 2 ^ (s + 1)
        - bitCorrection s (lateEntryRemainder s d) d := by
  obtain ⟨h2, -, hlate, hhigh, hpay⟩ := h
  rw [ThreeT4.seamIntegerGreedyRemainder_eq_lateGreedy h2]
  exact lateGreedy_eq_mod_sub_bitCorrection hlate hhigh hpay

/-- `T4`'s full two-sided bound `seamRemainder_bounds`, on the weaker hypothesis. -/
theorem seamRemainder_bounds' {s d : ℕ} (h : BitAdmissible s d) :
    seamIntegerGreedyRemainder s ≤ lateEntryRemainder s d % 2 ^ (s + 1) ∧
      lateEntryRemainder s d % 2 ^ (s + 1)
        ≤ seamIntegerGreedyRemainder s + lateCorrection s d := by
  refine ⟨seamRemainder_le_mod h, ?_⟩
  obtain ⟨h2, -, hlate, hhigh, hpay⟩ := h
  rw [ThreeT4.seamIntegerGreedyRemainder_eq_lateGreedy h2]
  exact mod_le_lateGreedy_add hlate hhigh hpay

/-- `T4`'s partial converse, on the weaker hypothesis. -/
theorem two_pow_le_seamRemainder_add_of_testBit_true' {s d : ℕ} (h : BitAdmissible s d)
    (hbit : Nat.testBit (lateEntryRemainder s d) s = true) :
    2 ^ s ≤ seamIntegerGreedyRemainder s + lateCorrection s d :=
  le_trans (ThreeT4.two_pow_le_mod_two_pow_succ_of_testBit_true hbit)
    (seamRemainder_bounds' h).2

/-! ## 5. `hhigh` is `C6`'s residual ceiling, verbatim

The point of this section is to make the verdict of the header precise rather
than rhetorical.  `lateEntryRemainder s d` is the residual after the ranks
`2, …, d - 1` have been offered — that is `T1.seamResidualUpto s (d - 1)` — and
`2 ^ (2 * s - d + 1) = 2 ^ (2 * s - (d - 1))`.  So `hhigh` at rank `d` **is**
`T1.ResidualInvariant` evaluated at the single rank `d - 1`, the invariant `T1`
refutes in its `∀ d` form and shows no rank-indexed interval induction can
produce (`T1.IntervalCeiling.two_pow_lt`).  Nothing in this file weakens it. -/

theorem seamWeightsFrom_getElem? {s d k : ℕ} (h : d + k < s) :
    (seamWeightsFrom s d)[k]? = some (truncatedMersenneWeight s (d + k)) := by
  induction k generalizing d with
  | zero => rw [seamWeightsFrom_eq_cons (by omega)]; simp
  | succ k ih =>
      rw [seamWeightsFrom_eq_cons (by omega), List.getElem?_cons_succ,
        ih (d := d + 1) (by omega)]
      congr 2
      omega

theorem lateEntryRemainder_eq_integerGreedy (s d : ℕ) :
    lateEntryRemainder s d =
      integerGreedyRemainder ((seamWeights s).take (d - 2)) (seamSubsetTarget s) := rfl

theorem integerGreedy_take_eq_seamResidual (s : ℕ) :
    ∀ k, k + 2 ≤ s →
      integerGreedyRemainder ((seamWeights s).take k) (seamSubsetTarget s)
        = Three.T1.seamResidual s k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hget : (seamWeights s)[k]? = some (truncatedMersenneWeight s (k + 2)) := by
        show (seamWeightsFrom s 2)[k]? = _
        rw [seamWeightsFrom_getElem? (by omega), show 2 + k = k + 2 by omega]
      rw [List.take_add_one, hget, Option.toList_some,
        ErdosProblems.RemC6.integerGreedyRemainder_append, ih (by omega),
        ErdosProblems.RemC6.integerGreedyRemainder_cons,
        ErdosProblems.RemC6.integerGreedyRemainder_nil]
      show _ = if truncatedMersenneWeight s (k + 2) ≤ Three.T1.seamResidual s k then _ else _
      split <;> rfl

/-- **The entering remainder is `T1`'s rank-indexed residual.** -/
theorem lateEntryRemainder_eq_seamResidualUpto {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s) :
    lateEntryRemainder s d = Three.T1.seamResidualUpto s (d - 1) := by
  rw [lateEntryRemainder_eq_integerGreedy, integerGreedy_take_eq_seamResidual s (d - 2) (by omega)]
  show _ = Three.T1.seamResidual s (d - 1 - 1)
  congr 1

/-- **`hhigh` is `C6`'s ceiling at rank `d - 1`.**  Not an analogue — the same
statement.  Together with `T1.not_residualInvariant` and
`T1.IntervalCeiling.two_pow_lt` this is the verdict: `hhigh` is the obstruction,
and it is one that `T1` has already shown is out of reach of the induction that
`C6` and this whole line of attack keep trying. -/
theorem hhigh_iff_seamResidualUpto {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s) :
    lateEntryRemainder s d < 2 ^ (2 * s - d + 1) ↔
      Three.T1.seamResidualUpto s (d - 1) < 2 ^ (2 * s - (d - 1)) := by
  rw [lateEntryRemainder_eq_seamResidualUpto h2 hds,
    show 2 * s - d + 1 = 2 * s - (d - 1) by omega]

/-- **The tangency self-corrects.**  `T1.not_residualInvariant` refutes `C6`'s
ceiling at `(s, d) = (13, 7)`, where the residual `524419` exceeds `2 ^ 19`.  The
first late rank of row `13` is `9`, and `hhigh` there is the ceiling at rank `8`:
rank `8` is taken, the residual drops to `261247`, and `261247 < 2 ^ 18`.  So
`T1`'s counterexample does **not** refute `hhigh`, which is why the scan finds no
failure of `hhigh` anywhere in `[6, 2200]`. -/
theorem hhigh_thirteen_nine : lateEntryRemainder 13 9 < 2 ^ (2 * 13 - 9 + 1) := by
  rw [lateEntryRemainder_eq_seamResidualUpto (by norm_num) (by norm_num)]
  norm_num [Three.T1.seamResidualUpto, Three.T1.seamResidual, truncatedMersenneWeight,
    seamSubsetTarget]

/-- The residual `T1` refutes the ceiling with, one rank later.  `524419` at rank
`7` becomes `261247` at rank `8`, and `2 ^ 18 = 262144`. -/
theorem seamResidualUpto_thirteen_eight : Three.T1.seamResidualUpto 13 8 = 261247 := by
  norm_num [Three.T1.seamResidualUpto, Three.T1.seamResidual, truncatedMersenneWeight,
    seamSubsetTarget]

/-! ### Anti-vacuity at the rows `T4` certifies -/

theorem bitAdmissible_fourteen : BitAdmissible 14 10 :=
  bitAdmissible_of_lateEntryAdmissible ThreeT4.Concrete.admissible_fourteen

theorem bitAdmissible_twenty : BitAdmissible 20 14 :=
  bitAdmissible_of_lateEntryAdmissible ThreeT4.Concrete.admissible_twenty

theorem seamRemainder_twenty_lt' : seamIntegerGreedyRemainder 20 < 2 ^ 20 :=
  seamRemainder_lt_two_pow_of_testBit_false' bitAdmissible_twenty
    ThreeT4.Concrete.testBit_twenty_halfPoint

/-- **Anti-vacuity for §3.**  `lateGreedy_lt_of_high`'s hypothesis is not empty:
`hhigh` holds at row `20`, rank `14`, so the unconditional-in-`hlow` bound fires
on the corpus's own certified object. -/
theorem seamRemainder_twenty_lt_of_high :
    seamIntegerGreedyRemainder 20 < 2 ^ (20 + 1) + 4 ^ (20 - 14) :=
  seamRemainder_lt_two_pow_succ_add (by norm_num) (by norm_num)
    BitCorr.Concrete.actual_hypotheses_hold.1

/-- **Anti-vacuity for §3 at the refuting row.**  Even at row `7`, where `hlow`
fails outright, `hhigh` alone gives a bound — `ρ 7 < 2 ^ 8 + 16`. -/
theorem seamRemainder_seven_lt_of_high :
    seamIntegerGreedyRemainder 7 < 2 ^ (7 + 1) + 4 ^ (7 - 5) :=
  seamRemainder_lt_two_pow_succ_add (by norm_num) (by norm_num) Seven.hhigh_seven_five

end ErdosProblems.DeclD4
