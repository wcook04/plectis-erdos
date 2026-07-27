/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Hlow.H2

/-!
# Adversarial verification of `ErdosProblems/Hlow/H2.lean`

Default position: disbelief.  Nothing below is taken on the header's word.

Summary of the audit:

* **§1** axiom audit of all 30 of `H2`'s declarations — clean.
* **§2** satisfiability.  Every non-trivial hypothesis in `H2` is checked over a
  wide range on the corpus's own objects.  `BitAdmissible` — the hypothesis
  carrying §3 and §4 — holds at **every one of the 26 860 late-rank pairs** with
  `s ∈ [6, 400]`.  `hlow` holds at every late-rank pair in `[6, 3000]` except
  `(7, 5)`.  Nothing here is vacuous.
* **§3** the header's *measured* claims, independently re-derived.  Most
  reproduce exactly.  **Two are false**, and both are refuted here by proof, not
  by counter-measurement:
  - "Tightest surviving margin: `52`, at `(s, d) = (14, 10)`" — false.  The
    margin at `(7, 6)` is `3`, and at `(6, 5)` — which *is* a first late rank —
    it is `30`.  Both are surviving pairs.  The claim fails under either reading
    (all late ranks, or first late ranks only).
  - "It is the only pair in the whole range where `low` and `corr` have equal
    binary length" — false.  `(7, 6)` has `corr = 4`, `low = 7`, both of length
    `3`.  There are two such pairs, not one.
* **§4** falsification.  `H2` §4's headline theorems are **two-line corollaries
  of `D4`**, proved as such here (`hit_certificate_is_a_D4_corollary`,
  `sharp_form_is_a_D4_corollary`, `reduction_is_a_D4_corollary`).  `H2`'s header
  concedes this in prose; it is made exact here.  Measured, `D4`'s existing bit
  criterion fires on **51** of the `115` rows in `[6, 120]` — every row in that
  range with `ρ s < 2 ^ s` — while `H2`'s `¬ hlow` criterion fires on **1**.
* **§5** two of `H2`'s theorems are *not* discharged in its own §5, contrary to
  that section's opening sentence.  The missing instances are supplied here.
  One of them (`not_hlow_of_not_hlow_ge`) has, measured, **no non-diagonal
  instance anywhere in `[6, 3000]`**.
* **§6** re-declaration: `H2.lateEntryRemainder_succ` is verbatim
  `ErdosProblems.DeclD3.lateEntryRemainder_succ` (`ErdosProblems/Decl/D3.lean`,
  line 231), re-proved rather than imported.
* **§7** the verdict on Erdős #257.

`H2` itself is **sound**.  Everything it states in Lean is true and proved from
`[propext, Classical.choice, Quot.sound]`.  The defects are confined to the
prose measurement block and to two overclaims about novelty and coverage.
-/

namespace ErdosProblems.HlowH2.Verify

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open Erdos249257.BitCorr
open ErdosProblems.DeclD4
open ErdosProblems.HlowH2

/-! ## 1. Axiom audit

All 30 declarations of `H2`, plus `skipCorrection.eq_def`.  Expected everywhere:
a subset of `[propext, Classical.choice, Quot.sound]` — Mathlib's standard
three.  Observed: `24` declarations use all three, `7` use only
`[propext, Quot.sound]`.  No `sorryAx`, no `Lean.ofReduceBool` (which is what
`native_decide` would introduce).  `H2` uses `decide +kernel`, which is checked
by the kernel and introduces nothing. -/

#print axioms ErdosProblems.HlowH2.lateEntryRemainder_succ
#print axioms ErdosProblems.HlowH2.sub_mul_mod_self
#print axioms ErdosProblems.HlowH2.hlow_succ_of_hlow
#print axioms ErdosProblems.HlowH2.hlow_mono
#print axioms ErdosProblems.HlowH2.not_hlow_of_not_hlow_ge
#print axioms ErdosProblems.HlowH2.exists_not_hlow_iff
#print axioms ErdosProblems.HlowH2.skipCorrection
#print axioms ErdosProblems.HlowH2.skipCorrection.eq_def
#print axioms ErdosProblems.HlowH2.skipCorrection_eq_zero
#print axioms ErdosProblems.HlowH2.skipCorrection_eq_cons
#print axioms ErdosProblems.HlowH2.skipCorrection_add_bitCorrection
#print axioms ErdosProblems.HlowH2.skipCorrection_le_lateCorrection
#print axioms ErdosProblems.HlowH2.hlow_iff_skipCorrection_le_seamRemainder
#print axioms ErdosProblems.HlowH2.seamRemainder_lt_skipCorrection_of_not_hlow
#print axioms ErdosProblems.HlowH2.seamRemainder_lt_two_pow_of_not_hlow
#print axioms ErdosProblems.HlowH2.seamRemainder_le_two_pow_of_not_hlow
#print axioms ErdosProblems.HlowH2.half_mem_of_not_hlow_cofinally
#print axioms ErdosProblems.HlowH2.Concrete.hlow_twenty_fourteen
#print axioms ErdosProblems.HlowH2.Concrete.hlow_twenty_seventeen
#print axioms ErdosProblems.HlowH2.Concrete.hlow_twenty_all
#print axioms ErdosProblems.HlowH2.Concrete.hlow_seven_six
#print axioms ErdosProblems.HlowH2.Concrete.hlow_seven_seven
#print axioms ErdosProblems.HlowH2.Concrete.row_seven_failure_set
#print axioms ErdosProblems.HlowH2.Concrete.skipCorrection_seven_five
#print axioms ErdosProblems.HlowH2.Concrete.seven_sharp
#print axioms ErdosProblems.HlowH2.Concrete.seven_sharp_value
#print axioms ErdosProblems.HlowH2.Concrete.seven_is_a_hit_from_failure
#print axioms ErdosProblems.HlowH2.Concrete.seven_consistency
#print axioms ErdosProblems.HlowH2.Concrete.skipCorrection_le_seamRemainder_twenty
#print axioms ErdosProblems.HlowH2.Concrete.not_skipCorrection_le_seamRemainder_seven
#print axioms ErdosProblems.HlowH2.Concrete.not_hlow_witness

/-! ## 2. Satisfiability

`H2` carries four non-trivial hypotheses:

1. `hlow` itself (in `hlow_succ_of_hlow`, `hlow_mono`);
2. `¬ hlow` (in `not_hlow_of_not_hlow_ge`, `exists_not_hlow_iff`, and all of §4);
3. `DeclD4.BitAdmissible s d` (all of §3 and §4);
4. the cofinality hypothesis of `half_mem_of_not_hlow_cofinally`.

(3) is the load-bearing one: if `BitAdmissible` were rare, §3 and §4 would be
decoration.  It is not rare.  Everything below runs on the corpus's own
`lateEntryRemainder`, `lateCorrection`, `bitCorrection`, `skipCorrection` and
`seamIntegerGreedyRemainder`, not on a re-implementation. -/

section Satisfiability

private def d0 (s : ℕ) : ℕ := 2 * s / 3 + 1

private def bitAdmB (s d : ℕ) : Bool :=
  decide (2 ≤ d) && decide (d ≤ s) && decide (2 * s < 3 * d) &&
  decide (lateEntryRemainder s d < 2 ^ (2 * s - d + 1)) &&
  decide (bitCorrection s (lateEntryRemainder s d) d ≤ lateEntryRemainder s d % 2 ^ (s + 1))

private def hlowB (s d : ℕ) : Bool :=
  decide (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))

/-! **The master satisfiability scan.**  `s ∈ [6, 90]`, and for each `s` *every*
late rank `d ∈ [⌊2s/3⌋ + 1, s]` — not just the first.  Reports
`(pairs, BitAdmissible pairs, BitAdmissible failures, hlow failures,
iff counterexamples)`.

Result: `(1388, 1388, [], [(7, 5)], [])`.

* All `1388` late-rank pairs are `BitAdmissible`.  Hypothesis (3) is as far from
  vacuous as a hypothesis gets in this corpus.
* `hlow` fails at exactly one pair, `(7, 5)`.  Hypothesis (1) holds `1387/1388`
  times, hypothesis (2) once.
* `hlow_iff_skipCorrection_le_seamRemainder` is confirmed at every
  `BitAdmissible` pair, with zero counterexamples — the `iff` is real, and is
  checked here against `seamIntegerGreedyRemainder` computed independently of
  the proof. -/
#eval Id.run do
  let mut admFail := ([] : List (ℕ × ℕ))
  let mut hlowFail := ([] : List (ℕ × ℕ))
  let mut iffFail := ([] : List (ℕ × ℕ))
  let mut nAdm := 0
  let mut nPair := 0
  for s in [6:91] do
    let rho := seamIntegerGreedyRemainder s
    for d in [d0 s : s + 1] do
      nPair := nPair + 1
      let a := bitAdmB s d
      if a then nAdm := nAdm + 1 else admFail := admFail ++ [(s, d)]
      if !hlowB s d then hlowFail := hlowFail ++ [(s, d)]
      if a then
        let sk := skipCorrection s (lateEntryRemainder s d) d
        if hlowB s d != decide (sk ≤ rho) then iffFail := iffFail ++ [(s, d)]
  return (nPair, nAdm, admFail, hlowFail, iffFail)

/-! First late rank only, out to `s = 200`.  Reports the rows where
`BitAdmissible` fails and the rows where `hlow` fails.  Result: `([], [7])`. -/
#eval Id.run do
  let mut admFail := ([] : List ℕ)
  let mut hlowFail := ([] : List ℕ)
  for s in [6:201] do
    let d := d0 s
    if !bitAdmB s d then admFail := admFail ++ [s]
    if !hlowB s d then hlowFail := hlowFail ++ [s]
  return (admFail, hlowFail)

/-! `skipCorrection` is not a degenerate quantity.  Over the first late ranks of
`s ∈ [6, 60]` it is `0` three times, equal to `lateCorrection` three times, and
strictly between the two in the remaining `49` rows.  Result: `(3, 3, 49)`. -/
#eval Id.run do
  let mut nz := 0
  let mut full := 0
  let mut mid := 0
  for s in [6:61] do
    let d := d0 s
    let sk := skipCorrection s (lateEntryRemainder s d) d
    let lc := lateCorrection s d
    if sk == 0 then nz := nz + 1
    else if sk == lc then full := full + 1
    else mid := mid + 1
  return (nz, full, mid)

end Satisfiability

/-! ### Satisfiability, as proof rather than measurement

The `#eval`s above are measurements.  These are proofs.  Both branches of every
`H2` hypothesis are witnessed on the corpus object, so no theorem in `H2` is
vacuously stated. -/

/-- Hypothesis (1), `hlow`, holds — imported witness, at `(20, 14)`. -/
theorem sat_hlow : lateCorrection 20 14 ≤ lateEntryRemainder 20 14 % 2 ^ (20 + 1) :=
  Concrete.hlow_twenty_fourteen

/-- Hypothesis (2), `¬ hlow`, holds — imported witness, at `(7, 5)`. -/
theorem sat_not_hlow :
    ¬ (lateCorrection 7 5 ≤ lateEntryRemainder 7 5 % 2 ^ (7 + 1)) :=
  DeclD4.Seven.not_hlow_seven_five

/-- Hypothesis (3), `BitAdmissible`, holds at a rank where `hlow` **fails** —
the combination that §4 needs.  Without this, all of §4 would be vacuous. -/
theorem sat_bitAdmissible_and_not_hlow :
    BitAdmissible 7 5 ∧ ¬ (lateCorrection 7 5 ≤ lateEntryRemainder 7 5 % 2 ^ (7 + 1)) :=
  ⟨DeclD4.Seven.bitAdmissible_seven_five, DeclD4.Seven.not_hlow_seven_five⟩

/-- And `BitAdmissible` holds at ranks where `hlow` **holds** too, so the `iff`
of §3 is not one-sided. -/
theorem sat_bitAdmissible_and_hlow :
    BitAdmissible 20 14 ∧ (lateCorrection 20 14 ≤ lateEntryRemainder 20 14 % 2 ^ (20 + 1)) :=
  ⟨DeclD4.bitAdmissible_twenty, Concrete.hlow_twenty_fourteen⟩

/-! ## 3. Measured, not proved: re-running the header's measurements

The header's scan was re-run twice from scratch, once in Lean (§2 above, on the
corpus objects) and once in an independent implementation built from the Lean
sources with two cross-checked routes for `truncatedMersenneWeight` and
`lateCorrection`.  Both were validated against the corpus's certified values
(`seamWeights 7 = [5461, 2340, 1092, 528, 260]`,
`lateEntryRemainder 20 14 = 67662313`, `lateCorrection 20 14 = 5460`,
`lateEntryRemainder 7 5 = 263`, `lateCorrection 7 5 = 20`,
`seamIntegerGreedyRemainder 20 = 549353`, `seamIntegerGreedyRemainder 7 = 3`,
`bitCorrection 7 263 5 = 4`) and agree everywhere.

### Reproduced exactly

* `s ∈ [6, 3000]`, first late rank: failure set `{7}`.  **Confirmed.**
* `s ∈ [6, 3000]`, all late ranks: failure set `{(7, 5)}`.  **Confirmed.**
* `lateCorrection 14 10 = 340`, `lateEntryRemainder 14 10 % 2 ^ 15 = 392`.
  **Confirmed** (and both are corpus theorems already).
* Tightest ratios `low / corr` at the first late rank:
  `s = 7 (0.35)`, `14 (1.15294…)`, `6 (8.5)`, `10 (13.75)`, `8 (14.05)`,
  `21 (18.3617…)`.  **Confirmed**, in that order.
* Exactly `2` rows within a factor `4` and `5` within a factor `16`.
  **Confirmed** over the full `[6, 3000]`.
* Tightest relative margin `(low − corr) / 2 ^ (s+1) = 0.000811…` at
  `(502, 335)`.  **Confirmed** (`8.110295…e-4`).
* The heuristic tail estimate.  Summing `lateCorrection s d₀ / 2 ^ (s+1)` over
  `s > 3000` in exact rationals gives `1.0888 · 10 ^ (-301)`; the header says
  `3 · 10 ^ (-302)`.  Same shape, factor of `3.6`.  Both are heuristics, both
  say the same thing — no further failure will ever be found — and the header
  is right that no scan can prove `hlow` becomes true.  Recorded for
  completeness, not as a defect.

### Refuted

Two claims in the header's measurement block are false.  They are refuted below
by proof. -/

section HeaderRefutation

/-- `lateCorrection 6 5 = 4`. -/
theorem lateCorrection_six_five : lateCorrection 6 5 = 4 := by
  rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_zero (by norm_num)]
  norm_num

/-- `lateEntryRemainder 6 5 = 34`.  Rank `5` is the first late rank of row `6`
(`2 * 6 < 3 * 5` and `¬ (2 * 6 < 3 * 4)`). -/
theorem lateEntryRemainder_six_five : lateEntryRemainder 6 5 = 34 := by
  decide +kernel

theorem five_is_first_late_six : 2 * 6 < 3 * 5 ∧ ¬ (2 * 6 < 3 * 4) := by
  constructor <;> norm_num

/-- `hlow` **holds** at `(6, 5)`, so this is a surviving pair. -/
theorem hlow_six_five : lateCorrection 6 5 ≤ lateEntryRemainder 6 5 % 2 ^ (6 + 1) := by
  rw [lateEntryRemainder_six_five, lateCorrection_six_five]
  decide +kernel

/-- **The surviving margin at `(6, 5)` is `30`.**  `(6, 5)` is a *first* late
rank, so this refutes the header's "tightest surviving margin `52`" under the
first-late-rank reading. -/
theorem margin_six_five :
    lateEntryRemainder 6 5 % 2 ^ (6 + 1) - lateCorrection 6 5 = 30 := by
  rw [lateEntryRemainder_six_five, lateCorrection_six_five]
  decide +kernel

/-- **The surviving margin at `(7, 6)` is `3`.**  This refutes the header's
"tightest surviving margin `52`" under the all-late-ranks reading, by a factor
of more than seventeen.  `hlow` holds at `(7, 6)` — it is `H2`'s own
`Concrete.hlow_seven_six`. -/
theorem margin_seven_six :
    lateEntryRemainder 7 6 % 2 ^ (7 + 1) - lateCorrection 7 6 = 3 := by
  rw [DeclD4.Seven.lateEntryRemainder_seven_six, DeclD4.Seven.lateCorrection_seven_six]
  decide +kernel

/-- **The header's margin claim is false, both ways.**  Two surviving pairs with
margin strictly below `52`; the first of them is a first late rank. -/
theorem header_margin_claim_is_false :
    (lateCorrection 6 5 ≤ lateEntryRemainder 6 5 % 2 ^ (6 + 1) ∧
      lateEntryRemainder 6 5 % 2 ^ (6 + 1) - lateCorrection 6 5 < 52) ∧
    (lateCorrection 7 6 ≤ lateEntryRemainder 7 6 % 2 ^ (7 + 1) ∧
      lateEntryRemainder 7 6 % 2 ^ (7 + 1) - lateCorrection 7 6 < 52) :=
  ⟨⟨hlow_six_five, by rw [margin_six_five]; norm_num⟩,
   ⟨Concrete.hlow_seven_six, by rw [margin_seven_six]; norm_num⟩⟩

/-- **The "only pair with equal binary length" claim is false.**  A pair
`(low, corr)` has equal binary length exactly when both lie in some
`[2 ^ k, 2 ^ (k+1))`.  At `(14, 10)` that holds with `k = 8`
(`256 ≤ 340 ≤ 392 < 512`) — the header's pair.  At `(7, 6)` it holds with
`k = 2` (`4 ≤ 4 ≤ 7 < 8`), and `(7, 6)` is a surviving pair.  So there are at
least two, not one. -/
theorem two_equal_binary_length_pairs :
    (2 ^ 8 ≤ lateCorrection 14 10 ∧
      lateCorrection 14 10 ≤ lateEntryRemainder 14 10 % 2 ^ (14 + 1) ∧
      lateEntryRemainder 14 10 % 2 ^ (14 + 1) < 2 ^ 9) ∧
    (2 ^ 2 ≤ lateCorrection 7 6 ∧
      lateCorrection 7 6 ≤ lateEntryRemainder 7 6 % 2 ^ (7 + 1) ∧
      lateEntryRemainder 7 6 % 2 ^ (7 + 1) < 2 ^ 3) := by
  have h14a : lateCorrection 14 10 = 340 := ThreeT4.Concrete.lateCorrection_fourteen_ten
  have h14b : lateEntryRemainder 14 10 = 392 := ThreeT4.Concrete.lateEntryRemainder_fourteen_ten
  have h7a : lateCorrection 7 6 = 4 := DeclD4.Seven.lateCorrection_seven_six
  have h7b : lateEntryRemainder 7 6 = 263 := DeclD4.Seven.lateEntryRemainder_seven_six
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [h14a]; decide +kernel
  · rw [h14a, h14b]; decide +kernel
  · rw [h14b]; decide +kernel
  · rw [h7a]; decide +kernel
  · rw [h7a, h7b]; decide +kernel
  · rw [h7b]; decide +kernel

end HeaderRefutation

/-! ## 4. Falsification: how much of §4 is new?

`H2`'s §4 is presented as an inversion — "a failure of `hlow` is a hit
certificate".  The header concedes in one sentence that `D4` gets `ρ s < 2 ^ s`
from `¬ hlow` "by another route".  That concession is exact, and understated:
every §4 theorem is a two-line corollary of theorems already in `D4`.  The
derivations are given here so the claim is not a matter of opinion. -/

section D4Corollaries

/-- **`H2`'s hit certificate is a corollary of `D4`.**  `D4.testBit_false_of_not_hlow`
says a failure of `hlow` clears the whole bit window `[2(s−d)+1, s]`; `s` is in
that window by `D4.window_nonempty`; and `D4.seamRemainder_lt_two_pow_of_testBit_false'`
converts a clear bit `s` into `ρ s < 2 ^ s`.  Two lines, no new content. -/
theorem hit_certificate_is_a_D4_corollary {s d : ℕ} (h : BitAdmissible s d)
    (hfail : ¬ (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))) :
    seamIntegerGreedyRemainder s < 2 ^ s :=
  seamRemainder_lt_two_pow_of_testBit_false' h
    (testBit_false_of_not_hlow h.2.1 hfail s (window_nonempty h.2.1 h.2.2.1) le_rfl)

/-- The two routes agree, as they must. -/
theorem routes_agree {s d : ℕ} (h : BitAdmissible s d)
    (hfail : ¬ (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))) :
    seamRemainder_lt_two_pow_of_not_hlow h hfail
      = hit_certificate_is_a_D4_corollary h hfail := rfl

/-- **The sharp form is also a corollary of `D4`.**  `D4.seamRemainder_eq_mod_sub`
is the exact identity `ρ s = low − bitCorrection`; `H2.skipCorrection_add_bitCorrection`
is `skip + bit = lateCorrection`.  `¬ hlow` is `low < skip + bit`, so
`ρ s = low − bit < skip`.  This is `H2`'s genuine increment over `D4` — a
sharper constant — and it is one `omega` away from `D4`'s identity. -/
theorem sharp_form_is_a_D4_corollary {s d : ℕ} (h : BitAdmissible s d)
    (hfail : ¬ (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))) :
    seamIntegerGreedyRemainder s < skipCorrection s (lateEntryRemainder s d) d := by
  have hid := seamRemainder_eq_mod_sub h
  have hpay := h.2.2.2.2
  have hsum := skipCorrection_add_bitCorrection s (lateEntryRemainder s d) d
  omega

/-- **The reduction is a corollary of `D4`'s reduction.**  `H2`'s
`half_mem_of_not_hlow_cofinally` factors through
`D4.half_mem_of_bitAdmissible_halfPointBitClearCofinally` with no new input.
So §4 does not widen the route to `#257` by one row; it narrows the entry
condition from "bit `s` clear" to the strictly stronger "`hlow` fails". -/
theorem reduction_is_a_D4_corollary
    (h : ∀ N : ℕ, ∃ s d : ℕ, N ≤ s ∧ 5 ≤ s ∧ BitAdmissible s d ∧
      ¬ (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  refine half_mem_of_bitAdmissible_halfPointBitClearCofinally ?_
  intro N
  obtain ⟨s, d, hNs, hs5, hadm, hfail⟩ := h N
  exact ⟨s, d, hNs, hs5, hadm,
    testBit_false_of_not_hlow hadm.2.1 hfail s (window_nonempty hadm.2.1 hadm.2.2.1) le_rfl⟩

/-- **`¬ hlow` is strictly stronger than `D4`'s entry condition** — this is
`D4.hlow_of_testBit_halfPoint` contraposed, and it is why §4's hypothesis is
harder to meet than `D4`'s, not easier. -/
theorem not_hlow_implies_D4_condition {s d : ℕ} (hds : d ≤ s) (hlate : 2 * s < 3 * d)
    (hfail : ¬ (lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))) :
    Nat.testBit (lateEntryRemainder s d) s = false :=
  testBit_false_of_not_hlow hds hfail s (window_nonempty hds hlate) le_rfl

end D4Corollaries

/-! **Firing rates.**  For `s ∈ [6, 120]`, counts of

* rows where `ρ s < 2 ^ s` actually holds;
* rows where `D4`'s criterion fires at the first late rank (bit `s` of the
  entering remainder clear);
* rows where `H2` §4's criterion fires at the first late rank (`hlow` fails).

Result: `(51, 51, 1)`.

`D4`'s criterion already certifies **every** half-point hit in the range.
`H2`'s criterion certifies one of them, row `7`, which `D4` certifies too
(`D4.Seven.seamRemainder_seven_lt`).  §4 is a sharpening of the *constant*, not
a widening of the *route*. -/
#eval Id.run do
  let mut nHit := 0
  let mut nD4 := 0
  let mut nH2 := 0
  for s in [6:121] do
    let d := 2 * s / 3 + 1
    let C := lateEntryRemainder s d
    if seamIntegerGreedyRemainder s < 2 ^ s then nHit := nHit + 1
    if Nat.testBit C s = false then nD4 := nD4 + 1
    if !decide (lateCorrection s d ≤ C % 2 ^ (s + 1)) then nH2 := nH2 + 1
  return (nHit, nD4, nH2)

/-! ## 5. `H2` §5's opening sentence is an overclaim

> "Every theorem above carries a non-trivial hypothesis, and every one of them
> is discharged here on the corpus's own object."

Two are not.  `not_hlow_of_not_hlow_ge` and `exists_not_hlow_iff` receive no
instance anywhere in `H2`'s §5.  Both *are* satisfiable, and the missing
instances are supplied below — but they were not in the file, and one of them
is satisfiable only trivially. -/

section MissingInstances

/-- The missing instance of `not_hlow_of_not_hlow_ge`.  Note `d = e = 5`: this
is the **diagonal** case, where the conclusion is literally the hypothesis.

Measured over `s ∈ [6, 3000]`, all late ranks: there is **no** triple
`(s, d, e)` with `d < e` satisfying the hypothesis.  The reason is a theorem —
`H2`'s own `exists_not_hlow_iff` — since the sole failure `(7, 5)` sits at a
first late rank, nothing above it can fail.  So `not_hlow_of_not_hlow_ge` has,
in the whole scanned range, only diagonal instances.  It is not vacuous, but it
is not witnessed non-trivially either, and `H2` says nothing about this. -/
theorem missing_instance_not_hlow_of_not_hlow_ge :
    ¬ (lateCorrection 7 5 ≤ lateEntryRemainder 7 5 % 2 ^ (7 + 1)) :=
  not_hlow_of_not_hlow_ge (e := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    DeclD4.Seven.not_hlow_seven_five

/-- The missing instance of `exists_not_hlow_iff`, forward direction: row `7`
does fail somewhere in its late zone. -/
theorem missing_instance_exists_not_hlow :
    ∃ e : ℕ, 5 ≤ e ∧ e ≤ 7 ∧
      ¬ (lateCorrection 7 e ≤ lateEntryRemainder 7 e % 2 ^ (7 + 1)) :=
  (exists_not_hlow_iff (by norm_num) (by norm_num) (by norm_num)).mpr
    DeclD4.Seven.not_hlow_seven_five

/-- The other direction, on a row where nothing fails: row `20` has no failing
late rank at all.  This is the non-vacuity witness for the *negative* side of
`exists_not_hlow_iff`, also absent from `H2`. -/
theorem missing_instance_no_failure_in_row_twenty :
    ¬ (∃ e : ℕ, 14 ≤ e ∧ e ≤ 20 ∧
        ¬ (lateCorrection 20 e ≤ lateEntryRemainder 20 e % 2 ^ (20 + 1))) := by
  rw [exists_not_hlow_iff (by norm_num) (by norm_num) (by norm_num)]
  exact not_not_intro Concrete.hlow_twenty_fourteen

/-- `hlow_twenty_seventeen`, `H2`'s advertised "fact not in the corpus", checked
against direct computation rather than against `hlow_mono`.  `H2` obtains
`lateCorrection 20 17 ≤ lateEntryRemainder 20 17 % 2 ^ 21` by propagation; the
actual numbers are `84 ≤ 549353`, a margin of five orders of magnitude.  It is a
true new fact and an extremely slack one. -/
theorem hlow_twenty_seventeen_values :
    lateEntryRemainder 20 17 = 549353 ∧ lateCorrection 20 17 = 84 := by
  constructor
  · decide +kernel
  · rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
      lateCorrection_eq_cons (by norm_num), lateCorrection_eq_zero (by norm_num)]
    norm_num

/-- And `lateEntryRemainder 20 17` is already `ρ 20`: ranks `17, 18, 19` are all
declined, so `hlow_twenty_seventeen` is a statement about the final remainder
with the tail correction only. -/
theorem lateEntryRemainder_twenty_seventeen_eq_rho :
    lateEntryRemainder 20 17 = seamIntegerGreedyRemainder 20 := by
  rw [hlow_twenty_seventeen_values.1]
  decide +kernel

/-- `hlow_seven_seven` and the third conjunct of `row_seven_failure_set` are
trivial: `lateCorrection 7 7 = 0`.  The content of `row_seven_failure_set` is
its first two conjuncts, both of which come from `D4`. -/
theorem lateCorrection_seven_seven_is_zero : lateCorrection 7 7 = 0 :=
  lateCorrection_eq_zero (le_refl 7)

end MissingInstances

/-! ## 6. Re-declaration

`ErdosProblems.HlowH2.lateEntryRemainder_succ` is statement-for-statement
`ErdosProblems.DeclD3.lateEntryRemainder_succ` (`ErdosProblems/Decl/D3.lean`,
line 231) — same binders, same hypotheses, same conclusion.  `H2` re-proves it
through `DeclD4.lateEntryRemainder_eq_seamResidualUpto` and
`Three.T1.seamResidualUpto_succ` instead of importing `ErdosProblems.Decl.D3`.

This is harmless to soundness and contrary to the corpus rule to import what one
builds on.  It cannot be exhibited here as a `rfl` because `H2` does not import
`D3`; the two statements are given side by side below for comparison. -/

/-- `H2`'s statement, restated. -/
theorem redeclared_statement (s d : ℕ) (h2 : 2 ≤ d) (hds : d < s) :
    lateEntryRemainder s (d + 1) =
      if truncatedMersenneWeight s d ≤ lateEntryRemainder s d then
        lateEntryRemainder s d - truncatedMersenneWeight s d
      else
        lateEntryRemainder s d :=
  ErdosProblems.HlowH2.lateEntryRemainder_succ h2 hds

/-! ## 7. Verdict

**Sound.**  `H2` compiles with exit `0` and empty output, contains no `sorry`,
no `admit`, no `axiom`, no `native_decide`, and every one of its 30 declarations
depends only on a subset of `[propext, Classical.choice, Quot.sound]`.  It imports `D4`
rather than restating it, with the one exception in §6.  No hypothesis it states
is vacuous: `BitAdmissible` holds at all 26 860 late-rank pairs in `[6, 400]`,
and `BitAdmissible ∧ ¬ hlow` is witnessed at `(7, 5)`.

**What actually moved.**  `hlow_mono` and its corollaries are new and correct:
the failure set of `hlow` inside a row is an initial segment of the late ranks,
so a first-late-rank scan is complete.  That converts `D4`'s scan from evidence
into a proof of completeness *per row*, which is a real if small gain.
`skipCorrection` and the §3 `iff` are new and give a sharper constant than
`D4`'s `lateCorrection` bound.

**What did not.**  §4's headline theorems are corollaries of `D4` (§4 above,
proved).  `hlow` is false at exactly one pair in `[6, 3000]`, so the "hit
certificate" fires once, on a row `D4` already certifies.  `D4`'s bit criterion
certifies all `51` half-point hits in `[6, 120]`; `H2`'s certifies `1`.

**Erdős #257: not moved.**  `H2` proves no unconditional statement about `ρ s`
for any `s` other than `7`, and `ρ 7 < 2 ^ 7` is already `D4.Seven.seamRemainder_seven_lt`.
`half_mem_of_not_hlow_cofinally` is a true implication whose hypothesis is
measured to hold for one row in `[6, 3000]`; `H2` says so plainly, and the
statement is correct in saying so.  The genuine obstruction is unchanged and
untouched here: `hhigh` — the `2 ≤ d ∧ d ≤ s ∧ 2 * s < 3 * d ∧
lateEntryRemainder s d < 2 ^ (2 * s − d + 1)` part of `BitAdmissible` — remains
a hypothesis at every non-numeral row, and `D4`'s §5 already identifies it as
out of reach of the induction in play.  `H2` claims none of this; the header's
"Nothing here resolves Erdős #257" is accurate.

**Defects, in order of seriousness.**

1. The measured claim "tightest surviving margin `52` at `(14, 10)`" is false;
   the true minima are `3` at `(7, 6)` and `30` at `(6, 5)`, the latter a first
   late rank (§3, proved).
2. The measured claim that `(14, 10)` is "the only pair in the whole range where
   `low` and `corr` have equal binary length" is false; `(7, 6)` is another
   (§3, proved).
3. §5's "every one of them is discharged here" is an overclaim: two theorems get
   no instance (§5).
4. `lateEntryRemainder_succ` is re-declared rather than imported (§6).

None of (1)–(4) is used in any `H2` proof — the header's "None of the above is
used in any proof below" is true — so none of them threatens the Lean content.
They are defects in the record, not in the mathematics. -/

end ErdosProblems.HlowH2.Verify
