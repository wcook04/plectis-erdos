/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Hlow.H1
import ErdosProblems.Rem.C1

/-!
# V1 — adversarial verification of `ErdosProblems/Hlow/H1.lean`

Two jobs.

**(1) Axiom audit.**  `#print axioms` on every theorem H1 states.  Anything other
than `[propext, Classical.choice, Quot.sound]` is a defect.

**(2) Satisfiability.**  Every non-trivial hypothesis in H1 is `#eval`-scanned
over a wide range of the *genuine object*, not over toy inputs.  A hypothesis
that never holds makes its theorem vacuous; four results earlier in this project
were vacuous, so the default here is disbelief.

The scans below recompute the corpus quantities through the corpus's own
definitions (`lateEntryRemainder`, `lateCorrection`, `truncatedMersenneWeight`,
`integerGreedyRemainder`), so they are a check on H1's *claims*, not a
re-statement of them.
-/

namespace ErdosProblems.HlowV1

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open Erdos249257.BitCorr

/-! ## 1. Axiom audit — every theorem in H1 -/

-- §1: `hlow` without division, and the bit criterion
#print axioms ErdosProblems.HlowH1.hlow_iff
#print axioms ErdosProblems.HlowH1.lateCorrection_lt_two_mul_four_pow
#print axioms ErdosProblems.HlowH1.two_pow_eq_two_mul_four_pow
#print axioms ErdosProblems.HlowH1.two_pow_le_mod_of_testBit
#print axioms ErdosProblems.HlowH1.hlow_of_testBit
#print axioms ErdosProblems.HlowH1.hlow_of_two_mul_four_pow_le
#print axioms ErdosProblems.HlowH1.window_width
#print axioms ErdosProblems.HlowH1.hlow_of_testBit_halfPoint
#print axioms ErdosProblems.HlowH1.testBit_false_of_not_hlow
#print axioms ErdosProblems.HlowH1.hlow_or_window_clear
#print axioms ErdosProblems.HlowH1.mod_lt_of_not_hlow

-- §2: the trapping bounds
#print axioms ErdosProblems.HlowH1.mod_le_mod_sub_add
#print axioms ErdosProblems.HlowH1.sub_multiple_mod
#print axioms ErdosProblems.HlowH1.lateGreedy_lower
#print axioms ErdosProblems.HlowH1.trap
#print axioms ErdosProblems.HlowH1.lateGreedy_lt_sharp
#print axioms ErdosProblems.HlowH1.lateGreedy_lt_two_pow_add
#print axioms ErdosProblems.HlowH1.seamRemainder_lt_sharp_of_hhigh
#print axioms ErdosProblems.HlowH1.seamRemainder_lt_sharp_of_declined
#print axioms ErdosProblems.HlowH1.seamRemainder_lower

-- §3: the refutation
#print axioms ErdosProblems.HlowH1.five_is_first_late_seven
#print axioms ErdosProblems.HlowH1.lateCorrection_seven_five
#print axioms ErdosProblems.HlowH1.lateEntryRemainder_seven_five
#print axioms ErdosProblems.HlowH1.declined_seven_five
#print axioms ErdosProblems.HlowH1.hhigh_holds_seven_five
#print axioms ErdosProblems.HlowH1.hlow_fails_seven_five
#print axioms ErdosProblems.HlowH1.not_hlow_of_hhigh
#print axioms ErdosProblems.HlowH1.not_admissible_seven_five
#print axioms ErdosProblems.HlowH1.seven_five_window_clear

-- §4: the payoff, and the half that genuinely needs `hlow`
#print axioms ErdosProblems.HlowH1.seamRemainder_seven_lt
#print axioms ErdosProblems.HlowH1.upper_trap_needs_hlow
#print axioms ErdosProblems.HlowH1.lateCorrection_seven_six
#print axioms ErdosProblems.HlowH1.lateEntryRemainder_seven_six
#print axioms ErdosProblems.HlowH1.admissible_seven_six

-- §5–§6: anti-vacuity witnesses
#print axioms ErdosProblems.HlowH1.twelve_is_first_late_seventeen
#print axioms ErdosProblems.HlowH1.lateEntryRemainder_seventeen_twelve
#print axioms ErdosProblems.HlowH1.testBit_seventeen_halfPoint
#print axioms ErdosProblems.HlowH1.hlow_seventeen_twelve
#print axioms ErdosProblems.HlowH1.admissible_seventeen
#print axioms ErdosProblems.HlowH1.seamRemainder_seventeen_lt
#print axioms ErdosProblems.HlowH1.fourteen_window_clear
#print axioms ErdosProblems.HlowH1.fourteen_bit_route_silent
#print axioms ErdosProblems.HlowH1.seamRemainder_twenty_lt_sharp

-- §7: instantiations
#print axioms ErdosProblems.HlowH1.mod_lt_seven_five
#print axioms ErdosProblems.HlowH1.window_width_seven_five
#print axioms ErdosProblems.HlowH1.hlow_or_window_clear_seven_five
#print axioms ErdosProblems.HlowH1.seamRemainder_lower_seventeen
#print axioms ErdosProblems.HlowH1.lateGreedy_lt_two_pow_add_seventeen
#print axioms ErdosProblems.HlowH1.hlow_iff_decided

-- The insufficiency result H1's "what is not claimed" section leans on.
#print axioms ErdosProblems.RemC1.exists_persistent_surplus_model

/-! ## 2. Satisfiability scaffolding

`lateEntryRemainder s d` re-runs the early greedy from scratch, so scanning all
`d` of a row through it is quadratic.  `rowEntries s` walks the row once and
returns `(d, lateEntryRemainder s d)` for every `d ∈ [2, s]`; `rowEntries_agrees`
below checks it against the corpus definition rather than trusting it. -/

/-! One descending pass of the seam greedy, tagging each rank with the capacity
that enters it. -/
def rowEntries (s : ℕ) : List (ℕ × ℕ) :=
  let rec go : ℕ → ℕ → List (ℕ × ℕ)
    | 0, C => [(s, C)]
    | Nat.succ k, C =>
        let e := s - (k + 1)
        let w := truncatedMersenneWeight s e
        (e, C) :: go k (if w ≤ C then C - w else C)
  go (s - 2) (seamSubsetTarget s)

/-- Late ranks of row `s`, with their entering capacity. -/
def lateEntries (s : ℕ) : List (ℕ × ℕ) :=
  (rowEntries s).filter (fun p => 2 * s < 3 * p.1 && 2 ≤ p.1)

def hhighAt (s : ℕ) (p : ℕ × ℕ) : Bool := p.2 < 2 ^ (2 * s - p.1 + 1)
def hlowAt (s : ℕ) (p : ℕ × ℕ) : Bool := lateCorrection s p.1 ≤ p.2 % 2 ^ (s + 1)
def declinedAt (s : ℕ) (p : ℕ × ℕ) : Bool := p.2 < truncatedMersenneWeight s p.1
def admissibleAt (s : ℕ) (p : ℕ × ℕ) : Bool := hhighAt s p && hlowAt s p

/-! **The fast walk is checked against the corpus definition**, on every rank of
every row `2 ≤ s ≤ 60`.  Expect `[]`. -/
#eval (List.range 61).flatMap (fun s =>
  if s < 2 then [] else
  ((rowEntries s).filter (fun p => p.2 ≠ lateEntryRemainder s p.1)).map (fun p => (s, p)))

/-! ## 3. Satisfiability of the hypotheses, on the genuine object

`N` below is the scan ceiling.  Raising it costs time but nothing else. -/

def N : ℕ := 260

/-! ### 3.1 `hlow` — the hypothesis H1 claims is FALSE

H1's headline is `not_hlow_of_hhigh`.  For that to be a real result the failure
must be genuine, and H1 also claims the failure set over the scanned range is the
single pair `(7,5)`.  Both are checked here. -/

/-! Every late `(s, d)` with `2 ≤ s ≤ N` at which `hlow` FAILS.  H1 claims this
is exactly `[(7, 5)]`. -/
#eval (List.range (N + 1)).flatMap (fun s =>
  ((lateEntries s).filter (fun p => p.1 < s && !hlowAt s p)).map (fun p => (s, p.1)))

/-! The same, with `d = s` included (`LateEntryAdmissible` permits `d ≤ s`, so
the `d = s` rank is inside the statement's scope). -/
#eval (List.range (N + 1)).flatMap (fun s =>
  ((lateEntries s).filter (fun p => !hlowAt s p)).map (fun p => (s, p.1)))

/-! Every late `(s, d)` at which `hhigh` fails.  H1's prose says "exactly one,
`(5,4)`" — check whether `d = s` ranks add to that. -/
#eval (List.range (N + 1)).flatMap (fun s =>
  ((lateEntries s).filter (fun p => !hhighAt s p)).map (fun p => (s, p.1)))

/-! Restricted to `d < s`, which is the range H1's prose appears to mean. -/
#eval (List.range (N + 1)).flatMap (fun s =>
  ((lateEntries s).filter (fun p => p.1 < s && !hhighAt s p)).map (fun p => (s, p.1)))

/-! The counterexample, spelled out: `(lateEntryRemainder 7 5, low block,
lateCorrection 7 5, hhigh bound)`.  `hlow` needs `20 ≤ 7`. -/
#eval (lateEntryRemainder 7 5, lateEntryRemainder 7 5 % 2 ^ 8, lateCorrection 7 5,
  2 ^ (2 * 7 - 5 + 1))

/-! ### 3.2 `hdecl` — the hypothesis of H1's headline POSITIVE theorem

`seamRemainder_lt_sharp_of_declined` needs a late rank the greedy declines.  If
late declines were rare the theorem would be near-vacuous. -/

/-! Rows `2 ≤ s ≤ N` with **no** late declined rank, i.e. rows where
`seamRemainder_lt_sharp_of_declined` cannot fire at all. -/
#eval (List.range (N + 1)).filter (fun s =>
  s ≥ 5 && ((lateEntries s).filter (fun p => p.1 < s && declinedAt s p)).isEmpty)

/-! Count of late declined ranks at a spread of rows: `(s, #declined late ranks,
#late ranks)`.  Non-vacuity is the first component being positive. -/
#eval ([5, 6, 7, 8, 11, 12, 13, 14, 17, 20, 33, 50, 77, 100, 150, 200, 259] : List ℕ).map
  (fun s => (s,
    ((lateEntries s).filter (fun p => p.1 < s && declinedAt s p)).length,
    ((lateEntries s).filter (fun p => p.1 < s)).length))

/-! ### 3.3 `hhigh` and `LateEntryAdmissible` -/

/-! Rows with **no** late rank satisfying `hhigh`, i.e. rows where
`seamRemainder_lt_sharp_of_hhigh` cannot fire. -/
#eval (List.range (N + 1)).filter (fun s =>
  s ≥ 5 && ((lateEntries s).filter (fun p => hhighAt s p)).isEmpty)

/-! Rows with **no** admissible late rank, i.e. rows `Three/T4` cannot reach.
H1 claims `s = 5` is the only one. -/
#eval (List.range (N + 1)).filter (fun s =>
  s ≥ 5 && ((lateEntries s).filter (fun p => admissibleAt s p)).isEmpty)

/-! Row `7` specifically: which of its late ranks are admissible?  H1 claims
`d = 5` fails and `d = 6` succeeds, so the failure is at a rank, not a row. -/
#eval (lateEntries 7).map (fun p => (p.1, p.2, hhighAt 7 p, hlowAt 7 p))

/-! ### 3.4 The bit criterion of §1

`hlow_of_testBit` needs a set bit in the closed window `[2*(s-d)+1, s]`.
`fourteen_bit_route_silent` claims the criterion is strictly weaker than `hlow`;
the scan below measures how often the criterion actually fires. -/

def windowHasSetBit (s : ℕ) (p : ℕ × ℕ) : Bool :=
  ((List.range (s + 1)).filter (fun j => 2 * (s - p.1) + 1 ≤ j)).any
    (fun j => Nat.testBit p.2 j)

/-! `(s, #late ranks with a set window bit, #late ranks with hlow)`.  The first
count is a lower bound for the second — a strict gap is what
`fourteen_bit_route_silent` exhibits. -/
#eval ([7, 14, 17, 20, 33, 50, 100, 200] : List ℕ).map (fun s => (s,
  ((lateEntries s).filter (fun p => p.1 < s && windowHasSetBit s p)).length,
  ((lateEntries s).filter (fun p => p.1 < s && hlowAt s p)).length))

/-! Any `(s, d)` where the bit criterion fires but `hlow` FAILS would refute
`hlow_of_testBit`.  Expect `[]`. -/
#eval (List.range (N + 1)).flatMap (fun s =>
  ((lateEntries s).filter (fun p => p.1 < s && windowHasSetBit s p && !hlowAt s p)).map
    (fun p => (s, p.1)))

/-! Half-point bit set (`hlow_of_testBit_halfPoint`'s hypothesis): `(s, #late
ranks with bit s set, #late ranks)`. -/
#eval ([7, 14, 17, 20, 33, 50, 100, 200] : List ℕ).map (fun s => (s,
  ((lateEntries s).filter (fun p => p.1 < s && Nat.testBit p.2 s)).length,
  ((lateEntries s).filter (fun p => p.1 < s)).length))

/-! ### 3.5 The late-rank weight identity both §2 proofs rest on

`truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank` is the crux of
`lateGreedy_lower` and `trap`.  Any failure here would break both.  Expect `[]`. -/

#eval (List.range (N + 1)).flatMap (fun s =>
  ((List.range s).filter (fun d =>
    2 ≤ d && d < s && 2 * s < 3 * d &&
      truncatedMersenneWeight s d ≠ 2 ^ (2 * s - d) + 4 ^ (s - d))).map (fun d => (s, d)))

/-! ## 4. Do the PROVED bounds actually hold?  Independent re-check

H1's §2 theorems are proved, so these must come back empty.  They are re-run
here anyway: a proved statement can still be mis-stated relative to the object
it is claimed to be about. -/

/-! `lateGreedy_lt_sharp` on the genuine entering remainders: any late `(s,d)`
with `hhigh` where `3ρ < 3·2^(s+1) + 2·4^(s-d) + 4` FAILS.  Expect `[]`. -/
#eval (List.range 121).flatMap (fun s =>
  ((lateEntries s).filter (fun p => hhighAt s p &&
    !(3 * integerGreedyRemainder (seamWeightsFrom s p.1) p.2
        < 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - p.1) + 4))).map (fun p => (s, p.1)))

/-! `lateGreedy_lower` on the genuine entering remainders, with NO side
condition.  Expect `[]`. -/
#eval (List.range 121).flatMap (fun s =>
  ((lateEntries s).filter (fun p =>
    !(p.2 % 2 ^ (s + 1)
        ≤ integerGreedyRemainder (seamWeightsFrom s p.1) p.2 + lateCorrection s p.1))).map
    (fun p => (s, p.1)))

/-! The same two bounds on a dense grid of *arbitrary* capacities, not just the
genuine entering remainder — `trap` and `lateGreedy_lower` quantify over all `C`.
Expect `(0, 0)`: (upper violations, lower violations). -/
#eval Id.run do
  let mut badU := 0
  let mut badL := 0
  for s in List.range' 6 25 do
    for d in List.range' ((2 * s) / 3 + 1) (s - (2 * s) / 3) do
      if 2 ≤ d && d ≤ s && 2 * s < 3 * d then
        let cap := 2 ^ (2 * s - d + 1)
        for t in List.range' 0 40 do
          let C := (t * 2654435761 + 12345) % cap
          let rho := integerGreedyRemainder (seamWeightsFrom s d) C
          if !(3 * rho < 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4) then badU := badU + 1
          if !(C % 2 ^ (s + 1) ≤ rho + lateCorrection s d) then badL := badL + 1
  return (badU, badL)

/-! ### 4.1 The half of `Three/T4` that H1 says genuinely needs `hlow`

`upper_trap_needs_hlow` exhibits one witness.  Here is the failure rate of
`ρ ≤ C % 2^(s+1)` over the same grid — a nonzero count is what forces that half
to stay conditional. -/

#eval Id.run do
  let mut bad := 0
  let mut tot := 0
  for s in List.range' 6 25 do
    for d in List.range' ((2 * s) / 3 + 1) (s - (2 * s) / 3) do
      if 2 ≤ d && d ≤ s && 2 * s < 3 * d then
        let cap := 2 ^ (2 * s - d + 1)
        for t in List.range' 0 40 do
          let C := (t * 2654435761 + 12345) % cap
          let rho := integerGreedyRemainder (seamWeightsFrom s d) C
          tot := tot + 1
          if !(rho ≤ C % 2 ^ (s + 1)) then bad := bad + 1
  return (bad, tot)

/-! H1's own witness, evaluated: `(ρ, low block)` at `s=7, d=6, C=257`.
`upper_trap_needs_hlow` claims `ρ = 257 > 1 = 257 % 2^8`. -/
#eval (integerGreedyRemainder (seamWeightsFrom 7 6) 257, (257 : ℕ) % 2 ^ 8,
  truncatedMersenneWeight 7 6)

/-! ## 5. Is the bound H1 proves strong enough to move #257?

`seamRemainder_lt_sharp_of_hhigh` gives `ρ s < 2^(s+1) + 4^(s-d)`, which is
**weaker** than `ρ s < 2^(s+1)`.  And `RemC1.exists_persistent_surplus_model`
proves `ρ s < 2^(s+1)` is itself insufficient.  So the gap is measured twice
over.  `(s, first late d, ρ s, 2^(s+1), the bound H1 proves)`. -/

#eval ([7, 14, 17, 20, 33, 50] : List ℕ).map (fun s =>
  let d := (2 * s) / 3 + 1
  (s, d, seamIntegerGreedyRemainder s, 2 ^ (s + 1), 2 ^ (s + 1) + 4 ^ (s - d)))

/-! Does the proved bound ever actually certify `ρ s < 2^(s+1)`?  It does so only
if `2^(s+1) + 4^(s-d) ≤ 2^(s+1)`, which is never.  Listing rows where the bound
implies the `2^(s+1)` ceiling: expect `[]`. -/
#eval ((List.range 121).filter (fun s =>
  5 ≤ s && (2 * s) / 3 + 1 ≤ s &&
    2 ^ (s + 1) + 4 ^ (s - ((2 * s) / 3 + 1)) ≤ 2 ^ (s + 1)))

end ErdosProblems.HlowV1
