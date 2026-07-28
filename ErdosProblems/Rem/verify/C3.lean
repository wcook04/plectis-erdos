/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Rem.C3

/-!
# C3-verify: adversarial audit of `ErdosProblems/Rem/C3.lean`

This file only audits.  It introduces no mathematics of its own; everything
below is `#print axioms`, `#check` and `#eval`.  It is *expected* to produce
output.  What must hold is: no `error`, no `warning`, and every axiom line a
sublist of `[propext, Classical.choice, Quot.sound]`.

## Audit protocol

1. **Axioms** — every named theorem of `Rem/C3`, plus the upstream results the
   whole chain rests on (`AngleD2.half_mem_iff_unboundedLargestSkipLate`,
   `BitR1.not_half_mem_iff_exists_forcedRun`,
   `BitR2.half_mem_of_remainderReachesHalfPointCofinally`,
   `BitR2.exists_largestSkipLateAt_of_surplus`,
   `BitR2.exists_largestSkipLateAt_of_remainder_le_two_pow`, `BitR3.rem_eq`).

2. **No proxy predicates** — `HitAt`, `ObeysRemainderCeiling` and the pin window
   are shown by `Iff.rfl` to be the corpus's own
   `Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder` statements,
   and the computational stand-in `BitR3.rem` is tied to it by the *proved*
   equation `rem_eq`, not by fiat.

3. **Satisfiability** — every non-trivial hypothesis is `#eval`-ed over a wide
   range of real rows, using replicas built directly from `BitR3.rem`.

## Findings recorded here (detail in the report)

* `obeysCeiling_of_succ_of_bad` / `obeysCeiling_of_badRun` — hypotheses hold,
  but the *only* rows of `[5, 2999]` at which they can fire are
  `s = 10, 11, 12` (the predecessors of the bad rows `11, 12, 13`).
  Non-vacuous, and the witnesses in `C3 §6` are honest — but the measured live
  set is three rows wide.
* `exists_largestSkipLateAt_of_surplus_of_ceiling_above` — all four hypotheses
  hold at `N = 9`, with the ceiling row `T` free to be *any* of the 2972 rows
  of `[29, 3000]`.  Richly non-vacuous, and the decoupling it claims is
  visible: `T` genuinely need not be `3 * N + 2`.
* `CeilingCofinally` — inner predicate holds at all `2996` rows of `[5, 3000]`;
  zero failures.  Cofinality itself unproved (correctly declared open).
* `PinEscapesCofinally` — inner predicate holds at `2995` of the `2996` rows of
  `[5, 3000]`; the sole occupancy is `s = 8`.  Cofinality unproved (correctly
  declared open), and `pin_occupied_eight` shows it is not a tautology.
* `HitGapBoundedBy K` — **no witness, at any `K`.**  This is the one hypothesis
  in the file exhibited *false* rather than satisfied
  (`not_hitGapBoundedBy_eight` refutes `K ≤ 8`), and the measured maximal gap
  grows with the range (`7, 9, 9, 10, 10, 10` over `[3, S]`).  The module
  docstring's non-vacuity paragraph names only `CeilingCofinally` and
  `PinEscapesCofinally` as unexhibited, and therefore understates by one.
* Nothing in `C3` discharges `RemainderReachesHalfPointCofinally` or
  `1 / 2 ∈ mersenneAchievementSet`.  Both endpoints still carry hypotheses.
  Erdős `#257` is not resolved here.
-/

namespace ErdosProblems.RemC3Verify

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open ErdosProblems

/-! ## 1. Axiom audit -/

section Axioms

-- upstream chain
#print axioms AngleD2.half_mem_iff_unboundedLargestSkipLate
#print axioms Erdos249257.BitR1.not_half_mem_iff_exists_forcedRun
#print axioms ErdosProblems.BitR3.rem_eq
#print axioms ErdosProblems.BitR2.half_mem_of_remainderReachesHalfPointCofinally
#print axioms ErdosProblems.BitR2.exists_largestSkipLateAt_of_surplus
#print axioms ErdosProblems.BitR2.exists_largestSkipLateAt_of_remainder_le_two_pow

-- §1 the bounded-gap criterion
#print axioms ErdosProblems.RemC3.remainderReachesHalfPointCofinally_of_hitGapBoundedBy
#print axioms ErdosProblems.RemC3.half_mem_of_hitGapBoundedBy

-- §2 kernel transfer
#print axioms ErdosProblems.RemC3.hitAt_of_rem
#print axioms ErdosProblems.RemC3.not_hitAt_of_rem
#print axioms ErdosProblems.RemC3.obeysRemainderCeiling_of_rem
#print axioms ErdosProblems.RemC3.pinEscape_of_rem

-- §3 the certified record run
#print axioms ErdosProblems.RemC3.hitAt_502
#print axioms ErdosProblems.RemC3.not_hitAt_503
#print axioms ErdosProblems.RemC3.not_hitAt_504
#print axioms ErdosProblems.RemC3.not_hitAt_505
#print axioms ErdosProblems.RemC3.not_hitAt_506
#print axioms ErdosProblems.RemC3.not_hitAt_507
#print axioms ErdosProblems.RemC3.not_hitAt_508
#print axioms ErdosProblems.RemC3.not_hitAt_509
#print axioms ErdosProblems.RemC3.not_hitAt_510
#print axioms ErdosProblems.RemC3.not_hitAt_511
#print axioms ErdosProblems.RemC3.hitAt_512
#print axioms ErdosProblems.RemC3.not_hitGapBoundedBy_eight

-- §4 downward ceiling transport
#print axioms ErdosProblems.RemC3.obeysCeiling_of_succ_of_bad
#print axioms ErdosProblems.RemC3.obeysCeiling_of_badRun
#print axioms ErdosProblems.RemC3.exists_largestSkipLateAt_of_surplus_of_ceiling_above

-- §5 the pin and the endpoint
#print axioms ErdosProblems.RemC3.pinned_of_ceilingCofinally_of_not_half_mem
#print axioms ErdosProblems.RemC3.half_mem_of_ceilingCofinally_of_pinEscapes
#print axioms ErdosProblems.RemC3.ceilingCofinally_of_missesWindow
#print axioms ErdosProblems.RemC3.pinEscapesCofinally_of_missesWindow

-- §6 witnesses
#print axioms ErdosProblems.RemC3.Witness.hitAt_100
#print axioms ErdosProblems.RemC3.Witness.hitAt_1200
#print axioms ErdosProblems.RemC3.Witness.not_hitAt_1201
#print axioms ErdosProblems.RemC3.Witness.obeysCeiling_12
#print axioms ErdosProblems.RemC3.Witness.obeysCeiling_11
#print axioms ErdosProblems.RemC3.Witness.obeysCeiling_11_not_from_goodRow
#print axioms ErdosProblems.RemC3.Witness.obeysCeiling_13
#print axioms ErdosProblems.RemC3.Witness.obeysCeiling_11_via_run
#print axioms ErdosProblems.RemC3.Witness.obeysCeiling_29
#print axioms ErdosProblems.RemC3.Witness.surplus_nine
#print axioms ErdosProblems.RemC3.Witness.exists_late_above_nine
#print axioms ErdosProblems.RemC3.Witness.obeysCeiling_100
#print axioms ErdosProblems.RemC3.Witness.exists_late_above_nine'
#print axioms ErdosProblems.RemC3.Witness.obeysCeiling_502
#print axioms ErdosProblems.RemC3.Witness.obeysCeiling_1200
#print axioms ErdosProblems.RemC3.Witness.pinEscape_502
#print axioms ErdosProblems.RemC3.Witness.pinEscape_1200
#print axioms ErdosProblems.RemC3.Witness.pin_occupied_eight

end Axioms

/-! ## 2. No proxy predicates

Every predicate in `C3` unfolds, by `Iff.rfl`, to a statement about the corpus's
own `seamIntegerGreedyRemainder`.  The computational replica `BitR3.rem` is tied
to it by the *proved* equation `rem_eq`, audited above. -/

section NoProxy

#check @ErdosProblems.RemC3.HitAt
#check @ErdosProblems.RemC3.HitGapBoundedBy
#check @ErdosProblems.RemC3.CeilingCofinally
#check @ErdosProblems.RemC3.PinEscapesCofinally
#check @ErdosProblems.BitR2.ObeysRemainderCeiling
#check @ErdosProblems.BitR2.RemainderReachesHalfPointCofinally
#check @ErdosProblems.BitR2.RemainderMissesHalfPointWindowCofinally
#check @ErdosProblems.BitR3.rem_eq
#check @Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder
#check @Erdos249257.mersenneAchievementSet

example (s : ℕ) :
    ErdosProblems.RemC3.HitAt s ↔ seamIntegerGreedyRemainder s ≤ 2 ^ s := Iff.rfl

example (s : ℕ) :
    ErdosProblems.BitR2.ObeysRemainderCeiling s ↔
      3 * seamIntegerGreedyRemainder s < 7 * 2 ^ s + 4 := Iff.rfl

/-- The hit set is *literally* the inner predicate of `Bit/R2`'s reduction — not
a proxy for it. -/
example :
    ErdosProblems.BitR2.RemainderReachesHalfPointCofinally ↔
      ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ 5 ≤ s ∧ ErdosProblems.RemC3.HitAt s := Iff.rfl

end NoProxy

/-! ## 3. Satisfiability, on real rows

All replicas are built from `BitR3.rem`, which `rem_eq` proves equal to
`seamIntegerGreedyRemainder`.  No independent reimplementation is involved, so
these numbers cannot drift from the statements they audit. -/

section Satisfiability

open ErdosProblems.BitR3

/-- `HitAt s`, as a `Bool`. -/
def hitB (s : ℕ) : Bool := decide (rem s ≤ 2 ^ s)

/-- `ObeysRemainderCeiling s`, as a `Bool`. -/
def ceilB (s : ℕ) : Bool := decide (3 * rem s < 7 * 2 ^ s + 4)

/-- The pin window `(2 ^ s, 2 ^ s + 2 * s)` is *occupied* at `s`.  The negation
is the inner predicate of `PinEscapesCofinally`. -/
def pinOccB (s : ℕ) : Bool := decide (2 ^ s < rem s ∧ rem s < 2 ^ s + 2 * s)

/-- `¬ LargestSkipLateAt s`, via `Bit/R2`'s own decidable certificate. -/
def badB (s : ℕ) : Bool := ErdosProblems.BitR2.noLateSkip s

def rowsIn (lo hi : ℕ) : List ℕ := (List.range (hi + 1 - lo)).map (· + lo)

def hitsIn (lo hi : ℕ) : List ℕ := (rowsIn lo hi).filter hitB

def gapsOf (l : List ℕ) : List ℕ :=
  match l with
  | [] => []
  | x :: xs => (List.zip xs (x :: xs)).map (fun p => p.1 - p.2)

/-! ### 3.1  The remainder values every witness in `C3` quotes -/

#eval ("rem 8 (doc: 265)", rem 8, "rem 9 (doc: 541)", rem 9,
       "rem 11 (doc: 2485)", rem 11, "rem 12 (doc: 5836)", rem 12,
       "rem 13 (doc: 15147)", rem 13)

/-! ### 3.2  `HitAt` is satisfied at large rows, and so is its negation -/

#eval ("hit 100", hitB 100, "hit 502", hitB 502, "hit 512", hitB 512,
       "hit 1200", hitB 1200, "hit 1201", hitB 1201)

-- Density of the hit set on `[3, 2000]`.  `C3` claims `979 / 1998`.
#eval ("hits on [3,2000]", (hitsIn 3 2000).length,
       "rows", (rowsIn 3 2000).length)

/-! ### 3.3  The record gap, and the growth that kills `HitGapBoundedBy`

`not_hitGapBoundedBy_eight` is sharp: nine consecutive misses refute `K ≤ 8`
and nothing more.  The maximal gap over `[3, S]` grows with `S`, so **no** `K`
is exhibited satisfying `HitGapBoundedBy K` — this hypothesis has no witness. -/

#eval ("maximal gap over [3,S], S = 100,200,500,1000,1500,2000 (doc: 7,9,9,10,10,10)",
       [100, 200, 500, 1000, 1500, 2000].map
         (fun S => (S, (gapsOf (hitsIn 3 S)).foldl max 0)))

#eval ("gap multiset on [3,2000]",
       (List.range 12).map
         (fun k => (k, ((gapsOf (hitsIn 3 2000)).filter (· = k)).length)))

-- The certified run itself: `502` and `512` hit, the nine rows between miss.
#eval ("rows 502..512", (rowsIn 502 512).map (fun s => (s, hitB s)))

/-! ### 3.4  `CeilingCofinally`: inner predicate, every row of `[5, 3000]` -/

#eval ("rows of [5,3000] where the ceiling FAILS",
       ((rowsIn 5 3000).filter (fun s => !ceilB s)))

#eval ("ceiling at the rows C3 certifies",
       [12, 13, 29, 100, 502, 1200].map (fun s => (s, ceilB s)))

/-! ### 3.5  `PinEscapesCofinally`: inner predicate, every row of `[5, 3000]` -/

#eval ("rows of [5,3000] where the pin window is OCCUPIED (escape FAILS)",
       ((rowsIn 5 3000).filter pinOccB))

#eval ("pin escape at the rows C3 certifies",
       [502, 1200].map (fun s => (s, !pinOccB s)))

-- `pin_occupied_eight` is genuine: `rem 8 = 265` really lies in `(256, 272)`,
-- so `PinEscapesCofinally` is a condition and not a tautology.
#eval ("rem 8", rem 8, "window", (2 ^ 8, 2 ^ 8 + 2 * 8), "occupied", pinOccB 8)

/-! ### 3.6  `obeysCeiling_of_succ_of_bad`: where can it fire?

The hypothesis pair is `¬ LargestSkipLateAt (s + 1)` together with the ceiling
at `s + 1`.  The ceiling never fails on `[5, 3000]`, so the live set is exactly
the predecessors of the bad rows. -/

#eval ("bad rows of [5,3000] (certificate `noLateSkip`)",
       (rowsIn 5 3000).filter badB)

#eval ("rows s of [5,2999] at which obeysCeiling_of_succ_of_bad fires",
       (rowsIn 5 2999).filter (fun s => badB (s + 1) && ceilB (s + 1)))

/-! ### 3.7  `exists_largestSkipLateAt_of_surplus_of_ceiling_above`

Hypotheses: `5 ≤ N`, `rem N = 2 ^ N + σ`, `2 * N ≤ σ`, `3 * N + 2 ≤ T`, and the
ceiling at `T`.  Exhibited at `N = 9`; the ceiling row `T` may be taken to be
any row of `[29, 3000]`, which is the decoupling the theorem claims. -/

#eval ("N = 9: rem 9", rem 9, "2^9", 2 ^ 9, "surplus", rem 9 - 2 ^ 9,
       "needs >= 2*9 =", 18, "holds", decide (2 * 9 ≤ rem 9 - 2 ^ 9))

#eval ("admissible ceiling rows T in [29,3000]",
       ((rowsIn 29 3000).filter ceilB).length,
       "of", (rowsIn 29 3000).length)

-- Base rows of `[5, 3000]` carrying surplus `≥ 2 * s`, i.e. rows at which the
-- surplus hypothesis of Theorem B is available at all.
#eval ("count of surplus rows in [5,3000]",
       ((rowsIn 5 3000).filter (fun s => decide (2 ^ s + 2 * s ≤ rem s))).length,
       "of", (rowsIn 5 3000).length)

/-! ### 3.8  The `1 / 2 ∈ mersenneAchievementSet` chain is *not* discharged

Both endpoints still carry hypotheses.  Nothing in `C3` produces
`(1 / 2 : ℝ) ∈ mersenneAchievementSet` unconditionally, and nothing produces
`RemainderReachesHalfPointCofinally` unconditionally. -/

#check @ErdosProblems.RemC3.half_mem_of_hitGapBoundedBy
#check @ErdosProblems.RemC3.half_mem_of_ceilingCofinally_of_pinEscapes
#check @ErdosProblems.RemC3.pinned_of_ceilingCofinally_of_not_half_mem
#check @ErdosProblems.RemC3.not_hitGapBoundedBy_eight

end Satisfiability

end ErdosProblems.RemC3Verify
