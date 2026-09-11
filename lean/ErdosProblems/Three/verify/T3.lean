/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Three.T3

/-!
# Adversarial verification support for `ErdosProblems/Three/T3.lean`

Computable definitions used by the repository-wide proof-trust and
satisfiability audits. The release checker owns proof-trust reporting, while
the measured results of the finite probes are recorded in `docs/TRUTH_AUDIT.md`.
Keeping this support module quiet makes standalone validation deterministic.
-/

namespace ErdosProblems.ThreeT3.Verify

open ErdosProblems ErdosProblems.ThreeT3 Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## Satisfiability support for non-trivial hypotheses on real data

`BitR3.rem` is the kernel-computable form of `seamIntegerGreedyRemainder`
(`BitR3.rem_eq`).  Everything below evaluates the *actual* remainder. -/

section Probes

/-- The isolation hypothesis of `seamIntegerGreedyRemainder_odd_of_isolated`. -/
def Isolated (s : ℕ) : Bool :=
  (List.range s).all fun d => decide (d < 3) || decide (¬ d ∣ 2 * s)

/-- Rows of `[5, N]` where the isolation hypothesis holds. -/
def isolatedRows (N : ℕ) : List ℕ :=
  ((List.range (N + 1)).filter fun s => decide (5 ≤ s) && Isolated s)

/-- Rows where isolation holds but the conclusion (odd remainder) fails.
MUST be empty. -/
def isolationCounterexamples (N : ℕ) : List ℕ :=
  (isolatedRows N).filter fun s => decide (BitR3.rem s % 2 ≠ 1)

/-- Parity census: `(odd, even)` over `[5, N]`. -/
def parityCensus (N : ℕ) : ℕ × ℕ :=
  let rows := (List.range (N + 1)).filter fun s => decide (5 ≤ s)
  (rows.countP fun s => decide (BitR3.rem s % 2 = 1),
   rows.countP fun s => decide (BitR3.rem s % 2 = 0))

/-- Rows of `[5, N]` occupying the hovering band `(2 ^ s, 2 ^ s + 2 * s)`
— the hypothesis of `hovering_low_bits`. -/
def hoverRows (N : ℕ) : List ℕ :=
  (List.range (N + 1)).filter fun s =>
    decide (5 ≤ s) && decide (2 ^ s < BitR3.rem s) &&
      decide (BitR3.rem s < 2 ^ s + 2 * s)

/-- Rows of `[5, N]` inside `Rem/C1`'s band `[2 ^ s + 2, 2 ^ s + 4]`
— the hypothesis of `c1_band_collapses_at_prime`. -/
def c1BandRows (N : ℕ) : List ℕ :=
  (List.range (N + 1)).filter fun s =>
    decide (5 ≤ s) && decide (2 ^ s + 2 ≤ BitR3.rem s) &&
      decide (BitR3.rem s ≤ 2 ^ s + 4)

/-- The 2-adic valuation of the remainder. -/
def v2 (n : ℕ) : ℕ :=
  if h0 : n = 0 then 0 else if n % 2 = 1 then 0 else 1 + v2 (n / 2)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by norm_num)

/-- Rows of `[5, N]` realising the inner predicate of `DyadicDepthCofinally`. -/
def dyadicRows (N : ℕ) : List ℕ :=
  (List.range (N + 1)).filter fun s =>
    decide (5 ≤ s) &&
      ((List.range (s + 1)).any fun k =>
        decide (2 * s ≤ 2 ^ k) && decide (BitR3.rem s % 2 ^ k = 0))

/-- Rows of `[5, N]` with `rem s ≤ 2 ^ s`, i.e. `Rem/C3.HitAt` — the event whose
cofinality *is* `RemainderReachesHalfPointCofinally`. -/
def hitCount (N : ℕ) : ℕ :=
  ((List.range (N + 1)).filter fun s => decide (5 ≤ s)).countP
    fun s => decide (BitR3.rem s ≤ 2 ^ s)

/-- The one-step correction `4 * ρ s - ρ (s+1) - 2 ^ (s+1)` of §5. -/
def gap (s : ℕ) : ℤ :=
  4 * (BitR3.rem s : ℤ) - (BitR3.rem (s + 1) : ℤ) - 2 ^ (s + 1)

end Probes

end ErdosProblems.ThreeT3.Verify
