/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.AngleA3

/-!
# FreeWalk3: exact free-`N` identities and limited no-go models

`Recon249.windowDiscrepancy_shift_emod` turns the base point `N` into a dynamical
variable: at fixed shift `h` and fixed depth `L`, writing `A_N` for
`windowDiscrepancy h N L`,

  `A_{N+1} ≡ 2·A_N + δ_N  (mod 2^L)`,  `δ_N = φ(N+h+1+L) − φ(N+1+L)`,

and `certifiedKill h N L` fails exactly when `A_N` lies within `r_N = N+h+L+2` of a
multiple of `2^L`.  The doubling map expands intervals, so the natural hope is that
a run of consecutive failures cannot be long.  This file does not prove such a
bound.  It records exact identities and countermodels for restricted argument
schemas; it does not rule out every arithmetic approach.  `Half/FreeWalk1.lean`
and `Half/FreeWalk2.lean` contain stronger prior results.

## What is proved

**1. The exact self-similar decomposition** (`windowDiscrepancy_split`):

  `A_{h,N,k+L} = 2^L · A_{h,N,k} + A_{h,N+k,L}`.

`AngleA3.windowDiscrepancy_emod_pow` records the `mod 2^L` shadow of this
(`2^L` divides the head).  The exact identity names the quotient: the head is
itself a window discrepancy, the depth-`k` one at the same base point.  So the
whole `N`-walk is the low-`L`-bit remainder of a *single* integer's successive
deepenings at the fixed base `N`:

  `certifiedKill h (N+k) L  ↔  A_{h,N,k+L} mod 2^L` clears the radius `N+k+h+L+2`
  (`certifiedKill_walk_iff`).

This identity is also a rearrangement of the earlier
`AngleA2.windowDiscrepancy_emod_truncate`; the verifier gives the direct
derivation.  Walking `k` steps can therefore be represented by the deeper
window at base `N`.

**2. The walk's one free move, and its exact price.**  `Lift.AngleA3.certifiedKill_of_endpoint'`
transports a certificate along the anti-diagonal `base + depth = const`.  Restated
for the walk (`certifiedKill_descend`): `certifiedKill h N L → certifiedKill h M (L + (N−M))`
for `M ≤ N`.  `walk_run_transfers` is a contrapositive: a run of `K ≤ L`
consecutive failures at depth `L` implies failures of the *depth* walk at the
single shifted cell `N + L`, for every depth up to `K`.  Its proof actually
uses only the last failed cell, not the full run.  **The coefficient-one price
is needed in the exhibited example**: base descent is *not*
free at fixed depth.  `certifiedKill 1 2 5` holds and `certifiedKill 1 1 5` fails
(`base_descent_not_free`), so the `+1` of depth per unit of base is necessary,
and `certifiedKill 1 1 6` — which the transfer does deliver — is the best available.

**3. The direction the supply theorem needs is quantitatively blocked.**  No law of
the form `certifiedKill h N L → certifiedKill h (N+1) (L+b)` holds for any fixed
budget `b ≤ 10`: `certifiedKill 3 63 8` holds while `certifiedKill 3 64 D` fails for
every `D ≤ 18` (`ascent_witness`, `ascent_blocked`, `no_bounded_ascent_law`).  One
step up in the base point costs at least `11` extra depth *at that cell*, and the
witness is a genuine cell, not a degenerate one.

**4. Runs of consecutive failures are real in the thin regime.**
`certifiedKill 3 63 12` holds, `certifiedKill 3 N 12` fails for all seven
`N = 64, …, 70`, and `certifiedKill 3 71 12` holds again (`failure_run_seven`,
`failure_run_seven_bracketed`).  At the far end of that run the exclusion radius is
`87` inside a modulus of `4096`: the failure zone is `4.2%` of the circle and the
walk sits inside it seven times running.  This is a non-trivial finite witness,
but not an extremal one: `FreeWalk2` already certifies runs of lengths `13`,
`17`, and `19`, and the verifier finds a run of length `8` at the same
`(h,L)`.

**5. There is no absolute bound, and two independent reasons.**

* `not_certifiedKill_of_pow_le` : `2^L ≤ N → ¬ certifiedKill h N L`.  Hence
  `free_walk_run_unbounded`: for every `h`, `L` and every `K`, the `K+1` base points
  `2^L, …, 2^L+K` all fail.  Runs at fixed depth are unconditionally infinite once
  `N` passes `2^L`, so any run bound must be stated relative to `2^L / N`, and the
  "absolute bound `K`" the brief asks for is false as stated.
* `not_certifiedKill_zero_shift` : with `h = 0` every certificate fails at every
  `(N, L)`.  So a run bound must use `h ≥ 1` — it cannot be a fact about the
  doubling map alone.

**6. A limitation of the crude step-size model.**

This file proves no constraint on the actual sequence of totient differences
from `K` consecutive failures.  The only relevant theorem here is the abstract
integer construction below.
`failure_zone_step_invariant` records only a pure integer possibility:
for every `β` in an interval of radius `r`, choosing `δ = −β` keeps `2β + δ`
in the same interval and obeys `|δ| ≤ r`.  The theorem mentions neither
`Nat.totient` nor the walk recurrence, and it does not show that an actual
totient difference ever equals this chosen `δ`.  Its conclusion is therefore
limited to the crude model in which the step input may be any integer within
the size bound.

`§7` gives a countermodel for arguments restricted to the recurrence and the
crude bound `0 ≤ φ(n) ≤ n` (that is all `abs_deltaTotient_le` uses).
`evenFloor n = 2⌊n/2⌋` obeys the same bound —
`evenFloor_le`, `abs_evenDelta_le` — is even, unbounded and monotone, and yet for
every even `h > 0` its window is `h·(2^L − 1)` and **every** certificate fails, at
every `N` and every `L` (`evenWindow_eq`, `not_evenKill`).  Hence no argument that
uses only this recurrence and this crude a-priori size bound can force a run bound
for all functions satisfying that model.  This does not cover the sharper totient
facts used in `FreeWalk1`, such as `φ(n) < n` for `n > 1` and `2 ≤ φ(n)` for
`n ≥ 3`: `evenFloor` does not satisfy those properties.

## Verdict

No absolute bound `K` on consecutive failures is proved here.  In fact,
`free_walk_run_unbounded` disproves such a bound without a restriction relating
`N` to `2^L`, and `not_certifiedKill_zero_shift` supplies a second obstruction
when `h = 0`.  In the crude free-step model, the failure radius and the
a-priori step-size bound have the same scale.  Finite thin-zone witnesses such
as item 4 (seven failures in a zone of relative width `2^{-4.6}`) are statements
about the actual values of `φ`,
not about the map — and by item 5 it is false without the `h ≥ 1` and `N ≪ 2^L`
side conditions that any honest statement must carry.

These results close only the displayed schemas: the proved downward transport,
fixed budgets `b ≤ 10` in the exhibited upward step, and arguments using the
crude size bound alone.  They do not close the free-`N` parameter against
stronger arithmetic information about `Nat.totient`.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace ErdosProblems
namespace Half
namespace FreeWalk3

set_option maxRecDepth 100000

/-! ## 1. The exact self-similar decomposition of a window -/

/-- **Split identity.**  A depth-`(k+L)` window at base `N` is exactly `2^L` times the
depth-`k` window at base `N` plus the depth-`L` window at base `N + k`.

`AngleA3.windowDiscrepancy_emod_pow` records only that `2^L` divides the head.  Here the
head is identified: it is itself a window discrepancy.  So deepening and sliding are the
same operation seen at two place values, and the `N`-walk carries no information beyond
the single deep window at the fixed base. -/
theorem windowDiscrepancy_split (h N k L : ℕ) :
    windowDiscrepancy h N (k + L)
      = 2 ^ L * windowDiscrepancy h N k + windowDiscrepancy h (N + k) L := by
  unfold windowDiscrepancy
  rw [Finset.sum_range_add]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < k := Finset.mem_range.mp hi
    rw [show k + L - 1 - i = L + (k - 1 - i) from by omega, pow_add]
    ring
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [show k + L - 1 - (k + j) = L - 1 - j from by omega,
      show N + h + 1 + (k + j) = N + k + h + 1 + j from by omega,
      show N + 1 + (k + j) = N + k + 1 + j from by omega]

/-- The `N`-walk at depth `L` reads exactly the low `L` bits of the deepening at the
fixed base `N`. -/
theorem windowDiscrepancy_slide_emod (h N k L : ℕ) :
    windowDiscrepancy h N (k + L) % 2 ^ L = windowDiscrepancy h (N + k) L % 2 ^ L := by
  rw [windowDiscrepancy_split,
    show (2 : ℤ) ^ L * windowDiscrepancy h N k + windowDiscrepancy h (N + k) L
      = windowDiscrepancy h (N + k) L + 2 ^ L * windowDiscrepancy h N k from by ring]
  exact Int.add_mul_emod_self_left _ _ _

/-- **The walk in closed form.**  Every cell the free-`N` walk visits is a window on the
single integer `windowDiscrepancy h N (k+L)`; only the exclusion radius moves. -/
theorem certifiedKill_walk_iff (h N k L : ℕ) :
    certifiedKill h (N + k) L ↔
      ((N : ℤ) + k + h + L + 2 < windowDiscrepancy h N (k + L) % 2 ^ L ∧
        windowDiscrepancy h N (k + L) % 2 ^ L < 2 ^ L - ((N : ℤ) + k + h + L + 2)) := by
  unfold certifiedKill
  rw [← windowDiscrepancy_slide_emod]
  constructor
  · rintro ⟨a, b⟩; push_cast at a b; exact ⟨by linarith, by linarith⟩
  · rintro ⟨a, b⟩; refine ⟨?_, ?_⟩ <;> push_cast <;> linarith

/-! ## 2. The one free move of the walk, and its exact price -/

/-- **Descent with an explicit depth price.**  A certificate at base `N` and depth `L`
gives a certificate at every smaller base `M`, at depth `L + (N − M)`: one extra unit of
depth per unit of base descended.  This is `Lift.AngleA3.certifiedKill_of_endpoint'` written in
walk coordinates; `AngleA4.exists_certifiedKill_antitone` is the same statement with the
depth left unquantified. -/
theorem certifiedKill_descend {h M N L : ℕ} (hMN : M ≤ N) (hcert : certifiedKill h N L) :
    certifiedKill h M (L + (N - M)) :=
  Lift.AngleA3.certifiedKill_of_endpoint' (by omega) (by omega) hcert

/-- **The depth price of §2 is sharp.**  Base descent is not free: `certifiedKill 1 2 5`
holds and `certifiedKill 1 1 5` fails.  So the `+1` depth per unit of base in
`certifiedKill_descend` cannot be removed. -/
theorem base_descent_not_free : certifiedKill 1 2 5 ∧ ¬ certifiedKill 1 1 5 := by
  constructor
  · decide
  · decide

/-- What the transfer does deliver at the same cell: one more unit of depth repairs it. -/
theorem base_descent_repaired : certifiedKill 1 1 6 := by
  have := certifiedKill_descend (M := 1) (N := 2) (L := 5) (by omega) base_descent_not_free.1
  simpa using this

/-- **A last-cell transfer, stated for a run.**  If the free-`N` walk at depth
`L` fails at the `K+1` base points `N, …, N+K` (with `K ≤ L`), then
the *depth* walk at the fixed base point `N + L` fails at every depth up to `K`.

The proof uses only the failure at `N+K`; the other `K` failures are
decorative.  The relevant cells share the right endpoint `N + K + L`, and the
conclusion is the contrapositive of the existing anti-diagonal transfer.  It is
not a two-sided description of a run.

**Vacuity, stated plainly.**  The conclusion `¬ certifiedKill h (N+L) k` is automatic from
`certifiedKill_depth_floor` whenever `2(N+L+h+k+2) ≥ 2^k`, i.e. whenever `k ≲ log₂ N`.  So
this transfer has content only for runs *longer* than `log₂` of their own base point.
Applied to `failure_run_seven` (`h = 3`, `N = 64`, `L = 12`, `K = 6`) it is **vacuous**:
`k ≤ 6` and `2^6 = 64 < 2·(64+12+3+6+2)`.

**MEASURED, NOT PROVED HERE.**  A search reported the following non-vacuous
instance; this file neither verifies it nor claims it was minimal over a
specified range:

  `h = 6`, `N = 125384`, `L = 21`, `K = 18`:

nineteen consecutive failures, bracketed by `certifiedKill 6 125383 21` and
`certifiedKill 6 125403 21`, with exclusion radius `2r/2^L ≈ 12%` of the circle, and
`2(N+L+h+K+2) = 250862 < 2^18 = 262144` so the transferred conclusion
`¬ certifiedKill 6 125405 18` is not forced by the depth floor (and is in fact true).
This measurement suggests that the transfer can have non-floor content at run
lengths of order `log₂ N`; it is not used by any theorem in this file. -/
theorem walk_run_transfers {h N L K : ℕ} (hKL : K ≤ L)
    (hrun : ∀ k ≤ K, ¬ certifiedKill h (N + k) L) :
    ∀ k ≤ K, ¬ certifiedKill h (N + L) k := by
  intro k hk hcert
  exact hrun k hk
    (Lift.AngleA3.certifiedKill_of_endpoint' (N := N + k) (N' := N + L) (by omega)
      (by omega) hcert)

/-! ## 3. The direction the supply theorem needs is quantitatively blocked -/

/-- A genuine certificate at base `63`, depth `8`, shift `3`. -/
theorem ascent_witness : certifiedKill 3 63 8 := by decide

/-- The very next base point has no certificate at depth `18`. -/
theorem ascent_blocked : ¬ certifiedKill 3 64 18 := by decide

/-- **No bounded-budget ascent law.**  There is no `b ≤ 10` for which
`certifiedKill h N L → certifiedKill h (N+1) (L+b)`: the cell `(h,N,L) = (3,63,8)` carries a
certificate and its successor base point carries none at any depth up to `18`.

Since `certifiedKill` is upward closed in depth (`certifiedKill_add`), a single failure at
depth `18` kills every smaller depth at once.  Walking one step *up* in the base point
therefore costs at least `11` extra depth at this cell — and nothing in the corpus bounds
that cost anywhere. -/
theorem no_bounded_ascent_law (b : ℕ) (hb : b ≤ 10) :
    certifiedKill 3 63 8 ∧ ¬ certifiedKill 3 64 (8 + b) := by
  refine ⟨ascent_witness, fun hc => ascent_blocked ?_⟩
  have hstep := certifiedKill_add hc (10 - b)
  rwa [show 8 + b + (10 - b) = 18 from by omega] at hstep

/-! ## 4. Runs of consecutive failures are real -/

/-- **A run of seven.**  At shift `3` and depth `12` the walk fails at seven consecutive
base points.  The exclusion radius there is at most `87` inside the modulus `2^12 = 4096`,
so the failure zone occupies about `4.2%` of the circle: this is not a boundary artefact of
a saturated radius, it is the walk genuinely sitting in a thin zone seven steps running. -/
theorem failure_run_seven : ∀ k ∈ Finset.range 7, ¬ certifiedKill 3 (64 + k) 12 := by decide

/-- The run of `failure_run_seven` is exactly seven: certificates on both sides. -/
theorem failure_run_seven_bracketed :
    certifiedKill 3 63 12 ∧ certifiedKill 3 71 12 := by
  constructor
  · decide
  · decide

/-! ## 5. There is no absolute bound on run length -/

/-- Beyond `2^L` the exclusion radius swallows the whole circle: no certificate at depth
`L` can exist at a base point that large. -/
theorem not_certifiedKill_of_pow_le {h N L : ℕ} (hN : 2 ^ L ≤ N) : ¬ certifiedKill h N L := by
  intro hc
  have hfloor := certifiedKill_depth_floor hc
  have hcast : ((2 : ℤ)) ^ L ≤ (N : ℤ) := by exact_mod_cast hN
  have hh : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
  have hL : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  have hNn : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  push_cast at hfloor
  linarith

/-- **No absolute run bound.**  For every shift `h`, every depth `L` and every length `K`,
the `K+1` consecutive base points `2^L, …, 2^L + K` are all failures.  So the brief's
"absolute bound `K` on consecutive failures" is false as stated; any true bound must be
conditioned on `N` being small relative to `2^L`. -/
theorem free_walk_run_unbounded (h L K : ℕ) :
    ∀ k ≤ K, ¬ certifiedKill h (2 ^ L + k) L :=
  fun _ _ => not_certifiedKill_of_pow_le (Nat.le_add_right _ _)

/-- **A run bound must use `h ≥ 1`.**  At `h = 0` the window vanishes identically
(`Lift.AngleA3.windowDiscrepancy_zero_shift`), so every certificate fails at every base point
and every depth: the failure run is infinite.  Nothing about the doubling map alone can
therefore bound a run. -/
theorem not_certifiedKill_zero_shift (N L : ℕ) : ¬ certifiedKill 0 N L := by
  rintro ⟨hlo, -⟩
  rw [Lift.AngleA3.windowDiscrepancy_zero_shift, Int.zero_emod] at hlo
  have hN : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  have hL : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  push_cast at hlo
  linarith

/-! ## 6. What the crude step-size model permits -/

/-- **A pure integer cancellation allowed by the crude size bound.**  For any `β`
in an interval of radius `r`, the choice `δ = −β` obeys `|δ| ≤ r` and leaves
`2β + δ` in the same interval.

This statement has no arithmetic content: it mentions neither `Nat.totient` nor
`windowDiscrepancy` nor `certifiedKill`.  In particular, it does not prove that
the actual totient step can make this choice.  It shows only that a model which
retains the size bound and otherwise treats `δ` as free cannot exclude one-step
persistence by interval expansion alone. -/
theorem failure_zone_step_invariant (r β : ℤ) (hβ : |β| ≤ r) :
    ∃ δ : ℤ, |δ| ≤ r ∧ |2 * β + δ| ≤ r := by
  refine ⟨-β, by rwa [abs_neg], ?_⟩
  rwa [show 2 * β + -β = β from by ring]

/-! ## 7. A surrogate no-go for the crude size-and-parity model -/

/-- `evenFloor n = 2⌊n/2⌋`: a comparison function.  It is even, monotone,
unbounded, and satisfies the crude bound `0 ≤ f n ≤ n`.  It does not satisfy
all totient properties used elsewhere in the free-walk analysis. -/
def evenFloor (n : ℕ) : ℕ := 2 * (n / 2)

/-- The surrogate obeys `φ`'s size bound. -/
theorem evenFloor_le (n : ℕ) : evenFloor n ≤ n := by unfold evenFloor; omega

/-- The comparison function is within one of the identity. -/
theorem le_evenFloor_succ (n : ℕ) : n ≤ evenFloor n + 1 := by unfold evenFloor; omega

/-- The surrogate is even, as `φ n` is for `n ≥ 3`. -/
theorem evenFloor_even (n : ℕ) : Even (evenFloor n) := ⟨n / 2, by unfold evenFloor; omega⟩

/-- The comparison function satisfies the analogue of the crude bound
`abs_deltaTotient_le`. -/
theorem abs_evenDelta_le (h n : ℕ) :
    |((evenFloor (n + h) : ℤ) - (evenFloor n : ℤ))| ≤ ((n + h : ℕ) : ℤ) := by
  have h1 : evenFloor (n + h) ≤ n + h := evenFloor_le _
  have h2 : evenFloor n ≤ n := evenFloor_le _
  have h1' : ((evenFloor (n + h) : ℤ)) ≤ ((n + h : ℕ) : ℤ) := by exact_mod_cast h1
  have h2' : ((evenFloor n : ℤ)) ≤ ((n : ℕ) : ℤ) := by exact_mod_cast h2
  have h3 : (0 : ℤ) ≤ (evenFloor (n + h) : ℤ) := Int.natCast_nonneg _
  have h4 : (0 : ℤ) ≤ (evenFloor n : ℤ) := Int.natCast_nonneg _
  have h5 : (0 : ℤ) ≤ ((h : ℕ) : ℤ) := Int.natCast_nonneg _
  rw [abs_le]
  push_cast at h1' h2' ⊢
  constructor <;> linarith

/-- An even shift translates the surrogate exactly. -/
theorem evenFloor_shift {h : ℕ} (hh : 2 ∣ h) (n : ℕ) :
    evenFloor (n + h) = evenFloor n + h := by unfold evenFloor; omega

/-- The surrogate window discrepancy, verbatim the definition of `windowDiscrepancy` with
`φ` replaced by `evenFloor`. -/
def evenWindow (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((evenFloor (N + h + 1 + j) : ℤ) - (evenFloor (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

/-- The surrogate certificate, verbatim the definition of `certifiedKill`. -/
def evenKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < evenWindow h N L % 2 ^ L ∧
    evenWindow h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

private lemma sum_two_pow_reflect (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 : ℤ) ^ (n - 1 - j) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ' (fun j => (2 : ℤ) ^ (n + 1 - 1 - j)) n]
      have hcong : ∀ i ∈ Finset.range n,
          (2 : ℤ) ^ (n + 1 - 1 - (i + 1)) = (2 : ℤ) ^ (n - 1 - i) := by
        intro i _; congr 1; omega
      rw [Finset.sum_congr rfl hcong, ih, show n + 1 - 1 - 0 = n from by omega, pow_succ]
      ring

/-- **The surrogate window in closed form.**  For an even shift, every coefficient is `h`,
so the window is `h·(2^L − 1)`. -/
theorem evenWindow_eq {h : ℕ} (hh : 2 ∣ h) (N L : ℕ) :
    evenWindow h N L = (h : ℤ) * (2 ^ L - 1) := by
  have hterm : ∀ j ∈ Finset.range L,
      ((evenFloor (N + h + 1 + j) : ℤ) - (evenFloor (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
        = (h : ℤ) * 2 ^ (L - 1 - j) := by
    intro j _
    rw [show N + h + 1 + j = (N + 1 + j) + h from by omega, evenFloor_shift hh]
    push_cast
    ring
  unfold evenWindow
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_two_pow_reflect]

/-- **The no-go.**  For every even `h > 0` the surrogate certificate fails at *every* base
point and *every* depth.

`evenFloor` satisfies the crude size bound `abs_evenDelta_le` and is even,
monotone and unbounded.  Thus a proof of a bound on consecutive failures that
uses only the recurrence `A_{N+1} ≡ 2A_N + δ_N` and this size bound cannot be
valid for every function in that model.  This countermodel says nothing about
arguments using sharper totient properties: for example, `evenFloor 4 = 4`
violates `φ(n) < n` for `n > 1`, and `evenFloor 1 = 0` does not model the lower
bound used by `FreeWalk1`. -/
theorem not_evenKill {h : ℕ} (hh : 2 ∣ h) (hpos : 0 < h) (N L : ℕ) : ¬ evenKill h N L := by
  rintro ⟨-, hhi⟩
  have h2L : (0 : ℤ) < 2 ^ L := by positivity
  set R : ℤ := evenWindow h N L % 2 ^ L with hR
  have hR0 : 0 ≤ R := Int.emod_nonneg _ (ne_of_gt h2L)
  have hRval : R = (-(h : ℤ)) % 2 ^ L := by
    rw [hR, evenWindow_eq hh,
      show (h : ℤ) * (2 ^ L - 1) = -(h : ℤ) + 2 ^ L * (h : ℤ) from by ring,
      Int.add_mul_emod_self_left]
  have hkey : R + 2 ^ L * ((-(h : ℤ)) / 2 ^ L) = -(h : ℤ) := by
    rw [hRval]; exact Int.emod_add_mul_ediv _ _
  have hdvd : (2 : ℤ) ^ L ∣ (h : ℤ) + R :=
    ⟨-((-(h : ℤ)) / 2 ^ L), by linear_combination hkey⟩
  have hhpos : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hpos
  have hle : (2 : ℤ) ^ L ≤ (h : ℤ) + R := Int.le_of_dvd (by linarith) hdvd
  have hN : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  have hL : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  linarith

end FreeWalk3
end Half
end ErdosProblems
