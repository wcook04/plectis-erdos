/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Lift.Recon249

/-!
# The free-`N` walk: where the doubling map does and does not expand

`Recon249.windowDiscrepancy_shift_emod` turns the unused base-point parameter `N`
of `certifiedKill h N L` into an exact affine recurrence on `ℤ/2^L`.  Writing

  `ρ_N = windowDiscrepancy h N L % 2^L`,   `δ_N = φ(N+h+1+L) − φ(N+1+L)`,

the recurrence is `ρ_{N+1} ≡ 2·ρ_N + δ_N (mod 2^L)`, and `certifiedKill h N L`
says exactly that `ρ_N` avoids the radius-`r_N` arc around `0`, where
`r_N = N+h+L+2`.  The doubling map expands intervals, so one hopes that a run of
consecutive failures is short.

This file proves escape criteria for the real walk and analyzes a coarser
integer-walk model using only `φ(n) < n` and `2 ≤ φ(n)` for `n ≥ 3`.  The
negative examples belong to that coarse model; they are not totient orbits.

## The budget, and why it is exactly critical

Those two elementary facts give the sharp two-sided step budget
(`walkStep_ge`, `walkStep_le`, packaged as `real_step_budget`)

  `2 − (N+L) ≤ δ_N ≤ (N+h+L) − 2`.

In the coarse interval model, the doubling map `x ↦ 2x + δ` has, against a
budget of size `Δ`, a trapping radius of `Δ`: a point at distance `≤ Δ` from
`0` can be held there forever, while the proved outer bands escape.  The failure
radius is `r_N = N+h+L+2`; the *downward* budget is `N+L−2` and the *upward*
budget is `N+h+L−2`.  So the trapping radius and the failure radius differ by
`h+4` on the upper side of the arc and by `4` on the lower side.  The size data
is therefore critical, not comfortably on either side of the question, and the
outcome is a dichotomy rather than a bound.

## What is proved

**Escape (positive).**

* `certifiedKill_of_upperBand`: if `N + L ≤ ρ_N ≤ N+h+L+2` — the residue fails,
  but sits in the top `h+3` values of the failure arc — then `certifiedKill`
  holds at some `N + j` with `2^j > h + 3`; `certifiedKill_of_upperBand_log`
  restates this as `j ≤ log₂(h+3) + 1`.  Note the bound is **independent of `N`
  and `L`**.
* `certifiedKill_of_lowerBand`: if `N+h+L ≤ 2^L − ρ_N ≤ N+h+L+2` — the bottom
  `3` values of the arc — then `certifiedKill h (N+1) L ∨ certifiedKill h (N+2) L`.
  **At most two consecutive failures, an absolute constant**, with no dependence
  on `h`, `N` or `L` at all.

Both come from one induction (`upperBand_run`, `lowerBand_run`) showing that the
excess over the trapping radius at least doubles each step while the failure
window only widens by `1`.

**No escape in the coarse model.**  `AdmissibleRun` records the recurrence and
the interval bounds on each step, but not evenness or any finer totient
arithmetic.  `trap_upper` and `trap_lower` exhibit, for
every `h`, `N`, `L`, explicit admissible walks that fail at **every** step:

  `a_j = (N+j+L) − 1`  with `d_j = 2 − (N+j+L)`,
  `a_j = −((N+j+h+L) − 1)`  with `d_j = (N+j+h+L) − 2`.

Their starting points are exactly **one** below the two escape thresholds
(`thresholds_are_sharp`).  Nor is this a knife-edge: `trap_interior` shows every
`c` with `−(N+h+L−2) ≤ c ≤ N+L−2` is a *fixed point* of the admissible constant
walk `a_j = c`, `d_j = −c`, whose step size `|c|` may be as small as `0`.  Hence:

  **`no_absolute_bound_on_consecutive_failures`: the coarse `AdmissibleRun`
  model has a permanently trapped walk.**  Formally, the theorem's boundedness
  conjunct is already a field of `AdmissibleRun`; it does not prove that the
  actual totient walk has arbitrarily long failure runs.  The displayed
  threshold examples also use odd steps, whereas genuine totient differences
  are even in this range, so they establish unit sharpness only for the coarse
  interval model.

Within that coarse model, the two escape bands contain `h+6` residues and the
remaining interval admits fixed or permanent model walks.  This does not
classify walks satisfying parity or further totient constraints.

**What the counterexample does and does not say.**  `AdmissibleRun` is the
constraint set the *method* has, not the constraint set the *totients* satisfy:
`d_j = −c` for a run of `j` asks for `φ(M+h) − φ(M) = −c` at consecutive `M`,
which is a statement about actual totients that nothing here decides.  So the
negative refutes the size argument, not #249.  What it does establish is that
any further progress along the free-`N` walk must consume arithmetic information
about individual totients; the recurrence plus `φ(n) < n` plus `2 ≤ φ(n)` is
exhausted, and this file computes exactly how far that exhausted budget reaches.

## Honest accounting of what this closes

The failure arc holds `2·(N+h+L)+5` residues.  The two escape theorems together
cover `h+6` of them (`upperBand_card`, `lowerBand_card`).  The theorem named
`coverage_fraction_tends_to_zero` proves only that for each multiplier there
exists a base point where the full arc exceeds that multiple of the covered
band; it does not formalize a limit or an eventual-for-all statement.  Since
`AngleA4.exists_certifiedKill_antitone` makes large `N` the hard side, the
covered band is on the wrong side of the difficulty.  **This file does not close
#249 and does not close any scale of it.**  It shows only that the coarse
interval bounds do not themselves rule out permanent model failures.

Operationally the positive half is still worth something: a search along the
orbit that ever lands in the outer band may stop, because a certificate is then
guaranteed within `log₂(h+3)+1` further steps, each costing one totient pair
rather than the `2L` a fresh cell costs.

## Non-vacuity

Every hypothesis above is exhibited satisfied, at kernel-checked data:

* `lowerBand_instance`: `h = 9`, `N = 9`, `L = 10`.  Here `2^L − ρ_N = 30` and
  `N+h+L = 28`, so the lower band hypothesis holds; `certifiedKill 9 9 10` is
  false and the theorem's conclusion is realised at `N+1`
  (`lowerBand_instance_realised`).
* `upperBand_instance`: `h = 30`, `N = 1`, `L = 10`.  Here `ρ_N = 14` and
  `N+L = 11`, so the upper band hypothesis holds.  This one genuinely takes two
  steps: `certifiedKill 30 1 10` and `certifiedKill 30 2 10` are both false and
  `certifiedKill 30 3 10` is true (`upperBand_instance_realised`), so the escape
  theorem is not vacuously predicting an immediate kill.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace ErdosProblems
namespace Half
namespace FreeWalk1

set_option maxRecDepth 40000

/-! ## The walk -/

/-- The single new totient pair entering the window when the base point advances:
`δ_N = φ(N+h+1+L) − φ(N+1+L)`. -/
def walkStep (h N L : ℕ) : ℤ :=
  (Nat.totient (N + h + 1 + L) : ℤ) - (Nat.totient (N + 1 + L) : ℤ)

/-- The residue the certificate reads: `ρ_N = A_{h,N,L} mod 2^L`, in `[0, 2^L)`. -/
def walkRes (h N L : ℕ) : ℤ := windowDiscrepancy h N L % 2 ^ L

/-- The distance from the residue up to `2^L`: `σ_N = 2^L − ρ_N`.  This is the
signed distance to `0` on the lower side of the arc. -/
def walkCo (h N L : ℕ) : ℤ := 2 ^ L - walkRes h N L

lemma walkRes_nonneg (h N L : ℕ) : 0 ≤ walkRes h N L :=
  Int.emod_nonneg _ (by positivity)

lemma walkRes_lt (h N L : ℕ) : walkRes h N L < 2 ^ L :=
  Int.emod_lt_of_pos _ (by positivity)

lemma walkRes_eq (h N L : ℕ) : walkRes h N L = 2 ^ L - walkCo h N L := by
  unfold walkCo; ring

/-- **The walk step, exactly.**  Immediate from
`Recon249.windowDiscrepancy_shift_emod`: the residue evolves by the doubling map
plus the one incoming totient pair. -/
theorem walkRes_succ (h N L : ℕ) :
    walkRes h (N + 1) L = (2 * walkRes h N L + walkStep h N L) % 2 ^ L := by
  unfold walkRes walkStep
  rw [ErdosProblems.Lift.Recon249.windowDiscrepancy_shift_emod]
  have h0 : Int.ModEq (2 ^ L) (windowDiscrepancy h N L % 2 ^ L) (windowDiscrepancy h N L) :=
    Int.emod_emod_of_dvd _ dvd_rfl
  exact ((h0.mul_left 2).add_right _).symm

/-! ## The two-sided step budget, from `φ(n) < n` and `2 ≤ φ(n)` -/

/-- `2 ≤ φ(n)` for `n ≥ 3`: the totient is positive and (above `2`) even. -/
lemma two_le_totient {n : ℕ} (hn : 3 ≤ n) : 2 ≤ Nat.totient n := by
  obtain ⟨k, hk⟩ := Nat.totient_even (by omega : 2 < n)
  have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
  omega

/-- **Upper budget.**  `δ_N ≤ (N+h+L) − 2`. -/
lemma walkStep_le {h N L : ℕ} (hNL : 2 ≤ N + L) :
    walkStep h N L ≤ (N : ℤ) + h + L - 2 := by
  have h1 : Nat.totient (N + h + 1 + L) < N + h + 1 + L :=
    Nat.totient_lt _ (by omega)
  have h2 : 2 ≤ Nat.totient (N + 1 + L) := two_le_totient (by omega)
  unfold walkStep
  have h1' : (Nat.totient (N + h + 1 + L) : ℤ) ≤ (N : ℤ) + h + L := by
    have : (Nat.totient (N + h + 1 + L) : ℤ) < ((N + h + 1 + L : ℕ) : ℤ) := by
      exact_mod_cast h1
    push_cast at this
    linarith
  have h2' : (2 : ℤ) ≤ (Nat.totient (N + 1 + L) : ℤ) := by exact_mod_cast h2
  linarith

/-- **Lower budget.**  `2 − (N+L) ≤ δ_N`. -/
lemma walkStep_ge {h N L : ℕ} (hNL : 2 ≤ N + L) :
    (2 : ℤ) - ((N : ℤ) + L) ≤ walkStep h N L := by
  have h1 : Nat.totient (N + 1 + L) < N + 1 + L := Nat.totient_lt _ (by omega)
  have h2 : 2 ≤ Nat.totient (N + h + 1 + L) := two_le_totient (by omega)
  unfold walkStep
  have h1' : (Nat.totient (N + 1 + L) : ℤ) ≤ (N : ℤ) + L := by
    have : (Nat.totient (N + 1 + L) : ℤ) < ((N + 1 + L : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast at this
    linarith
  have h2' : (2 : ℤ) ≤ (Nat.totient (N + h + 1 + L) : ℤ) := by exact_mod_cast h2
  linarith

/-- **The budget along a run.**  At every point of the orbit based at `N` the real
step obeys both bounds.  This is the complete list of constraints the size data
imposes; `AdmissibleRun` below abstracts exactly this list. -/
theorem real_step_budget {h N L : ℕ} (hNL : 2 ≤ N + L) (j : ℕ) :
    2 - ((N : ℤ) + j + L) ≤ walkStep h (N + j) L
      ∧ walkStep h (N + j) L ≤ (N : ℤ) + j + h + L - 2 := by
  constructor
  · have := walkStep_ge (h := h) (N := N + j) (L := L) (by omega)
    push_cast at this ⊢
    linarith
  · have := walkStep_le (h := h) (N := N + j) (L := L) (by omega)
    push_cast at this ⊢
    linarith

/-! ## Failure of the certificate, in terms of the residue -/

/-- A certificate fails exactly when the residue lies in the arc of radius
`N+h+L+2` about `0`, i.e. near `0` from above or near `2^L` from below. -/
lemma not_certifiedKill_iff (h N L : ℕ) :
    ¬ certifiedKill h N L ↔
      (walkRes h N L ≤ (N : ℤ) + h + L + 2
        ∨ (2 : ℤ) ^ L - ((N : ℤ) + h + L + 2) ≤ walkRes h N L) := by
  rw [certifiedKill, not_and_or, not_lt, not_lt]
  rfl

/-! ## The upper band: escape in `log₂(h+3)` steps -/

/-- **The upper-band induction.**  While the run keeps failing, the residue's
excess over the trapping radius `N+j+L−1` at least doubles, and the residue stays
on the upper side of the arc. -/
theorem upperBand_run {h N L K : ℕ} (hNL : 2 ≤ N + L)
    (hroom : 4 * ((N : ℤ) + K + h + L) + 8 ≤ 2 ^ L)
    (hfail : ∀ j, 0 < j → j < K → ¬ certifiedKill h (N + j) L)
    (hlo : (N : ℤ) + L ≤ walkRes h N L)
    (hhi : walkRes h N L ≤ (N : ℤ) + h + L + 2) :
    ∀ j, j < K →
      ((N : ℤ) + j + L + 2 ^ j - 1 ≤ walkRes h (N + j) L
        ∧ walkRes h (N + j) L ≤ (N : ℤ) + j + h + L + 2) := by
  have hN0 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  have hh0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
  have hL0 : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  intro j
  induction j with
  | zero =>
      intro _
      simpa using ⟨hlo, hhi⟩
  | succ j ih =>
      intro hjK
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hjK' : (j : ℤ) ≤ (K : ℤ) := by exact_mod_cast Nat.le_of_lt (by omega : j < K)
      have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      have hpow : (0 : ℤ) < 2 ^ j := pow_pos (by norm_num) j
      have hpow2 : (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j := by ring
      obtain ⟨hs1, hs2⟩ := real_step_budget (h := h) (N := N) (L := L) hNL j
      -- no wraparound
      have hxlo : 0 ≤ 2 * walkRes h (N + j) L + walkStep h (N + j) L := by linarith
      have hxhi : 2 * walkRes h (N + j) L + walkStep h (N + j) L < 2 ^ L := by linarith
      have hidx : N + (j + 1) = N + j + 1 := by omega
      have hval : walkRes h (N + (j + 1)) L
          = 2 * walkRes h (N + j) L + walkStep h (N + j) L := by
        rw [hidx, walkRes_succ]
        exact Int.emod_eq_of_lt hxlo hxhi
      refine ⟨?_, ?_⟩
      · rw [hval]
        push_cast
        rw [hpow2] at *
        linarith
      · rcases (not_certifiedKill_iff h (N + (j + 1)) L).mp (hfail (j + 1) (by omega) hjK)
          with hcase | hcase
        · push_cast at hcase ⊢
          linarith
        · exfalso
          rw [hval] at hcase
          push_cast at hcase
          linarith

/-- **Upper-band escape.**  If the residue at `N` fails but lies in the top
`h+3` values of the failure arc, a certificate appears within `K` steps for any
`K` with `2^(K-1) > h+3` — a bound depending on `h` alone, not on `N` or `L`. -/
theorem certifiedKill_of_upperBand {h N L K : ℕ} (hNL : 2 ≤ N + L)
    (hK : (h : ℤ) + 3 < 2 ^ (K - 1))
    (hroom : 4 * ((N : ℤ) + K + h + L) + 8 ≤ 2 ^ L)
    (hlo : (N : ℤ) + L ≤ walkRes h N L)
    (hhi : walkRes h N L ≤ (N : ℤ) + h + L + 2) :
    ∃ j < K, certifiedKill h (N + j) L := by
  by_contra hcon
  have hfail : ∀ j, 0 < j → j < K → ¬ certifiedKill h (N + j) L :=
    fun j _ hj hc => hcon ⟨j, hj, hc⟩
  have hK1 : 1 ≤ K := by
    by_contra hc
    have : K = 0 := by omega
    subst this
    norm_num at hK
    linarith [Int.natCast_nonneg h]
  obtain ⟨hA, hB⟩ :=
    upperBand_run (h := h) (N := N) (L := L) (K := K) hNL hroom hfail hlo hhi (K - 1) (by omega)
  linarith

/-- **Upper-band escape, logarithmic form.**  A certificate appears within
`log₂(h+3) + 1` steps. -/
theorem certifiedKill_of_upperBand_log {h N L : ℕ} (hNL : 2 ≤ N + L)
    (hroom : 4 * ((N : ℤ) + (Nat.log 2 (h + 3) + 2) + h + L) + 8 ≤ 2 ^ L)
    (hlo : (N : ℤ) + L ≤ walkRes h N L)
    (hhi : walkRes h N L ≤ (N : ℤ) + h + L + 2) :
    ∃ j ≤ Nat.log 2 (h + 3) + 1, certifiedKill h (N + j) L := by
  have hK : (h : ℤ) + 3 < 2 ^ (Nat.log 2 (h + 3) + 2 - 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (h + 3)
    have h2 : Nat.log 2 (h + 3) + 2 - 1 = Nat.log 2 (h + 3) + 1 := by omega
    rw [h2]
    exact_mod_cast this
  obtain ⟨j, hj, hcert⟩ :=
    certifiedKill_of_upperBand (K := Nat.log 2 (h + 3) + 2) hNL hK hroom hlo hhi
  exact ⟨j, by omega, hcert⟩

/-! ## The lower band: at most two consecutive failures, absolutely -/

/-- **The lower-band induction.**  Mirror image of `upperBand_run`: the excess of
`σ_j = 2^L − ρ_j` over its trapping radius `N+j+h+L−1` at least doubles. -/
theorem lowerBand_run {h N L K : ℕ} (hNL : 2 ≤ N + L)
    (hroom : 4 * ((N : ℤ) + K + h + L) + 8 ≤ 2 ^ L)
    (hfail : ∀ j, 0 < j → j < K → ¬ certifiedKill h (N + j) L)
    (hlo : (N : ℤ) + h + L ≤ walkCo h N L)
    (hhi : walkCo h N L ≤ (N : ℤ) + h + L + 2) :
    ∀ j, j < K →
      ((N : ℤ) + j + h + L + 2 ^ j - 1 ≤ walkCo h (N + j) L
        ∧ walkCo h (N + j) L ≤ (N : ℤ) + j + h + L + 2) := by
  have hN0 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  have hh0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
  have hL0 : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  intro j
  induction j with
  | zero =>
      intro _
      simpa using ⟨hlo, hhi⟩
  | succ j ih =>
      intro hjK
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hjK' : (j : ℤ) ≤ (K : ℤ) := by exact_mod_cast Nat.le_of_lt (by omega : j < K)
      have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      have hpow : (0 : ℤ) < 2 ^ j := pow_pos (by norm_num) j
      have hpow2 : (2 : ℤ) ^ (j + 1) = 2 * 2 ^ j := by ring
      obtain ⟨hs1, hs2⟩ := real_step_budget (h := h) (N := N) (L := L) hNL j
      have hres : walkRes h (N + j) L = 2 ^ L - walkCo h (N + j) L := walkRes_eq h (N + j) L
      -- rewrite the doubling step in terms of the codistance
      have hshape : 2 * walkRes h (N + j) L + walkStep h (N + j) L
          = (2 ^ L - (2 * walkCo h (N + j) L - walkStep h (N + j) L)) + 1 * 2 ^ L := by
        rw [hres]; ring
      have hylo : 0 ≤ 2 ^ L - (2 * walkCo h (N + j) L - walkStep h (N + j) L) := by
        linarith
      have hyhi : 2 ^ L - (2 * walkCo h (N + j) L - walkStep h (N + j) L) < 2 ^ L := by
        linarith
      have hidx : N + (j + 1) = N + j + 1 := by omega
      have hval : walkCo h (N + (j + 1)) L
          = 2 * walkCo h (N + j) L - walkStep h (N + j) L := by
        have hthis : walkRes h (N + (j + 1)) L
            = 2 ^ L - (2 * walkCo h (N + j) L - walkStep h (N + j) L) := by
          rw [hidx, walkRes_succ, hshape, Int.add_mul_emod_self_right]
          exact Int.emod_eq_of_lt hylo hyhi
        show (2 : ℤ) ^ L - walkRes h (N + (j + 1)) L
            = 2 * walkCo h (N + j) L - walkStep h (N + j) L
        rw [hthis]
        ring
      refine ⟨?_, ?_⟩
      · rw [hval]
        push_cast
        rw [hpow2] at *
        linarith
      · rcases (not_certifiedKill_iff h (N + (j + 1)) L).mp (hfail (j + 1) (by omega) hjK)
          with hcase | hcase
        · exfalso
          have hcc : walkCo h (N + (j + 1)) L
              = 2 ^ L - walkRes h (N + (j + 1)) L := rfl
          rw [hval] at hcc
          push_cast at hcase hcc h1 h2
          linarith
        · have hcc : walkCo h (N + (j + 1)) L
              = 2 ^ L - walkRes h (N + (j + 1)) L := rfl
          rw [hval] at hcc
          push_cast at hcase hcc ⊢
          linarith

/-- **Lower-band escape: an absolute constant.**  If the residue at `N` fails on
the lower side of the arc and sits in the bottom `3` values, then a certificate
holds at `N+1` or at `N+2`.  There is no dependence on `h`, `N` or `L`
whatsoever: at most two consecutive failures. -/
theorem certifiedKill_of_lowerBand {h N L : ℕ} (hNL : 2 ≤ N + L)
    (hroom : 4 * ((N : ℤ) + 3 + h + L) + 8 ≤ 2 ^ L)
    (hlo : (N : ℤ) + h + L ≤ walkCo h N L)
    (hhi : walkCo h N L ≤ (N : ℤ) + h + L + 2) :
    certifiedKill h (N + 1) L ∨ certifiedKill h (N + 2) L := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hfail : ∀ j, 0 < j → j < 3 → ¬ certifiedKill h (N + j) L := by
    intro j hj0 hj3
    interval_cases j
    · exact hc1
    · exact hc2
  have hroom' : 4 * ((N : ℤ) + (3 : ℕ) + h + L) + 8 ≤ 2 ^ L := by push_cast; linarith
  obtain ⟨hA, hB⟩ :=
    lowerBand_run (h := h) (N := N) (L := L) (K := 3) hNL hroom' hfail hlo hhi 2 (by omega)
  norm_num at hA hB
  linarith

/-! ## The negative half: no absolute bound, and the thresholds are sharp -/

/-- **Exactly the data the size argument has.**  A run of the walk based at `N`
for which the affine recurrence holds and the step obeys the two-sided totient
budget of `real_step_budget`, and which never leaves the failure arc.  Any
argument that bounds the number of consecutive failures using only the
recurrence and `φ(n) < n`, `2 ≤ φ(n)` must rule this out. -/
structure AdmissibleRun (h N L : ℕ) (a d : ℕ → ℤ) : Prop where
  /-- the affine doubling recurrence of `walkRes_succ` -/
  step_rec : ∀ j, a (j + 1) = 2 * a j + d j
  /-- the lower half of the budget of `real_step_budget` -/
  step_lo : ∀ j, 2 - ((N : ℤ) + j + L) ≤ d j
  /-- the upper half of the budget of `real_step_budget` -/
  step_hi : ∀ j, d j ≤ (N : ℤ) + j + h + L - 2
  /-- the certificate fails at **every** step of the run -/
  trapped : ∀ j, |a j| ≤ (N : ℤ) + j + h + L + 2

/-- **Upper-side trapped walk.**  `a_j = (N+j+L) − 1` with `d_j = 2 − (N+j+L)`
is admissible and fails forever.  Its start is one below the threshold `N+L` of
`certifiedKill_of_upperBand`. -/
theorem trap_upper (h N L : ℕ) (hNL : 2 ≤ N + L) :
    AdmissibleRun h N L (fun j => (N : ℤ) + j + L - 1) (fun j => 2 - ((N : ℤ) + j + L)) := by
  have hNL' : (2 : ℤ) ≤ (N : ℤ) + L := by exact_mod_cast hNL
  have hh0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j; push_cast; ring
  · intro j; linarith
  · intro j
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    linarith
  · intro j
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    have hnn : (0 : ℤ) ≤ (N : ℤ) + j + L - 1 := by linarith
    rw [abs_of_nonneg hnn]
    linarith

/-- **Lower-side trapped walk.**  `a_j = −((N+j+h+L) − 1)` with
`d_j = (N+j+h+L) − 2` is admissible and fails forever.  Its start is one below
(in absolute value) the threshold `N+h+L` of `certifiedKill_of_lowerBand`. -/
theorem trap_lower (h N L : ℕ) (hNL : 2 ≤ N + L) :
    AdmissibleRun h N L (fun j => -((N : ℤ) + j + h + L - 1))
      (fun j => (N : ℤ) + j + h + L - 2) := by
  have hNL' : (2 : ℤ) ≤ (N : ℤ) + L := by exact_mod_cast hNL
  have hh0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j; push_cast; ring
  · intro j
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    linarith
  · intro j; linarith
  · intro j
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    have hnn : (0 : ℤ) ≤ (N : ℤ) + j + h + L - 1 := by linarith
    rw [abs_neg, abs_of_nonneg hnn]
    linarith

/-- **The trapping is not a knife-edge: the whole interior is fixed.**  For every
`c` in the interior arc `−(N+h+L−2) ≤ c ≤ N+L−2` the *constant* walk `a_j = c`,
`d_j = −c` is admissible and fails forever.  So it is not merely some extremal
trajectory that survives: every residue strictly inside the trapping radii is a
fixed point of an admissible walk, and the step it uses is `|d_j| = |c|`, which
can be as small as `0` — nowhere near the edge of the budget. -/
theorem trap_interior (h N L : ℕ) (c : ℤ)
    (hc1 : -((N : ℤ) + h + L - 2) ≤ c) (hc2 : c ≤ (N : ℤ) + L - 2) :
    AdmissibleRun h N L (fun _ => c) (fun _ => -c) := by
  have hh0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j; ring
  · intro j
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    linarith
  · intro j
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    linarith
  · intro j
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    rw [abs_le]
    constructor <;> linarith

/-- For every `h`, `N`, `L` there is a coarse `AdmissibleRun` that remains
trapped.  The second conjunct is already the `trapped` field of that structure.
This does not construct a sequence of actual totient differences. -/
theorem no_absolute_bound_on_consecutive_failures (h N L : ℕ) (hNL : 2 ≤ N + L) :
    ∃ a d : ℕ → ℤ, AdmissibleRun h N L a d ∧ ∀ K : ℕ, ∀ j < K,
      |a j| ≤ (N : ℤ) + j + h + L + 2 :=
  ⟨_, _, trap_upper h N L hNL, fun _ j _ => (trap_upper h N L hNL).trapped j⟩

/-- **Both escape thresholds are sharp to the unit inside `AdmissibleRun`.**
The upper-band theorem
fires at `N+L`; the walk of `trap_upper` starts at `N+L−1` and never escapes.
The lower-band theorem fires at codistance `N+h+L`; the walk of `trap_lower`
starts at codistance `N+h+L−1` and never escapes.  These model walks have odd
steps and therefore are not genuine totient walks in the range where totients
are even. -/
theorem thresholds_are_sharp (h N L : ℕ) (hNL : 2 ≤ N + L) :
    ((fun j => (N : ℤ) + j + L - 1) 0 = ((N : ℤ) + L) - 1
      ∧ AdmissibleRun h N L (fun j => (N : ℤ) + j + L - 1)
          (fun j => 2 - ((N : ℤ) + j + L)))
    ∧ ((fun j => -((N : ℤ) + j + h + L - 1)) 0 = -(((N : ℤ) + h + L) - 1)
      ∧ AdmissibleRun h N L (fun j => -((N : ℤ) + j + h + L - 1))
          (fun j => (N : ℤ) + j + h + L - 2)) :=
  ⟨⟨by push_cast; ring, trap_upper h N L hNL⟩,
   ⟨by push_cast; ring, trap_lower h N L hNL⟩⟩

/-! ## How much of the failure arc the escape theorems cover -/

/-- The upper band has `h+3` residues. -/
theorem upperBand_card (h N L : ℕ) :
    (Finset.Icc ((N : ℤ) + L) ((N : ℤ) + h + L + 2)).card = h + 3 := by
  rw [Int.card_Icc]
  omega

/-- The lower band has `3` residues. -/
theorem lowerBand_card (h N L : ℕ) :
    (Finset.Icc ((N : ℤ) + h + L) ((N : ℤ) + h + L + 2)).card = 3 := by
  rw [Int.card_Icc]
  omega

/-- **An arbitrarily small-ratio witness.**  The failure arc holds
`2·(N+h+L)+5` residues; the two escape theorems cover `h+6` of them, a count
independent of `N`.  The statement supplies, for each ratio `M`, one base point
where the arc is more than `M` times the covered band.  It does not itself state
a limit or quantify over all larger base points. -/
theorem coverage_fraction_tends_to_zero (h L M : ℕ) :
    ∃ N, M * (h + 6) < 2 * (N + h + L) + 5 :=
  ⟨M * (h + 6), by omega⟩

/-! ## Non-vacuity: the hypotheses hold at kernel-checked data -/

/-- `2^10 − ρ = 30` at `h = 9`, `N = 9`, `L = 10`. -/
theorem lowerBand_instance_data : walkCo 9 9 10 = 30 := by
  unfold walkCo walkRes
  decide

/-- The lower-band hypothesis is satisfiable: at `h = 9`, `N = 9`, `L = 10` the
codistance is `30` and `N+h+L = 28 ≤ 30 ≤ 30`.  So
`certifiedKill_of_lowerBand` fires, and predicts a kill at `N+1` or `N+2`. -/
theorem lowerBand_instance :
    certifiedKill 9 (9 + 1) 10 ∨ certifiedKill 9 (9 + 2) 10 := by
  refine certifiedKill_of_lowerBand (h := 9) (N := 9) (L := 10) (by norm_num) ?_ ?_ ?_
  · norm_num
  · rw [lowerBand_instance_data]; norm_num
  · rw [lowerBand_instance_data]; norm_num

/-- And the prediction is correct: the kill is at `N+1`, while `N` itself fails.
(Both facts are kernel evaluations, independent of the theorem.) -/
theorem lowerBand_instance_realised :
    ¬ certifiedKill 9 9 10 ∧ certifiedKill 9 10 10 := by
  constructor
  · decide
  · decide

/-- `ρ = 14` at `h = 30`, `N = 1`, `L = 10`. -/
theorem upperBand_instance_data : walkRes 30 1 10 = 14 := by
  unfold walkRes
  decide

/-- The upper-band hypothesis is satisfiable: at `h = 30`, `N = 1`, `L = 10` the
residue is `14`, and `N+L = 11 ≤ 14 ≤ 43 = N+h+L+2`.  With `K = 7` the escape
theorem applies, since `h+3 = 33 < 64 = 2^6`. -/
theorem upperBand_instance : ∃ j < 7, certifiedKill 30 (1 + j) 10 := by
  refine certifiedKill_of_upperBand (h := 30) (N := 1) (L := 10) (K := 7)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_
  · rw [upperBand_instance_data]; norm_num
  · rw [upperBand_instance_data]; norm_num

/-- The escape here genuinely takes two steps, so the theorem is not silently
predicting an immediate kill: `certifiedKill 30 1 10` and `certifiedKill 30 2 10`
are both false, and `certifiedKill 30 3 10` is true. -/
theorem upperBand_instance_realised :
    ¬ certifiedKill 30 1 10 ∧ ¬ certifiedKill 30 2 10 ∧ certifiedKill 30 3 10 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

end FreeWalk1
end Half
end ErdosProblems
