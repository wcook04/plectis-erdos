/-
Adversarial verification of ErdosProblems/Half/FreeWalk3.lean.

Diagnostics only.  Everything below is either (a) an axiom audit of a
declaration actually proved in FreeWalk3.lean, or (b) a probe showing that one
of that file's statements is weaker, or more vacuous, than its docstring
claims.  Nothing here is imported by the corpus and no new claim about #249 or
about `mersenneAchievementSet` is made.
-/
import ErdosProblems.Half.FreeWalk1
import ErdosProblems.Half.FreeWalk2
import ErdosProblems.Half.FreeWalk3

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace FreeWalk3Verify

set_option maxRecDepth 100000

/-! ## 1. Axiom audit of every declaration in FreeWalk3.lean -/

#print axioms ErdosProblems.Half.FreeWalk3.windowDiscrepancy_split
#print axioms ErdosProblems.Half.FreeWalk3.windowDiscrepancy_slide_emod
#print axioms ErdosProblems.Half.FreeWalk3.certifiedKill_walk_iff
#print axioms ErdosProblems.Half.FreeWalk3.certifiedKill_descend
#print axioms ErdosProblems.Half.FreeWalk3.base_descent_not_free
#print axioms ErdosProblems.Half.FreeWalk3.base_descent_repaired
#print axioms ErdosProblems.Half.FreeWalk3.walk_run_transfers
#print axioms ErdosProblems.Half.FreeWalk3.ascent_witness
#print axioms ErdosProblems.Half.FreeWalk3.ascent_blocked
#print axioms ErdosProblems.Half.FreeWalk3.no_bounded_ascent_law
#print axioms ErdosProblems.Half.FreeWalk3.failure_run_seven
#print axioms ErdosProblems.Half.FreeWalk3.failure_run_seven_bracketed
#print axioms ErdosProblems.Half.FreeWalk3.not_certifiedKill_of_pow_le
#print axioms ErdosProblems.Half.FreeWalk3.free_walk_run_unbounded
#print axioms ErdosProblems.Half.FreeWalk3.not_certifiedKill_zero_shift
#print axioms ErdosProblems.Half.FreeWalk3.failure_zone_step_invariant
#print axioms ErdosProblems.Half.FreeWalk3.evenFloor_le
#print axioms ErdosProblems.Half.FreeWalk3.le_evenFloor_succ
#print axioms ErdosProblems.Half.FreeWalk3.evenFloor_even
#print axioms ErdosProblems.Half.FreeWalk3.abs_evenDelta_le
#print axioms ErdosProblems.Half.FreeWalk3.evenFloor_shift
#print axioms ErdosProblems.Half.FreeWalk3.evenWindow_eq
#print axioms ErdosProblems.Half.FreeWalk3.not_evenKill

/-! ## 2. Probe: the "run" hypothesis of `walk_run_transfers` is decorative

`walk_run_transfers` assumes `K+1` consecutive failures
(`∀ k ≤ K, ¬ certifiedKill h (N+k) L`) and concludes
`∀ k ≤ K, ¬ certifiedKill h (N+L) k`.  The single instance `k = K` of that
hypothesis already gives the whole conclusion, because `certifiedKill` is
upward closed in depth (`certifiedKill_add`).  So the theorem uses no property
of a *run* at all; it is the contrapositive of the anti-diagonal transfer
`Lift.AngleA3.certifiedKill_of_endpoint'` at one point. -/
theorem transfer_needs_only_the_last_failure {h N L K : ℕ} (hKL : K ≤ L)
    (hsingle : ¬ certifiedKill h (N + K) L) :
    ∀ k ≤ K, ¬ certifiedKill h (N + L) k := by
  intro k hk hcert
  have hK : certifiedKill h (N + L) K := by
    have hup := certifiedKill_add hcert (K - k)
    rwa [show k + (K - k) = K from by omega] at hup
  exact hsingle
    (ErdosProblems.Lift.AngleA3.certifiedKill_of_endpoint' (N := N + K) (N' := N + L)
      (by omega) (by omega) hK)

/-- `walk_run_transfers` is an immediate corollary of the single-point version:
its `∀ k ≤ K` hypothesis is used only at `k = K`. -/
theorem walk_run_transfers_is_a_corollary {h N L K : ℕ} (hKL : K ≤ L)
    (hrun : ∀ k ≤ K, ¬ certifiedKill h (N + k) L) :
    ∀ k ≤ K, ¬ certifiedKill h (N + L) k :=
  transfer_needs_only_the_last_failure hKL (hrun K le_rfl)

/-! ## 3. Probe: at FreeWalk3's own numerical witness the transfer is empty

FreeWalk3 states this in prose ("Applied to `failure_run_seven` it is
**vacuous**").  Here it is kernel-checked: the conclusion of
`walk_run_transfers` for `h = 3`, `N = 64`, `L = 12`, `K = 6` — namely
`∀ k ≤ 6, ¬ certifiedKill 3 76 k` — is provable with *no* hypothesis at all. -/
theorem transfer_conclusion_at_seven_run_is_unconditional :
    ∀ k ∈ Finset.range 7, ¬ certifiedKill 3 76 k := by
  decide

/-! ## 4. Probe: `failure_zone_step_invariant` has no arithmetic content

FreeWalk3's §6 presents

  `|β| ≤ r → ∃ δ, |δ| ≤ r ∧ |2β + δ| ≤ r`

as "the metric obstruction: doubling is exactly critical", the point being that
the totient size bound is large enough to cancel the doubling.  But the
statement holds with the radius `r` deleted entirely and `δ` confined to
`|δ| ≤ |β|`, which is far *tighter* than the totient bound ever permits.  The
size of the admissible `δ`-range plays no role: `δ = -β` inverts doubling for
purely formal reasons.  Neither `Nat.totient` nor `windowDiscrepancy` nor
`certifiedKill` occurs in the statement. -/
theorem step_invariant_needs_no_radius (β : ℤ) :
    ∃ δ : ℤ, |δ| ≤ |β| ∧ |2 * β + δ| ≤ |β| := by
  refine ⟨-β, le_of_eq (abs_neg β), ?_⟩
  rw [show 2 * β + -β = β from by ring]

/-- FreeWalk3's §6 statement follows from the radius-free one, for every `r`. -/
theorem file_step_invariant_from_radius_free (r β : ℤ) (hβ : |β| ≤ r) :
    ∃ δ : ℤ, |δ| ≤ r ∧ |2 * β + δ| ≤ r := by
  obtain ⟨δ, h1, h2⟩ := step_invariant_needs_no_radius β
  exact ⟨δ, le_trans h1 hβ, le_trans h2 hβ⟩

/-! ## 5. Probe: "a run of seven" is not extremal, even at the same `(h, L)`

At the same shift and depth there is a run of **eight**, at `N = 349, …, 356`,
also bracketed by certificates.  FreeWalk3 never claims seven is maximal, but
its §4 rhetoric ("the answer is not one") is calibrated to a number that is not
the largest available in the very slice it examines. -/
theorem failure_run_eight :
    ∀ k ∈ Finset.range 8, ¬ certifiedKill 3 (349 + k) 12 := by
  decide

theorem failure_run_eight_bracketed :
    certifiedKill 3 348 12 ∧
      certifiedKill 3 357 12 := by
  constructor
  · decide
  · decide

/-! ## 6. Probe: prior art in the same directory, uncited and unimported

FreeWalk3 imports only `ErdosProblems.Lift.AngleA3` and never mentions
`FreeWalk1` or `FreeWalk2`, which sit beside it in `ErdosProblems/Half/` and
already contain sharper forms of §2, §4, §5, §6 and §7.  The references below
resolve, so the prior art really is in the corpus. -/

/-! FreeWalk2 already proves the two-sided run law, of which FreeWalk3's
`walk_run_transfers` is one weakened direction (its conclusion
`¬ certifiedKill h (N+L) K` follows from `¬ certifiedKill h N (L+K)` by the same
`AngleA3` endpoint transfer FreeWalk3 uses). -/
#check @ErdosProblems.Half.FreeWalk2.consecutiveFail_iff
#print axioms ErdosProblems.Half.FreeWalk2.consecutiveFail_iff

/-- FreeWalk2 already has kernel-checked runs of 13, 17 and 19 at depths that
clear the depth floor, each terminated by an explicit certificate.  FreeWalk3's
§4 "run of seven" is strictly weaker, and its unverified prose witness
(`h = 6`, `N = 125384`, `L = 21`) was declined on the grounds that `decide`
cannot handle six-digit totients — while FreeWalk2 discharges depth `32` at
`N = 4518` with `decide +kernel`. -/
theorem freeWalk2_already_has_nineteen :
    ErdosProblems.Half.FreeWalk2.ConsecutiveFail 22 4518 14 18 :=
  ErdosProblems.Half.FreeWalk2.freeWalk_run_19

#print axioms ErdosProblems.Half.FreeWalk2.no_small_absolute_run_bound

/-! FreeWalk1 already proves the headline negative of FreeWalk3's §6–§7, and
proves it against the *sharp* two-sided budget `2−(N+L) ≤ δ ≤ (N+h+L)−2` rather
than the crude `|δ| ≤ N+h+L+1`.  `trap_interior` is FreeWalk3's
`failure_zone_step_invariant` — the same `δ = −c` trick — but inside
`AdmissibleRun`, which actually carries the recurrence and the budget. -/
#check @ErdosProblems.Half.FreeWalk1.trap_interior
#check @ErdosProblems.Half.FreeWalk1.no_absolute_bound_on_consecutive_failures
#print axioms ErdosProblems.Half.FreeWalk1.no_absolute_bound_on_consecutive_failures

/-! ## 7. Probe: FreeWalk3's §7 premise is false about this corpus

§7 asserts "the only arithmetic the certificate machinery takes from `φ` is
`0 ≤ φ(n) ≤ n`".  FreeWalk1, in the same directory, derives its step budget from
`Nat.totient_lt` (`φ n < n` for `n > 1`) and `two_le_totient` (`2 ≤ φ n` for
`n ≥ 3`).  The surrogate `evenFloor` fails both: `evenFloor 4 = 4` and
`evenFloor 1 = 0`.  So `evenFloor` does *not* satisfy every property of `φ` the
corpus's own free-walk analysis consumes, and the §7 no-go is a barrier only
against arguments restricted to the crude size bound. -/
theorem evenFloor_fails_totient_lt :
    ErdosProblems.Half.FreeWalk3.evenFloor 4 = 4 ∧ Nat.totient 4 < 4 := by
  constructor
  · decide
  · decide

theorem evenFloor_fails_two_le :
    ErdosProblems.Half.FreeWalk3.evenFloor 1 = 0 ∧ 2 ≤ Nat.totient 3 := by
  constructor
  · decide
  · decide

#check @ErdosProblems.Half.FreeWalk1.two_le_totient

/-! ## 8. Probe: `windowDiscrepancy_slide_emod` is an existing corpus lemma

FreeWalk3's §1 corollary is `ErdosProblems.Lift.AngleA2.windowDiscrepancy_emod_truncate`
with its arguments permuted, re-proved from scratch and uncited.  The one-line
derivation below is the whole distance between them. -/
theorem slide_emod_is_angleA2_truncate (h N k L : ℕ) :
    windowDiscrepancy h N (k + L) % 2 ^ L = windowDiscrepancy h (N + k) L % 2 ^ L := by
  rw [show k + L = L + k from Nat.add_comm k L]
  exact ErdosProblems.Lift.AngleA2.windowDiscrepancy_emod_truncate h k N L

#check @ErdosProblems.Lift.AngleA2.windowDiscrepancy_emod_truncate

end FreeWalk3Verify
