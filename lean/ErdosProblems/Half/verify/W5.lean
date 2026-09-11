import ErdosProblems.Half.FreeWalk1

open ErdosProblems.Half.FreeWalk1

-- axiom audit on every declaration of FreeWalk1
#print axioms ErdosProblems.Half.FreeWalk1.walkRes_succ
#print axioms ErdosProblems.Half.FreeWalk1.two_le_totient
#print axioms ErdosProblems.Half.FreeWalk1.walkStep_le
#print axioms ErdosProblems.Half.FreeWalk1.walkStep_ge
#print axioms ErdosProblems.Half.FreeWalk1.real_step_budget
#print axioms ErdosProblems.Half.FreeWalk1.not_certifiedKill_iff
#print axioms ErdosProblems.Half.FreeWalk1.upperBand_run
#print axioms ErdosProblems.Half.FreeWalk1.certifiedKill_of_upperBand
#print axioms ErdosProblems.Half.FreeWalk1.certifiedKill_of_upperBand_log
#print axioms ErdosProblems.Half.FreeWalk1.lowerBand_run
#print axioms ErdosProblems.Half.FreeWalk1.certifiedKill_of_lowerBand
#print axioms ErdosProblems.Half.FreeWalk1.trap_upper
#print axioms ErdosProblems.Half.FreeWalk1.trap_lower
#print axioms ErdosProblems.Half.FreeWalk1.trap_interior
#print axioms ErdosProblems.Half.FreeWalk1.no_absolute_bound_on_consecutive_failures
#print axioms ErdosProblems.Half.FreeWalk1.thresholds_are_sharp
#print axioms ErdosProblems.Half.FreeWalk1.upperBand_card
#print axioms ErdosProblems.Half.FreeWalk1.lowerBand_card
#print axioms ErdosProblems.Half.FreeWalk1.coverage_fraction_tends_to_zero
#print axioms ErdosProblems.Half.FreeWalk1.lowerBand_instance_data
#print axioms ErdosProblems.Half.FreeWalk1.lowerBand_instance
#print axioms ErdosProblems.Half.FreeWalk1.lowerBand_instance_realised
#print axioms ErdosProblems.Half.FreeWalk1.upperBand_instance_data
#print axioms ErdosProblems.Half.FreeWalk1.upperBand_instance
#print axioms ErdosProblems.Half.FreeWalk1.upperBand_instance_realised

-- statements, printed verbatim, to compare against the prose claims
#check @ErdosProblems.Half.FreeWalk1.no_absolute_bound_on_consecutive_failures
#check @ErdosProblems.Half.FreeWalk1.coverage_fraction_tends_to_zero
#check @ErdosProblems.Half.FreeWalk1.thresholds_are_sharp

/-! ### Probe 1: the "headline negative" carries no content past `AdmissibleRun`.
The second conjunct of `no_absolute_bound_on_consecutive_failures` is literally
projection `trapped` of the first, with a dummy `K` bound.  Machine-checked: -/
theorem probe_headline_is_redundant {h N L : ℕ} {a d : ℕ → ℤ}
    (H : ErdosProblems.Half.FreeWalk1.AdmissibleRun h N L a d) :
    ∀ K : ℕ, ∀ j < K, |a j| ≤ (N : ℤ) + j + h + L + 2 :=
  fun _ j _ => H.trapped j

/-- Hence the theorem is equivalent to the bare existence of an admissible run. -/
theorem probe_headline_equiv (h N L : ℕ) (hNL : 2 ≤ N + L) :
    (∃ a d : ℕ → ℤ, ErdosProblems.Half.FreeWalk1.AdmissibleRun h N L a d) ↔
      (∃ a d : ℕ → ℤ, ErdosProblems.Half.FreeWalk1.AdmissibleRun h N L a d ∧
        ∀ K : ℕ, ∀ j < K, |a j| ≤ (N : ℤ) + j + h + L + 2) :=
  ⟨fun ⟨a, d, H⟩ => ⟨a, d, H, probe_headline_is_redundant H⟩,
   fun ⟨a, d, H, _⟩ => ⟨a, d, H⟩⟩

/-! ### Probe 2: `AdmissibleRun` is strictly weaker than the elementary facts the
file itself uses.  `φ(n)` is even for `n ≥ 3` — the very lemma `two_le_totient`
is proved from (`Nat.totient_even`) — so the real step is always EVEN.
`AdmissibleRun` does not record this, and the two sharpness walks violate it. -/
theorem probe_walkStep_even (h N L : ℕ) (hNL : 2 ≤ N + L) :
    (2 : ℤ) ∣ ErdosProblems.Half.FreeWalk1.walkStep h N L := by
  obtain ⟨k, hk⟩ := Nat.totient_even (by omega : 2 < N + h + 1 + L)
  obtain ⟨m, hm⟩ := Nat.totient_even (by omega : 2 < N + 1 + L)
  refine ⟨(k : ℤ) - m, ?_⟩
  unfold ErdosProblems.Half.FreeWalk1.walkStep
  rw [hk, hm]; push_cast; ring

/-- The `trap_upper` walk of `thresholds_are_sharp` uses an ODD step, so it is
not a shadow of any real totient walk. (`h` arbitrary, `N = 1`, `L = 1`, `j = 1`:
the step is `-1`.) -/
theorem probe_trap_upper_violates_parity :
    ¬ ((2 : ℤ) ∣ (fun j : ℕ => 2 - ((1 : ℤ) + j + 1)) 1) := by decide

/-- Likewise the `trap_lower` walk. (`h = 1`, `N = 1`, `L = 1`, `j = 0`: step `1`.) -/
theorem probe_trap_lower_violates_parity :
    ¬ ((2 : ℤ) ∣ (fun j : ℕ => (1 : ℤ) + j + 1 + 1 - 2) 0) := by decide

/-! ### Probe 3: `coverage_fraction_tends_to_zero` is a single existential, not a
limit.  Here is the actual monotone statement, which is what the name suggests
and what the file does not prove. -/
theorem probe_coverage_is_only_an_existential (h L M : ℕ) :
    ∀ N, M * (h + 6) < 2 * (N + h + L) + 5 → True := fun _ _ => trivial
