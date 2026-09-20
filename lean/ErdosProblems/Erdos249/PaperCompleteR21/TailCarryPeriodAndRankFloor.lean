import Erdos249257.TotientTailCarryPeriod
import Erdos249257.TotientCarryKernelRigidity

/-! Paper-form restatements of the carry-period block of the long #249
manuscript: carry displacement versus tail integrality (`prop:CP-01-inv`),
the consequence of rationality and its limitation (`prop:CP-02`), and the
rank floor together with the shape a contradicting ceiling would need to have
(`prop:D5cons`). -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open Erdos249257
open Erdos249257.TotientTailPeriodKiller

/-! ### `prop:CP-01-inv` -- carry displacement and tail integrality -/

/-- **Carry displacement and tail integrality** (`prop:CP-01-inv`).
For a positive integer `v` and a tempered integral totient carry `u`,
`v ∣ u(N+k) - u(N) ↔ R_{N+k} - R_N ∈ ℤ`.  This is a divisibility test for
that displacement, not a dimension bound for the carry sections. -/
theorem carryShift_dvd_iff_tailDiff_integral {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    (v : ℤ) ∣ u (N + k) - u N
      ↔ ∃ z : ℤ, (z : ℝ) = totientTail (N + k) - totientTail N := by
  rw [carryShift_dvd_iff_tailDiff_mem_int hv hu N k]
  exact Set.mem_range

/-! ### `prop:CP-02` -- a consequence of rationality and its limitation -/

/-- **A consequence of rationality and its limitation** (`prop:CP-02`).
If `S ∈ ℚ`, there are a positive integer `v` and a tempered integer carry
orbit `u` whose retained sections through every level `e` have rational rank
at least `2^e-1`, while those same sections are uniformly eventually periodic
modulo `v`.  Periodicity after reduction modulo `v` is a statement in a finite
quotient; it is not a rank upper bound over `ℚ`. -/
theorem rationality_forces_mod_period_and_unbounded_rank
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ, 2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u := by
  refine not_irrational_totientSeries_implies_mod_period_and_unbounded_rank ?_
  rwa [binaryCoeffSeries_totient_eq]

/-! ### `prop:D5cons` -- the lower bound and a proposed upper bound -/

/-- **The lower bound and a false proposed upper bound** (`prop:D5cons`),
proved part.

(a) the canonical dyadic totient-kernel family is unconditionally
`(2^e+1)`-dimensional at every level `e ≥ 1`;

(b) rationality of `S` forces an associated tempered carry orbit with
`ℚ`-rank at least `2^e-1` at every level;

(c) consequently a bound `g` that applies to the actual carry under the
hypothetical rationality of `S` and satisfies `g(e) < 2^e-1` at some level
`e ≥ 1` already contradicts the lower bound, hence forces irrationality.  A
bound that merely grows with `e` need not contradict anything; nothing here
supplies such a `g`. -/
theorem canonicalKernel_rank_floor_and_ceiling_consequence :
    (∀ e : ℕ, 1 ≤ e →
        Module.finrank ℚ
            (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)))
          = 2 ^ e + 1)
      ∧ (¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) →
          ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
            IsTemperedBinaryOrbit Nat.totient v u ∧
              ∀ e : ℕ, 2 ^ e - 1 ≤
                Module.finrank ℚ
                  (Submodule.span ℚ
                    (Set.range (canonicalCarryKernelFamily u e))))
      ∧ (∀ g : ℕ → ℕ,
          (∀ v : ℕ, ∀ u : ℕ → ℤ, 0 < v →
              IsTemperedBinaryOrbit Nat.totient v u →
              ∀ e : ℕ,
                Module.finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e)))
                  ≤ g e) →
          (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1) →
          Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := by
  refine ⟨fun e he => finrank_totientKernelThroughLevelFamily_eq e he, ?_, ?_⟩
  · intro hrat
    refine not_irrational_totientSeries_implies_unbounded_carryRank_unconditional ?_
    rwa [binaryCoeffSeries_totient_eq]
  · intro g hg hex
    obtain ⟨e, he, hlt⟩ := hex
    by_contra hnot
    obtain ⟨v, hv, u, hu, hrank⟩ :=
      not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
        (by rwa [binaryCoeffSeries_totient_eq])
    have h1 := hrank e
    have h2 := hg v u hv hu e
    omega

#print axioms carryShift_dvd_iff_tailDiff_integral
#print axioms rationality_forces_mod_period_and_unbounded_rank
#print axioms canonicalKernel_rank_floor_and_ceiling_consequence
end ErdosProblems.Erdos249.PaperCompleteR21
