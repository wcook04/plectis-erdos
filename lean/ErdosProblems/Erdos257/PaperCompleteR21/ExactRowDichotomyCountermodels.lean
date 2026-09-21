import Erdos249257.BooleanMobiusExactRowDichotomy
import Erdos249257.BooleanMobiusCriticalCapacityCofinal

/-!
Paper-form restatements of five environments of the long Erdős #257 manuscript
`paper/reasoning-parts/erdos257/a257_front.tex`:

* `record:257bm-k1`   (line 5077), "A bounded model of the doubling-or-return
  alternative";
* `record:257bm-k-dich` (line 5096), "Doubling or returning to an earlier
  depth";
* `record:257bm-k2`   (line 5118), "A sufficient fractional-mass bound need not
  hold";
* `record:257bm-k4`   (line 5158), "The returning endpoint need not be larger";
* `record:257rig-k6`  (line 5188), "Uniqueness at a critical crossing".

Every quantity is the paper's: `X_D(2)` is `localMersennePrefixValue D`,
`S(D,1,M)` is `localBinarySuffix D 1 M`, the combined fractional mass
`∑_{d∈D} (2^M mod (2^d-1))/(2^d-1)` is `localFractionMass D M`, the crossing
weight `w(c)` is `mersenneWeightRat c`, and `G` is the real half-greedy
support `greedyMersenneSupport (1/2)`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257

/-! ## `record:257bm-k-dich`: doubling or returning to an earlier depth -/

/-- Long `record:257bm-k-dich`, main clause.  For `n ≥ 6`, an exact row at `n`
has at least one of the two asserted continuations; the returned depth
`2c - 2` is not claimed to exceed `n`. -/
theorem paper_exact_row_double_or_recycle {n : ℕ} (hn : 6 ≤ n)
    (hrow : ExactLocalMersenneHalfRow n) :
    ExactLocalMersenneHalfRow (2 * n - 1) ∨
      ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2) :=
  exactLocalMersenneHalfRow_double_or_recycle hn hrow

/-- Long `record:257bm-k-dich`, parity clause: a finite Mersenne value cannot
equal `1/2`, because its reduced denominator is odd. -/
theorem paper_finite_row_value_ne_half {D : Finset ℕ} (h0 : 0 ∉ D) :
    localMersennePrefixValue D ≠ (1 / 2 : ℚ) := by
  intro heq
  have hodd := finiteErdosSum_den_odd D h0
  rw [← localMersennePrefixValue_eq_finiteErdosSum, heq] at hodd
  obtain ⟨k, hk⟩ := hodd
  norm_num at hk
  omega

/-- Long `record:257bm-k-dich`, the worked example at `n = 6`.  The support
`{2,3,6}` is an exact row at depth `6`; `{2,3,6,7,11}` is an exact row at
depth `11 = 2·6 - 1`; and the second conclusion also holds with `c = 4`, whose
returned depth `2c - 2 = 6` is exactly the original depth, so it allows no
depth increase. -/
theorem paper_exact_row_example_six_and_eleven :
    localPrefixQuotient ({2, 3, 6} : Finset ℕ) 6 = 2 ^ (6 - 1) - 1 ∧
      ExactLocalMersenneHalfRow 6 ∧
      localPrefixQuotient ({2, 3, 6, 7, 11} : Finset ℕ) 11 = 2 ^ (11 - 1) - 1 ∧
      ExactLocalMersenneHalfRow (2 * 6 - 1) ∧
      (4 ≤ 4 ∧ 4 ≤ 6 ∧ ExactLocalMersenneHalfRow (2 * 4 - 2)) ∧
      2 * 4 - 2 = 6 := by
  have hsix : localPrefixQuotient ({2, 3, 6} : Finset ℕ) 6 = 2 ^ (6 - 1) - 1 := by
    decide
  have heleven :
      localPrefixQuotient ({2, 3, 6, 7, 11} : Finset ℕ) 11 = 2 ^ (11 - 1) - 1 := by
    decide
  have hrow6 : ExactLocalMersenneHalfRow 6 :=
    ⟨({2, 3, 6} : Finset ℕ), by decide, hsix⟩
  have hrow11 : ExactLocalMersenneHalfRow 11 :=
    ⟨({2, 3, 6, 7, 11} : Finset ℕ), by decide, heleven⟩
  refine ⟨hsix, hrow6, heleven, ?_, ⟨le_rfl, by omega, ?_⟩, by omega⟩
  · simpa using hrow11
  · simpa using hrow6

/-! ## `record:257bm-k1`: a bounded model of the doubling-or-return
alternative -/

/-- Long `record:257bm-k1`.  The predicate `n = 6` satisfies exactly the same
two-branch transition shape as the dichotomy above (seed at `6`, and the
transition always takes the recycle branch with `c = 4`, whose conclusion is
back at `2·4 - 2 = 6`), yet it is not cofinal: it is only ever true at
`n = 6`.  Hence the transition shape together with an endpoint-six seed is
logically insufficient for cofinal exact rows. -/
theorem paper_bounded_double_or_recycle_countermodel :
    (∀ n : ℕ, boundedDoubleOrRecycleModel n ↔ n = 6) ∧
      boundedDoubleOrRecycleModel 6 ∧
      (∀ n : ℕ, 6 ≤ n → boundedDoubleOrRecycleModel n →
        boundedDoubleOrRecycleModel (2 * n - 1) ∨
          ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ boundedDoubleOrRecycleModel (2 * c - 2)) ∧
      (∀ n : ℕ, 6 ≤ n → boundedDoubleOrRecycleModel n →
        4 ≤ 4 ∧ 4 ≤ n ∧ boundedDoubleOrRecycleModel (2 * 4 - 2)) ∧
      ¬ (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ boundedDoubleOrRecycleModel n) := by
  refine ⟨fun n => Iff.rfl, boundedDoubleOrRecycleModel_seed,
    fun n hn hmodel => boundedDoubleOrRecycleModel_transition hn hmodel, ?_,
    boundedDoubleOrRecycleModel_not_cofinal⟩
  intro n hn hmodel
  have hn6 : n = 6 := hmodel
  subst hn6
  exact ⟨le_rfl, by omega, by unfold boundedDoubleOrRecycleModel; omega⟩

/-- Long `record:257bm-k1`, the existential packaging. -/
theorem paper_exists_seeded_bounded_double_or_recycle_model :
    ∃ P : ℕ → Prop,
      P 6 ∧
        (∀ n : ℕ, 6 ≤ n → P n →
          P (2 * n - 1) ∨ ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ P (2 * c - 2)) ∧
        ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n :=
  exists_seeded_bounded_double_or_recycle_model

/-! ## `record:257bm-k2`: a sufficient fractional-mass bound need not hold -/

/-- Long `record:257bm-k2`, exact arithmetic at `D = {2,3}`, `c = 5`.  Direct
calculation gives `X_D(2) = 10/21 < 1/2 < 331/651 = X_{D∪{5}}(2)` and
`S(D,1,8) = 6 < 8`, while the combined fractional mass at depth `8` is
`757/651 > 1`.  So the one-unit fractional-mass bound, which suffices for the
sharp capacity estimate, is not necessary for it, and it cannot hold at every
real crossing core. -/
theorem paper_fractional_mass_bound_not_necessary :
    localMersennePrefixValue ({2, 3} : Finset ℕ) = 10 / 21 ∧
      localMersennePrefixValue ({2, 3} : Finset ℕ) < (1 / 2 : ℚ) ∧
      localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) = 331 / 651 ∧
      (1 / 2 : ℚ) < localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 = 6 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 8 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 2 ^ (5 - 2) ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 = 757 / 651 ∧
      1 < localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 =
        localFractionMass ({2, 3} : Finset ℕ) 8 + localMersenneFraction 8 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [localMersennePrefixValue, mersenneWeightRat, localFractionMass,
      localMersenneFraction, localBinarySuffix, localPrefixQuotient,
      localMersenneQuotient]

/-- Long `record:257bm-k2`, the sufficiency being tested: a combined
fractional mass at most one does give the sharp capacity estimate at a genuine
crossing.  The fixture above shows this sufficient condition is not
necessary. -/
theorem paper_fractional_mass_bound_suffices_for_sharp_capacity
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) < localMersennePrefixValue (insert c D))
    (hfrac : localFractionMass (insert c D) (2 * c - 2) ≤ 1) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) := by
  classical
  have hcNotD : c ∉ D := by
    intro hcD
    have := (hD c hcD).2
    omega
  have hmass : localFractionMass (insert c D) (2 * c - 2) =
      localMersenneFraction (2 * c - 2) c +
        localFractionMass D (2 * c - 2) := by
    unfold localFractionMass
    rw [Finset.sum_insert hcNotD]
  rw [hmass] at hfrac
  exact localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_of_splitFractionMass
    hc hD hbelow hcross (by linarith)

/-! ## `record:257bm-k4`: the returning endpoint need not be larger -/

/-- Long `record:257bm-k4`, first clause: the recycling theorem is
unconditional, but its witness satisfies `c ≤ n`. -/
theorem paper_skipped_core_recycling_witness_bounded
    {E : Finset ℕ} {n : ℕ} (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2) :=
  exists_skippedCoreExactRow_of_value_above hE habove

/-- Long `record:257bm-k4`, second clause: `2c - 2` may be at most `n`, so the
endpoint need not grow.  At `n = 6` the recycled depth `2·4 - 2 = 6` is the
original depth. -/
theorem paper_returning_endpoint_may_fail_to_grow :
    ∃ n c : ℕ, 4 ≤ c ∧ c ≤ n ∧ 2 * c - 2 ≤ n ∧
      ExactLocalMersenneHalfRow (2 * c - 2) := by
  refine ⟨6, 4, le_rfl, by omega, by omega, ?_⟩
  have hrow6 : ExactLocalMersenneHalfRow 6 :=
    ⟨({2, 3, 6} : Finset ℕ), by decide, by decide⟩
  simpa using hrow6

/-- Long `record:257bm-k4`, fourth clause: inside a protected exact row the
two invariants `endpoint < 2·cutoff` and `new_above_cutoff` do force strict
endpoint progress.  First half: a first crossing rank `e` of a protected row
lies strictly beyond the cutoff. -/
theorem paper_protected_row_crossing_beyond_cutoff
    (s : ProtectedExactLocalMersenneRow) {e : ℕ} (heSupport : e ∈ s.support)
    (heCross : (1 / 2 : ℚ) <
      localMersennePrefixValue (insert e (s.support.filter fun d => d < e))) :
    s.cutoff < e := by
  classical
  by_contra hnot
  have heLe : e ≤ s.cutoff := by omega
  have hFsub : insert e (s.support.filter fun d => d < e) ⊆ s.core := by
    intro d hdF
    simp only [Finset.mem_insert, Finset.mem_filter] at hdF
    rcases hdF with hdeq | ⟨hdSupport, hde⟩
    · have heCore : e ∈ s.core := by
        by_contra heNotCore
        have := s.new_above_cutoff e heSupport heNotCore
        omega
      simpa [hdeq] using heCore
    · by_contra hdCore
      have := s.new_above_cutoff d hdSupport hdCore
      omega
  have hFle :
      localMersennePrefixValue (insert e (s.support.filter fun d => d < e)) ≤
        localMersennePrefixValue s.core := by
    unfold localMersennePrefixValue
    apply Finset.sum_le_sum_of_subset_of_nonneg hFsub
    intro d hdCore _hdF
    have hdTwo : 2 ≤ d := (s.core_bounds d hdCore).1
    exact (mersenneWeightRat_pos (n := d) (by omega)).le
  have hcoreBelow := s.core_below_half
  linarith

/-- Long `record:257bm-k4`, fourth clause, second half: `cutoff < c` together
with `endpoint < 2·cutoff` forces `endpoint < 2c - 2`, that is, strict
endpoint progress. -/
theorem paper_protected_row_endpoint_growth
    (s : ProtectedExactLocalMersenneRow) {c : ℕ} (hc : s.cutoff < c) :
    s.endpoint < 2 * c - 2 := by
  have h1 := s.endpoint_lt_twice_cutoff
  have h2 := s.cutoff_four
  omega

/-! ## `record:257rig-k6`: uniqueness at a critical crossing -/

/-- Long `record:257rig-k6`.  For `c ≥ 4`, a support `D` inside `[2,c)` that is
below one half with genuine crossing deficit `1/2 - X_D(2) < w(c)` is exactly
the canonical half-greedy prefix through `c - 1`; equivalently
`D = G ∩ {1,…,c-1}`, so the support is fixed by `c`. -/
theorem paper_critical_crossing_support_is_greedy_prefix
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c) :
    D = halfGreedyPrefixSupport (c - 1) ∧
      (↑D : Set ℕ) = greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Iic (c - 1) := by
  have h1 := eq_halfGreedyPrefixSupport_of_critical_crossing hc hD hbelow hcross
  refine ⟨h1, ?_⟩
  have h2 : primitivePrefix (greedyMersenneSupport (1 / 2 : ℝ)) (c - 1) =
      (↑(halfGreedyPrefixSupport (c - 1)) : Set ℕ) := by
    simpa [halfGreedyPrefixSupport] using
      (primitivePrefix_greedyMersenneSupport_eq_prefixRat (1 / 2 : ℚ) (c - 1))
  rw [h1, ← h2]
  rfl

#print axioms paper_exact_row_double_or_recycle
#print axioms paper_finite_row_value_ne_half
#print axioms paper_exact_row_example_six_and_eleven
#print axioms paper_bounded_double_or_recycle_countermodel
#print axioms paper_exists_seeded_bounded_double_or_recycle_model
#print axioms paper_fractional_mass_bound_not_necessary
#print axioms paper_skipped_core_recycling_witness_bounded
#print axioms paper_returning_endpoint_may_fail_to_grow
#print axioms paper_protected_row_crossing_beyond_cutoff
#print axioms paper_protected_row_endpoint_growth
#print axioms paper_critical_crossing_support_is_greedy_prefix

end ErdosProblems.Erdos257.PaperCompleteR21
