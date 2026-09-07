import ErdosProblems.Erdos257.GreedyRepairCriterion
import ErdosProblems.Erdos257.MersenneSubseriesRigidity
import Erdos257PeriodNoncollapse.GreedyTrapDynamics
import ErdosProblems.Erdos257.SignedFinitePeriodNoncollapse

/-!
# Complete paper-statement assemblies for Erdős 257, round 7

These are new *uncompiled proof candidates*. They assemble the displayed
conjunctions from the supplied library without adding assumptions, axioms, or
admissions. They must be elaborated against the packet's Lean 4.29.1 tree before
being counted as newly verified results. Nothing here asserts universal #257
or membership of either outstanding rational target.

The primary paper obligations are identified in the docstrings. The coverage
ledger distinguishes the existing components from these end-to-end assemblies.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR7

open scoped ENNReal

open Erdos257PeriodNoncollapse Filter MeasureTheory

/-- Short `res:period`: coprimality, exact order, and the strict denominator
bound in one statement, with precisely the extra hypothesis needed for the bound. -/
theorem short_finite_period
    (F : Finset ℕ) (b : ℕ) (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    ∃ hcop : Nat.Coprime b (finiteErdosSum F b).den,
      orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id ∧
      (2 ≤ F.lcm id → F.lcm id < (finiteErdosSum F b).den) := by
  refine ⟨coprime_base_den_finiteErdosSum F b h0 hb,
    finite_period_noncollapse_rat_den F b hF h0 hb, ?_⟩
  exact lcm_lt_den_finiteErdosSum F b hF h0 hb

/-- Short `res:general-repair`: the three displayed conditions, expressed as
both biconditionals rather than merely as an implication. -/
theorem short_general_repair (x : ℝ) (hx : 0 ≤ x) :
    (x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N) ∧
    (x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N) := by
  exact ⟨mem_iff_greedyBinaryDefect_cofinal_repairs hx,
    mem_iff_greedyBinaryDefect_sqrt_windows hx⟩

/-- Long `thm:generic-repair`: all four iff-forms and the last sentence's
one-window exclusion, with the paper's exact constant 12. -/
theorem long_general_repair (x : ℝ) (hx : 0 ≤ x) :
    (x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N) ∧
    (x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N) ∧
    (x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
        greedyBinaryDefect x N ≤ supportCoeff (greedyMersenneSupport x) (N + 1)) ∧
    (x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ greedyBinaryDefect x N ≤ N + 1) ∧
    (∀ K : ℕ,
      (∀ N : ℕ, K ≤ N → N < K + 2 * Nat.sqrt K + 12 →
        greedyBinaryDefect x N < greedyBinaryDefect x (N + 1)) →
      x ∉ mersenneAchievementSet) := by
  exact ⟨mem_iff_greedyBinaryDefect_sqrt_windows hx,
    mem_iff_greedyBinaryDefect_cofinal_repairs hx,
    mem_iff_greedyBinaryDefect_cofinal_load_bound hx,
    mem_iff_greedyBinaryDefect_cofinal_linear_bound hx,
    fun K h => not_mem_of_greedyBinaryDefect_strict_sqrt_window hx K h⟩

/-- Long `thm:scaled-greedy-trap`: recurrence, uniform trap, escape and
bounded cofinal return are assembled, not conflated. -/
theorem long_scaled_greedy_trap (x : ℝ) (hx : 0 ≤ x) :
    (∀ N : ℕ, scaledGreedyRemainder x (N + 1) =
      if mersenneScale (N + 1) ≤ 2 * scaledGreedyRemainder x N then
        2 * scaledGreedyRemainder x N - mersenneScale (N + 1)
      else 2 * scaledGreedyRemainder x N) ∧
    (x ∈ mersenneAchievementSet ↔
      ∀ N : ℕ, scaledGreedyRemainder x N < 2) ∧
    (x ∉ mersenneAchievementSet →
      Tendsto (scaledGreedyRemainder x) atTop atTop) ∧
    (x ∈ mersenneAchievementSet ↔ ScaledGreedyRemainderCofinallyBounded x) := by
  exact ⟨scaledGreedyRemainder_succ x,
    mem_mersenneAchievementSet_iff_forall_scaledRemainder_lt_two hx,
    scaledGreedyRemainder_tendsto_atTop_of_not_mem hx,
    mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded hx⟩

/-- Long `thm:rational-membership`: both advertised equivalences. The forward
implication's rationality assumption is retained. -/
theorem long_rational_membership (q : ℚ) (hq : 0 ≤ q) :
    ((q : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (q : ℝ)).Infinite) ∧
    ((q : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
        ¬ mersenneWeight (n + 1) ≤ greedyMersenneRemainder (q : ℝ) n) := by
  exact ⟨rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite q hq,
    rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips q hq⟩

/-- Exact geometric clauses of long `thm:geometry`, `thm:topology`, and
`prop:achievement-set-topology`. No decimal approximation or general-weight
measure claim is asserted by this theorem. -/
theorem long_achievement_geometry :
    IsCompact mersenneAchievementSet ∧
    IsClosed mersenneAchievementSet ∧
    Perfect mersenneAchievementSet ∧
    IsTotallyDisconnected mersenneAchievementSet ∧
    IsNowhereDense mersenneAchievementSet ∧
    volume mersenneAchievementSet = 1 ∧
    Function.Injective positiveMersenneDigitValue ∧
    Set.range positiveMersenneDigitValue = mersenneAchievementSet := by
  exact ⟨isCompact_mersenneAchievementSet,
    isClosed_mersenneAchievementSet,
    perfect_mersenneAchievementSet,
    isTotallyDisconnected_mersenneAchievementSet,
    isNowhereDense_mersenneAchievementSet,
    volume_mersenneAchievementSet,
    positiveMersenneDigitValue_injective,
    range_positiveMersenneDigitValue_eq⟩

/-- Long `thm:supported-dichotomy`: the exact volume alternatives, injectivity
and infinitude-conditioned perfectness, together. -/
theorem long_supported_dichotomy (J : Set ℕ) :
    ((∃ F : Finset ℕ, J = (↑F : Set ℕ)ᶜ ∧
       volume (supportedMersenneAchievementSet J) = ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0)) ∧
    Function.Injective (supportedMersenneDigitValue J) ∧
    (J.Infinite → Perfect (supportedMersenneAchievementSet J)) := by
  exact ⟨volume_supportedMersenneAchievementSet_dichotomy J,
    supportedMersenneDigitValue_injective J,
    fun hJ => perfect_supportedMersenneAchievementSet hJ⟩

/-- Long `thm:tempered-orbit-rigidity`: rationality equivalence, exact analytic
identification and uniqueness for a fixed multiplier. Positivity alone is not
substituted for temperedness. -/
theorem long_tempered_orbit_rigidity (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) :
    (HasRationalValue (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u) ∧
    (∀ (v : ℕ) (u : ℕ → ℤ), IsTemperedBinaryOrbit c v u →
      ∀ N, (u N : ℝ) = (v : ℝ) * binaryCoeffTail c N) ∧
    (∀ (v : ℕ) (u w : ℕ → ℤ),
      IsTemperedBinaryOrbit c v u → IsTemperedBinaryOrbit c v w → u = w) := by
  refine ⟨binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit c hc, ?_, ?_⟩
  · intro v u hu
    exact temperedBinaryOrbit_eq_scaledTail c hc hu
  · intro v u w hu hw
    funext N
    have huN := temperedBinaryOrbit_eq_scaledTail c hc hu N
    have hwN := temperedBinaryOrbit_eq_scaledTail c hc hw N
    have hcast : (u N : ℝ) = (w N : ℝ) := huN.trans hwN.symm
    exact_mod_cast hcast

/-- Long `lem:tail-transfer`, first with explicit eventual agreement. This
closes the reverse-prefix assembly absent from the cited one-way tail lemma. -/
theorem irrational_support_of_eventual_agreement
    (b : ℕ) (hb : 2 ≤ b) (A B : Set ℕ) (K : ℕ)
    (hAB : ∀ n, K < n → (n ∈ A ↔ n ∈ B))
    (hA : Irrational (erdosSupportSeries b A)) :
    Irrational (erdosSupportSeries b B) := by
  have ht := irrational_erdosSupportSeries_tail_of_irrational b A hb K hA
  have heq : {n : ℕ | n ∈ A ∧ K < n} = {n : ℕ | n ∈ B ∧ K < n} := by
    ext n
    constructor
    · rintro ⟨hnA, hn⟩
      exact ⟨(hAB n hn).1 hnA, hn⟩
    · rintro ⟨hnB, hn⟩
      exact ⟨(hAB n hn).2 hnB, hn⟩
  rw [heq] at ht
  exact irrational_erdosSupportSeries_of_tail b B hb K ht

/-- Long `lem:tail-transfer`: the complete finite symmetric-difference iff.
The union of the two differences is the symmetric difference. -/
theorem long_finite_symmetric_difference
    (b : ℕ) (hb : 2 ≤ b) (A B : Set ℕ)
    (hfin : ((A \ B) ∪ (B \ A)).Finite) :
    Irrational (erdosSupportSeries b A) ↔ Irrational (erdosSupportSeries b B) := by
  classical
  obtain ⟨K, hK⟩ := hfin.bddAbove
  have heq : ∀ n, K < n → (n ∈ A ↔ n ∈ B) := by
    intro n hn
    constructor
    · intro hA
      by_contra hB
      have hmem : n ∈ (A \ B) ∪ (B \ A) := Or.inl ⟨hA, hB⟩
      exact (not_le_of_gt hn) (hK hmem)
    · intro hB
      by_contra hA
      have hmem : n ∈ (A \ B) ∪ (B \ A) := Or.inr ⟨hB, hA⟩
      exact (not_le_of_gt hn) (hK hmem)
  exact ⟨irrational_support_of_eventual_agreement b hb A B K heq,
    irrational_support_of_eventual_agreement b hb B A K
      (fun n hn => (heq n hn).symm)⟩

/-- The signed unit-coefficient extension stated in the short note's finite
period section, including the large-lcm denominator bound. -/
theorem signed_period_with_bound
    (F : Finset ℕ) (ε : ℕ → ℤ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hε : ∀ n ∈ F, ε n = 1 ∨ ε n = -1) :
    signedFiniteErdosSum F ε b ≠ 0 ∧
    (∃ hcop : Nat.Coprime b (signedFiniteErdosSum F ε b).den,
      orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id) ∧
    (2 ≤ F.lcm id → F.lcm id < (signedFiniteErdosSum F ε b).den) := by
  obtain ⟨hne, hord⟩ := signed_finite_period_noncollapse F ε b hF h0 hb hε
  exact ⟨hne, ⟨coprime_base_signedFiniteErdosSum F ε b h0 hb hε, hord⟩,
    lcm_lt_den_signedFiniteErdosSum F ε b hF h0 hb hε⟩

end ErdosProblems.Erdos257.PaperCompleteR7

end
