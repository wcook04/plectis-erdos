import ErdosProblems.Skip.D6
import ErdosProblems.Skip.Wire1

/-!
Adversarial verification scratch file for `ErdosProblems/Skip/D6.lean`.
Nothing here is a contribution; it is an audit.
-/

namespace Erdos249257

namespace SkipD6

#print axioms largestSkipLateAt_of_lateSkip
#print axioms lateSkip_of_largestSkipLateAt
#print axioms seamGreedyUnboundedSkippedRanksAlong_of_unboundedSkip
#print axioms half_mem_of_unboundedSkip
#print axioms half_mem_of_forall_lateSkip
#print axioms half_mem_of_forall_largestSkipLateAt
#print axioms half_mem_of_largestSkipLateStepSocket
#print axioms mem_cofRanksLate_iff
#print axioms halfCofactor_not_late
#print axioms halfCofactor_notMem_cofRanksLate
#print axioms cofRanks_late_or_half
#print axioms cofRanksLate_cases
#print axioms cofRanksLate_eq_empty_of_three_dvd
#print axioms cofRanksLate_subset_or_largestSkipLateAt
#print axioms cofRanks_subset_or_largestSkipLateAt
#print axioms Ico_subset_seamWordSupport_of_rightTail
#print axioms not_largestSkipLateAt_of_rightTail
#print axioms not_rightTail_of_largestSkipLateAt
#print axioms half_mem_of_cofRanksLate_cofinal_miss
#print axioms half_mem_or_eventually_late_selected
#print axioms eventually_cofRanksLate_subset_of_late_selected
#print axioms half_mem_or_eventually_allRight_landingExcess_two_impossible
#print axioms allRight_landingExcess_two_lateSkip

#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_unboundedSkippedRanks
#print axioms Erdos249257.AngleB2.allRight_landingExcess_two_impossible
#print axioms Erdos249257.seamGreedyEventuallyRight_iff_half_not_mem

/-! ### Audit A.  D6's `cofRanksLate` dichotomy is empty on a third of all rows. -/

example : cofRanksLate 63 = ∅ := cofRanksLate_eq_empty_of_three_dvd 63 (by norm_num) rfl

/-- On every row divisible by 3 the "unconditional skip dichotomy" is the left
disjunct for the trivial reason that the set is empty. -/
example (s : ℕ) (hs : 61 ≤ s) (h3 : s % 3 = 0) :
    cofRanksLate s ⊆ seamWordSupport (HalfCylinderIntegerGreedy.seamGreedyWord s) := by
  rw [cofRanksLate_eq_empty_of_three_dvd s (by omega) h3]
  exact Finset.empty_subset _

/-! ### Audit B.  Under D6's own `hright`, the positive disjunct is FALSE.
The corpus classification `seamGreedyEventuallyRight_iff_half_not_mem` predates
D6.  Every theorem in D6 that carries an all-right-tail hypothesis is therefore
operating in a regime where `1/2 ∉ mersenneAchievementSet`, so the "wave" and the
per-class late skip can never be converted into the advertised endpoint. -/

theorem audit_rightTail_kills_positive_branch
    (D : ℕ) (hD : 60 ≤ D)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      HalfCylinderIntegerGreedy.seamGreedyWord (s + 1) =
        (HalfCylinderIntegerGreedy.seamGreedyWord s).extend true) :
    (1 / 2 : ℝ) ∉ mersenneAchievementSet :=
  seamGreedyEventuallyRight_iff_half_not_mem.mp ⟨D + 1, by omega, hright⟩

/-! ### Audit C.  D6's headline is strictly weaker than a five-line consequence
of lemmas that already existed (`Wire1.allRight_landingExcess_two_impossible_of_earlyRightTail`,
itself from `AngleB2` + `seamWordSupport_add_eq_of_eventually_right`).

D6 proves

    `1/2 ∈ MAS ∨ ∃ S₀, ∀ D ≥ max 60 S₀, hright → landing = 2 → hhalfcof → False`.

The following drops BOTH remaining hypotheses — no `hright`, no half-cofactor
selection assumption — and is proved without using anything from D6. -/

theorem audit_strictly_stronger_than_D6_headline :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S₀ : ℕ, ∀ D : ℕ, 60 ≤ D → S₀ ≤ D →
        Recon257.seamExcess (D + 1) = 2 → False := by
  by_cases hmem : (1 / 2 : ℝ) ∈ mersenneAchievementSet
  · exact Or.inl hmem
  obtain ⟨S, hS5, hright⟩ := seamGreedyEventuallyRight_iff_half_not_mem.mpr hmem
  exact Or.inr ⟨2 * S, fun D hD hS₀ hlanding =>
    Wire1.allRight_landingExcess_two_impossible_of_earlyRightTail S D hS5 hD
      (by omega) hright hlanding⟩

/-- And D6's headline follows from it immediately, confirming the strict
implication direction. -/
theorem audit_D6_headline_is_a_corollary :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ S₀ : ℕ, ∀ D : ℕ, 60 ≤ D → S₀ ≤ D →
        (∀ s : ℕ, D + 1 ≤ s →
          HalfCylinderIntegerGreedy.seamGreedyWord (s + 1) =
            (HalfCylinderIntegerGreedy.seamGreedyWord s).extend true) →
        Recon257.seamExcess (D + 1) = 2 →
        (∀ s : ℕ, D + 1 ≤ s → s < D + 4 →
          (s + 1) / 2 ∈ AngleB2.cofRanks s →
            (s + 1) / 2 ∈ seamWordSupport (HalfCylinderIntegerGreedy.seamGreedyWord s)) →
        False := by
  rcases audit_strictly_stronger_than_D6_headline with h | ⟨S₀, hS₀⟩
  · exact Or.inl h
  exact Or.inr ⟨S₀, fun D hD hle _ hlanding _ => hS₀ D hD hle hlanding⟩

/-! ### Audit D.  D6's per-class conclusion is already free (no `hhalfcof`)
at any producer row, by `Wire1.ratchetWindow_all_late`. -/

theorem audit_lateSkip_window_is_free
    (D : ℕ) (hD : 60 ≤ D)
    (hUM : SeamGreedyUpperOrMiddleAt D (by omega))
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      HalfCylinderIntegerGreedy.seamGreedyWord (s + 1) =
        (HalfCylinderIntegerGreedy.seamGreedyWord s).extend true) :
    ∃ s : ℕ, D + 1 ≤ s ∧ s < D + 4 ∧ LargestSkipLateAt s :=
  ⟨D + 1, le_rfl, by omega, Wire1.ratchetWindow_all_late D hD hUM hright (D + 1) le_rfl (by omega)⟩

/-! ### Audit E.  `not_rightTail_of_largestSkipLateAt` cannot consume the
witnesses the D6 docstring advertises.  The docstring claims a refutation of
`hright` at `D = 101` using a row `t = 105`; the lemma requires `3 * S ≤ 2 * s`,
i.e. `3 * 102 = 306 ≤ 2 * 105 = 210`, which is false. -/

example : ¬ (3 * 102 ≤ 2 * 105) := by norm_num

#check @not_rightTail_of_largestSkipLateAt

end SkipD6

end Erdos249257
