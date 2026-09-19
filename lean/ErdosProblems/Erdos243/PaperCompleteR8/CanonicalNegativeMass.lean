import ErdosProblems.Erdos243.PaperCompleteR7.Frontier

/-!
# Finite negative mass on the actual reciprocal-tail state

The canonical rational-tail construction supplies
positivity and exact dynamics. The scalar finite-mass theorem needs neither
quadratic growth nor a separately supplied normalized-vanishing hypothesis.
Summability of the displayed negative mass remains an explicit assumption.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR8

open PaperCompleteR7

/-- Finite normalized negative mass on the canonical rational-tail state forces
an eventual Sylvester recurrence. The original growth hypothesis is unnecessary
for this implication; this theorem does not establish the mass hypothesis. -/
theorem canonical_sylvester_of_finite_negative_mass
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hmass : Summable (fun n =>
      max (-(centeredState (a n : ℤ) (canonicalDenominator a q n : ℤ)
        (canonicalNaturalNumerator a p q n : ℤ) : ℝ)) 0 /
          (canonicalNaturalNumerator a p q n : ℝ))) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  obtain ⟨hCp, _hDp, hC, hD, _hrep⟩ :=
    canonical_integer_tail a hpos p q hq hs
  exact finite_negative_mass_paper.2 a
    (canonicalNaturalNumerator a p q) (canonicalDenominator a q)
    (fun n => centeredState (a n : ℤ) (canonicalDenominator a q n : ℤ)
      (canonicalNaturalNumerator a p q n : ℤ))
    hCp hC hD (fun _ => rfl) hmass

end ErdosProblems.Erdos243.PaperCompleteR8
