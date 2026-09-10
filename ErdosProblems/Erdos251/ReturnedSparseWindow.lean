import ErdosProblems.Erdos251.PaperSparseCouplingR7

/-! Extended block-window bound from the R10 #251 supplement.
Reuses the existing finite incidence theorem. No asymptotic supplier is assumed. -/

namespace ErdosProblems.Erdos251.PaperR7

noncomputable def extendedSupport (S : Finset ℕ) (X m : ℕ) : Finset ℕ :=
  S.filter (fun t => X ≤ t ∧ t < 2 * X + m)

theorem affected_eq_extended (S : Finset ℕ) (X m : ℕ) :
    affectedStarts (Finset.Ico X (2 * X)) S m =
      affectedStarts (Finset.Ico X (2 * X)) (extendedSupport S X m) m := by
  classical
  ext n
  simp only [affectedStarts, extendedSupport, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨hn, j, hj, hS⟩
    refine ⟨hn, j, hj, hS, ?_, ?_⟩
    · omega
    · have hjm := Finset.mem_range.mp hj
      omega
  · rintro ⟨hn, j, hj, hS, _, _⟩
    exact ⟨hn, j, hj, hS⟩

theorem card_affected_window_le (S : Finset ℕ) (X m : ℕ) :
    (affectedStarts (Finset.Ico X (2 * X)) S m).card ≤
      m * (extendedSupport S X m).card := by
  rw [affected_eq_extended]
  exact affectedStarts_card_le _ _ _


end ErdosProblems.Erdos251.PaperR7
