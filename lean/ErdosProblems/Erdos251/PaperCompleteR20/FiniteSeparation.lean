import ErdosProblems.Erdos251.PaperCompleteR20.SignedWindow

namespace ErdosProblems.Erdos251.PaperCompleteR20
open Filter Topology

theorem one_tail_signed_certificate (D D' : ℝ) (s A B Q : ℤ)
    (hs : s = -1 ∨ s = 1) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hstep : D' = 2 * D - (2 * s : ℤ))
    (herr : |(Q : ℝ) * D - A| ≤ B)
    (hlo : 2 * s * A - Q > 2 * B) (hhi : Q - s * A > B) :
    ((1/2 : ℝ) < (s : ℝ)*D ∧ (s : ℝ)*D < 1) ∧ |D'| < 1 ∧
      D ∉ Set.range ((↑) : ℤ → ℝ) ∧ D' ∉ Set.range ((↑) : ℤ → ℝ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlor : (2 : ℝ)*s*A-Q > 2*B := by exact_mod_cast hlo
  have hhir : (Q : ℝ)-s*A > B := by exact_mod_cast hhi
  obtain ⟨hel, heu⟩ := abs_le.mp herr
  have hb : (1/2 : ℝ) < (s : ℝ)*D ∧ (s : ℝ)*D < 1 := by
    rcases hs with rfl | rfl <;> norm_num at hlor hhir ⊢ <;>
      constructor <;> nlinarith
  have hc := signed_two_window_consequences D D' (2*s) s hstep hs rfl hb.1 hb.2
  have hw := (signed_two_window_iff D D' (2*s) (even_two_mul s) hstep).mpr
    ⟨s, hs, rfl, hb⟩
  exact ⟨hb, hw.2.1, hc.2⟩

theorem finite_separation_complete (D : ℝ) (S R : ℕ → ℝ)
    (hR : ∀ L, 0 ≤ R L) (herr : ∀ L, |D-S L| ≤ R L)
    (hlim : Tendsto R atTop (𝓝 0)) :
    D ∉ Set.range ((↑) : ℤ → ℝ) ↔
      ∃ L, R L < Metric.infDist (S L) (Set.range ((↑) : ℤ → ℝ)) := by
  let Z : Set ℝ := Set.range ((↑) : ℤ → ℝ)
  have hne : Z.Nonempty := ⟨0, ⟨0, by simp⟩⟩
  have hclosed : IsClosed Z := Int.isClosedEmbedding_coe_real.isClosed_range
  constructor
  · intro hD
    have hd : 0 < Metric.infDist D Z := by
      apply (Metric.infDist_pos_iff_notMem_closure hne).mp
      simpa [hclosed.closure_eq, Z] using hD
    obtain ⟨L, hL⟩ := ((tendsto_order.mp hlim).2 _ (half_pos hd)).exists
    refine ⟨L, ?_⟩
    have ht : Metric.infDist D Z ≤ Metric.infDist (S L) Z + |D-S L| := by
      simpa only [Real.dist_eq] using
        (Metric.infDist_le_infDist_add_dist (x := D) (y := S L) (s := Z))
    change R L < Metric.infDist (S L) Z
    linarith [herr L]
  · rintro ⟨L, hL⟩ ⟨z, hz⟩
    have ht := Metric.infDist_le_dist_of_mem (x := S L) (s := Set.range ((↑) : ℤ → ℝ)) (Set.mem_range_self z)
    rw [hz, Real.dist_eq, abs_sub_comm] at ht
    linarith [herr L]

/-- The exact integer margins printed next to the one-tail example. -/
theorem one_tail_example_margins :
    (2 * (-1) * (-662838684750) - 2^40 - 2*11764181250 : ℤ) = 202637379224 ∧
    (2^40 - (-1)*(-662838684750) - 11764181250 : ℤ) = 424908761776 := by
  norm_num

/-- Shrinking radii need not separate a changing noninteger value. -/
theorem changing_value_enclosure {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    |(1 : ℝ)-1| ≤ r ∧ |(1+r^2)-1| ≤ r ∧
      1+r^2 ∉ Set.range ((↑) : ℤ → ℝ) := by
  refine ⟨by simpa using hr.le, ?_, ?_⟩
  · rw [add_sub_cancel_left, abs_of_nonneg (sq_nonneg r)]
    nlinarith
  · rintro ⟨z, hz⟩
    have hlo : (1 : ℝ) < z := by rw [hz]; nlinarith
    have hhi : (z : ℝ) < 2 := by rw [hz]; nlinarith
    have hl : (1 : ℤ) < z := by exact_mod_cast hlo
    have hh : z < (2 : ℤ) := by exact_mod_cast hhi
    omega

end ErdosProblems.Erdos251.PaperCompleteR20
#print axioms ErdosProblems.Erdos251.PaperCompleteR20.one_tail_signed_certificate
#print axioms ErdosProblems.Erdos251.PaperCompleteR20.finite_separation_complete
#print axioms ErdosProblems.Erdos251.PaperCompleteR20.one_tail_example_margins

#print axioms ErdosProblems.Erdos251.PaperCompleteR20.changing_value_enclosure
