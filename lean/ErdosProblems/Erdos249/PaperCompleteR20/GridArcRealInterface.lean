import ErdosProblems.Erdos249.PaperCompleteR20.FiniteGridExample

namespace ErdosProblems.Erdos249.PaperCompleteR20

/-- Membership in the image of [a,a+b] in the real circle of circumference 4096. -/
def translatedGridArc (a b x : ℝ) : Prop :=
  ∃ k : ℤ, a ≤ x + 4096 * k ∧ x + 4096 * k ≤ a + b

theorem gridArc_iff_translated {a b x : ℝ}
    (ha : 0 ≤ a) (ha' : a < 4096) (hb : b < 4096)
    (hx : 0 ≤ x) (hx' : x < 4096) :
    gridArc a b x ↔ translatedGridArc a b x := by
  constructor
  · rintro ⟨_, _, h | h⟩
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by norm_num; constructor <;> linarith⟩
  · rintro ⟨k, hlo, hhi⟩
    have hk0 : 0 ≤ k := by
      by_contra hn
      have hk : k ≤ -1 := by omega
      have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast hk
      linarith
    have hk1 : k ≤ 1 := by
      by_contra hn
      have hk : 2 ≤ k := by omega
      have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have he : k = 0 ∨ k = 1 := by omega
    refine ⟨hx, hx', ?_⟩
    rcases he with rfl | rfl
    · left; simpa using And.intro hlo hhi
    · right; simpa using hhi

theorem translated_four_arcs_no_common_representative :
    ¬ ∃ x : ℝ, 0 ≤ x ∧ x < 4096 ∧
      translatedGridArc 2920 854 x ∧ translatedGridArc 2024 1694 x ∧
      translatedGridArc 3532 2534 x ∧ translatedGridArc 3796 3374 x := by
  rintro ⟨x, hx, hx', h1, h2, h3, h4⟩
  apply four_arcs_no_common_point
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · exact (gridArc_iff_translated (by norm_num) (by norm_num) (by norm_num) hx hx').mpr h1
  · exact (gridArc_iff_translated (by norm_num) (by norm_num) (by norm_num) hx hx').mpr h2
  · exact (gridArc_iff_translated (by norm_num) (by norm_num) (by norm_num) hx hx').mpr h3
  · exact (gridArc_iff_translated (by norm_num) (by norm_num) (by norm_num) hx hx').mpr h4

theorem translatedGridArc_sub_period {a b x : ℝ} (n : ℤ)
    (h : translatedGridArc a b x) : translatedGridArc a b (x - 4096 * n) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + n, ?_⟩
  push_cast
  convert hk using 1 <;> congr 1 <;> ring

theorem translated_four_arcs_no_common_point :
    ¬ ∃ x : ℝ,
      translatedGridArc 2920 854 x ∧ translatedGridArc 2024 1694 x ∧
      translatedGridArc 3532 2534 x ∧ translatedGridArc 3796 3374 x := by
  rintro ⟨x, h1, h2, h3, h4⟩
  let n : ℤ := ⌊x / 4096⌋
  have hlo := Int.floor_le (x / 4096)
  have hhi := Int.lt_floor_add_one (x / 4096)
  apply translated_four_arcs_no_common_representative
  refine ⟨x - 4096 * n, ?_, ?_, translatedGridArc_sub_period n h1,
    translatedGridArc_sub_period n h2, translatedGridArc_sub_period n h3,
    translatedGridArc_sub_period n h4⟩
  · dsimp [n]; linarith
  · dsimp [n]; linarith

end ErdosProblems.Erdos249.PaperCompleteR20
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.gridArc_iff_translated
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.translated_four_arcs_no_common_representative

#print axioms ErdosProblems.Erdos249.PaperCompleteR20.translated_four_arcs_no_common_point
