import ErdosProblems.Erdos251.SparsePolylogR11
import ErdosProblems.Erdos251.ReturnedSparseWindow

/-! # Growing unnormalised blocks: total variation and bounded tests
UNRUN candidate. Probability is uniform over the X starting indices in
[X,2X). The letters themselves are not rescaled. Total variation uses the
supremum-over-events convention, so bounded tests carry a factor two.
-/
noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR11.GrowingBlocks
open PaperR7 PaperR8.SparseSchedule SparsePolylog

def eventFrequency {α : Type*} (a : ℕ → α) (X m : ℕ)
    (E : Set (Fin m → α)) : ℝ := (eventStarts a (Ico X (2 * X)) m E).card / (X : ℝ)

def testMean {α : Type*} (a : ℕ → α) (X m : ℕ)
    (Φ : ℕ → (Fin m → α) → ℝ) : ℝ :=
  (∑ N ∈ Ico X (2 * X), Φ N (fun i => a (N + i.val))) / X

def blockTV {α : Type*} (a b : ℕ → α) (X m : ℕ) : ℝ :=
  sSup (Set.range (fun E : Set (Fin m → α) => |eventFrequency a X m E - eventFrequency b X m E|))

theorem eventFrequency_bounds {α : Type*} (a : ℕ → α) (X m : ℕ)
    (E : Set (Fin m → α)) : 0 ≤ eventFrequency a X m E ∧ eventFrequency a X m E ≤ 1 := by
  classical
  have hcard : (eventStarts a (Ico X (2 * X)) m E).card ≤ X := by
    have h := card_le_card (filter_subset (fun N => (fun i : Fin m => a (N + i.val)) ∈ E)
      (Ico X (2 * X)))
    have hI : (Ico X (2 * X)).card = X := by simp [two_mul]
    simpa only [eventStarts, hI] using h
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  by_cases hX : X = 0
  · simp [eventFrequency, hX]
  · have hXP : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
    apply (div_le_iff₀ hXP).mpr
    simpa only [one_mul] using (show ((eventStarts a (Ico X (2 * X)) m E).card : ℝ) ≤ X by exact_mod_cast hcard)

theorem event_discrepancy_le_one {α : Type*} (a b : ℕ → α) (X m : ℕ)
    (E : Set (Fin m → α)) : |eventFrequency a X m E - eventFrequency b X m E| ≤ 1 := by
  have ha := eventFrequency_bounds a X m E
  have hb := eventFrequency_bounds b X m E
  rw [abs_le]
  constructor <;> linarith

theorem event_discrepancy_le_TV {α : Type*} (a b : ℕ → α) (X m : ℕ)
    (E : Set (Fin m → α)) : |eventFrequency a X m E - eventFrequency b X m E| ≤ blockTV a b X m := by
  apply le_csSup
  · exact ⟨1, by rintro y ⟨F, rfl⟩; exact event_discrepancy_le_one a b X m F⟩
  · exact ⟨E, rfl⟩

theorem blockTV_nonnegative {α : Type*} (a b : ℕ → α) (X m : ℕ) : 0 ≤ blockTV a b X m :=
  (abs_nonneg _).trans (event_discrepancy_le_TV a b X m ∅)

theorem blockTV_le_one {α : Type*} (a b : ℕ → α) (X m : ℕ) : blockTV a b X m ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨E, rfl⟩
  exact event_discrepancy_le_one a b X m E

theorem blockTV_le_finite_support {α : Type*} (a b : ℕ → α) (X m : ℕ) (S : Finset ℕ)
    (hS : ∀ N ∈ Ico X (2 * X), ∀ i : Fin m,
      a (N + i.val) ≠ b (N + i.val) → N + i.val ∈ S) :
    blockTV a b X m ≤ (m : ℝ) * S.card / X := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨E, rfl⟩
  have h := block_event_count_difference_le a b (Ico X (2 * X)) S m hS E
  have hr : |((eventStarts a (Ico X (2 * X)) m E).card : ℝ) -
      (eventStarts b (Ico X (2 * X)) m E).card| ≤ (m : ℝ) * S.card := by exact_mod_cast h
  simpa only [eventFrequency, ← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg X : (0 : ℝ) ≤ X)]
    using div_le_div_of_nonneg_right hr (Nat.cast_nonneg X : (0 : ℝ) ≤ X)

theorem testMean_le_finite_support {α : Type*} (a b : ℕ → α) (X m : ℕ) (S : Finset ℕ)
    (hS : ∀ N ∈ Ico X (2 * X), ∀ i : Fin m,
      a (N + i.val) ≠ b (N + i.val) → N + i.val ∈ S)
    (Φ : ℕ → (Fin m → α) → ℝ)
    (ha : ∀ N ∈ Ico X (2 * X), |Φ N (fun i => a (N + i.val))| ≤ 1)
    (hb : ∀ N ∈ Ico X (2 * X), |Φ N (fun i => b (N + i.val))| ≤ 1) :
    |testMean a X m Φ - testMean b X m Φ| ≤ 2 * (m : ℝ) * S.card / X := by
  have h := block_test_sum_difference_le a b (Ico X (2 * X)) S m hS Φ ha hb
  simpa only [testMean, ← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg X : (0 : ℝ) ≤ X)]
    using div_le_div_of_nonneg_right h (Nat.cast_nonneg X : (0 : ℝ) ≤ X)

/-- The support interval has length X+m, not X; this handles right-edge blocks. -/
theorem window_support {α : Type*} (a b : ℕ → α) (c : ℕ → ℕ)
    (hchange : ∀ n, a n ≠ b n → n ∈ Set.range c) (X m : ℕ) :
    ∀ N ∈ Ico X (2 * X), ∀ i : Fin m,
      a (N + i.val) ≠ b (N + i.val) → N + i.val ∈ supportSlice c X (X + m) := by
  classical
  intro N hN i hne
  have hNi := mem_Ico.mp hN
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by have := i.isLt; omega⟩,
    hchange (N + i.val) hne⟩

theorem polylog_block_bounds {α : Type*} (a b : ℕ → α) {β : ℝ}
    (hβ : 0 < β) (start : ℕ)
    (hchange : ∀ n, a n ≠ b n → n ∈ Set.range (centre (polylog β) start)) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X m : ℕ, X₀ ≤ X → m ≤ X →
      blockTV a b X m ≤ C * ((m : ℝ) / iterlog X) ∧
      ∀ Φ : ℕ → (Fin m → α) → ℝ,
        (∀ N ∈ Ico X (2 * X), |Φ N (fun i => a (N + i.val))| ≤ 1) →
        (∀ N ∈ Ico X (2 * X), |Φ N (fun i => b (N + i.val))| ≤ 1) →
        |testMean a X m Φ - testMean b X m Φ| ≤ 2 * C * ((m : ℝ) / iterlog X) := by
  obtain ⟨C, hC, X₀, hX₀⟩ := polylog_extended_rate hβ start
  refine ⟨C, hC, max 1 X₀, ?_⟩
  intro X m hX hm
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  have hXP : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hDP := iterlog_pos hX1
  let S := supportSlice (centre (polylog β) start) X (X + m)
  have hcard : (S.card : ℝ) ≤ C * X / iterlog X :=
    hX₀ X (X + m) ((le_max_right _ _).trans hX) (by omega)
  have hbound : (m : ℝ) * S.card / X ≤ C * ((m : ℝ) / iterlog X) := by
    calc
      (m : ℝ) * S.card / X ≤ (m : ℝ) * (C * X / iterlog X) / X :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)) hXP.le
      _ = C * ((m : ℝ) / iterlog X) := by field_simp [hXP.ne', hDP.ne']
  have hS := window_support a b _ hchange X m
  refine ⟨(blockTV_le_finite_support a b X m S hS).trans hbound, ?_⟩
  intro Φ ha hb
  have h := testMean_le_finite_support a b X m S hS Φ ha hb
  calc
    _ ≤ 2 * (m : ℝ) * S.card / X := h
    _ = 2 * ((m : ℝ) * S.card / X) := by ring
    _ ≤ 2 * (C * ((m : ℝ) / iterlog X)) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = _ := by ring

theorem small_blocks_eventually_le_index (m : ℕ → ℕ)
    (hm : Tendsto (fun X => (m X : ℝ) / iterlog X) atTop (𝓝 0)) :
    ∀ᶠ X : ℕ in atTop, m X ≤ X := by
  have hs : ∀ᶠ X : ℕ in atTop, (m X : ℝ) / iterlog X < 1 :=
    hm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hs, eventually_ge_atTop (1 : ℕ)] with X hX hX1
  have h := (div_lt_iff₀ (iterlog_pos hX1)).mp hX
  have hL := iterlog_le_nat hX1
  have hreal : (m X : ℝ) ≤ X := by linarith
  exact_mod_cast hreal

/-- The actual total-variation limit, allowing a different block alphabet at every X. -/
theorem growing_block_TV {α : Type*} (a b : ℕ → α) {β : ℝ}
    (hβ : 0 < β) (start : ℕ)
    (hchange : ∀ n, a n ≠ b n → n ∈ Set.range (centre (polylog β) start))
    (m : ℕ → ℕ) (hm : Tendsto (fun X => (m X : ℝ) / iterlog X) atTop (𝓝 0)) :
    Tendsto (fun X => blockTV a b X (m X)) atTop (𝓝 0) := by
  obtain ⟨C, hC, X₀, hX₀⟩ := polylog_block_bounds a b hβ start hchange
  have hu : Tendsto (fun X => C * ((m X : ℝ) / iterlog X)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hm.const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun X => blockTV_nonnegative a b X (m X))) ?_ hu
  filter_upwards [eventually_ge_atTop X₀, small_blocks_eventually_le_index m hm] with X hX hmX
  exact (hX₀ X (m X) hX hmX).1

/-- Uniformity in all bounded tests, including tests depending on the starting index. -/
theorem growing_block_tests_uniform {α : Type*} (a b : ℕ → α) {β : ℝ}
    (hβ : 0 < β) (start : ℕ)
    (hchange : ∀ n, a n ≠ b n → n ∈ Set.range (centre (polylog β) start))
    (m : ℕ → ℕ) (hm : Tendsto (fun X => (m X : ℝ) / iterlog X) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
      ∀ Φ : ℕ → (Fin (m X) → α) → ℝ,
        (∀ N ∈ Ico X (2 * X), |Φ N (fun i => a (N + i.val))| ≤ 1) →
        (∀ N ∈ Ico X (2 * X), |Φ N (fun i => b (N + i.val))| ≤ 1) →
        |testMean a X (m X) Φ - testMean b X (m X) Φ| < ε := by
  obtain ⟨C, hC, X₀, hX₀⟩ := polylog_block_bounds a b hβ start hchange
  have hu : Tendsto (fun X => 2 * C * ((m X : ℝ) / iterlog X)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hm.const_mul (2 * C)
  intro ε hε
  have hs := hu.eventually (gt_mem_nhds hε)
  filter_upwards [hs, eventually_ge_atTop X₀, small_blocks_eventually_le_index m hm] with X hεX hX hmX
  intro Φ ha hb
  exact ((hX₀ X (m X) hX hmX).2 Φ ha hb).trans_lt hεX

/-- Arbitrary fixed real test bounds follow uniformly by rescaling.
The bound B need not be one, and tests may vary with X and the start N. -/
theorem growing_block_tests_bounded {α : Type*} (a b : ℕ → α) {β : ℝ}
    (hβ : 0 < β) (start : ℕ)
    (hchange : ∀ n, a n ≠ b n → n ∈ Set.range (centre (polylog β) start))
    (m : ℕ → ℕ) (hm : Tendsto (fun X => (m X : ℝ) / iterlog X) atTop (𝓝 0))
    (B : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
      ∀ Φ : ℕ → (Fin (m X) → α) → ℝ,
        (∀ N ∈ Ico X (2 * X), |Φ N (fun i => a (N + i.val))| ≤ B) →
        (∀ N ∈ Ico X (2 * X), |Φ N (fun i => b (N + i.val))| ≤ B) →
        |testMean a X (m X) Φ - testMean b X (m X) Φ| < ε := by
  let D : ℝ := |B| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hBD : B ≤ D := by dsimp [D]; linarith [le_abs_self B]
  intro ε hε
  have hu := growing_block_tests_uniform a b hβ start hchange m hm
    (ε / D) (div_pos hε hD)
  filter_upwards [hu] with X hX
  intro Φ ha hb
  let ψ : ℕ → (Fin (m X) → α) → ℝ := fun N u => Φ N u / D
  have ha' : ∀ N ∈ Ico X (2 * X), |ψ N (fun i => a (N + i.val))| ≤ 1 := by
    intro N hN
    change |Φ N (fun i => a (N + i.val)) / D| ≤ 1
    rw [abs_div, abs_of_pos hD]
    exact (div_le_one hD).mpr ((ha N hN).trans hBD)
  have hb' : ∀ N ∈ Ico X (2 * X), |ψ N (fun i => b (N + i.val))| ≤ 1 := by
    intro N hN
    change |Φ N (fun i => b (N + i.val)) / D| ≤ 1
    rw [abs_div, abs_of_pos hD]
    exact (div_le_one hD).mpr ((hb N hN).trans hBD)
  have h := hX ψ ha' hb'
  have heq : testMean a X (m X) ψ - testMean b X (m X) ψ =
      (testMean a X (m X) Φ - testMean b X (m X) Φ) / D := by
    unfold testMean ψ
    simp only [← sum_div]
    ring
  rw [heq, abs_div, abs_of_pos hD] at h
  exact (div_lt_div_iff_of_pos_right hD).mp h

#print axioms growing_block_TV
#print axioms growing_block_tests_uniform
end ErdosProblems.Erdos251.PaperR11.GrowingBlocks
