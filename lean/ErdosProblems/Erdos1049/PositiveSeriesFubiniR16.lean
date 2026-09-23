import ErdosProblems.Erdos1049.PositiveSeriesR16

/-! Nonnegative series assembly. New candidate; all Lean checks UNRUN. -/
namespace ErdosProblems.Erdos1049.PaperR16
open Filter
open scoped BigOperators Topology

/-- A coefficient sequence and its actual convergent value at a real point. -/
structure PositiveSum (c : ℕ → ℝ) (w value : ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ c n
  sum : HasSum (fun n : ℕ => c n * w ^ n) value

lemma PositiveSum.eval_eq {c : ℕ → ℝ} {w v : ℝ} (h : PositiveSum c w v) :
    coeffEval c w = v := h.sum.tsum_eq

lemma PositiveSum.conv {a b : ℕ → ℝ} {w x y : ℝ}
    (ha : PositiveSum a w x) (hb : PositiveSum b w y) (hw : 0 ≤ w) :
    PositiveSum (coeffConv a b) w (x * y) := by
  refine ⟨coeffConv_nonneg ha.nonneg hb.nonneg, ?_⟩
  have h := coeffConv_hasSum ha.nonneg hb.nonneg hw ha.sum.summable hb.sum.summable
  simpa only [ha.eval_eq, hb.eval_eq] using h

/-- The nonnegative Fubini implication proved with finite rectangles. -/
lemma summable_rows_nonneg {ι κ : Type*} {f : ι → κ → ℝ}
    (hf0 : ∀ i j, 0 ≤ f i j) (hrow : ∀ i, Summable (f i))
    (houter : Summable (fun i => ∑' j, f i j)) :
    Summable (fun p : ι × κ => f p.1 p.2) := by
  classical
  apply summable_of_sum_le (f := fun p : ι × κ => f p.1 p.2) (fun p => hf0 p.1 p.2)
    (c := ∑' i, ∑' j, f i j)
  intro s
  have hsub : s ⊆ (s.image Prod.fst) ×ˢ (s.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  calc
    _ ≤ ∑ p ∈ (s.image Prod.fst) ×ˢ (s.image Prod.snd), f p.1 p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hf0 p.1 p.2)
    _ = ∑ i ∈ s.image Prod.fst, ∑ j ∈ s.image Prod.snd, f i j := by
      rw [Finset.sum_product]
    _ ≤ ∑ i ∈ s.image Prod.fst, ∑' j, f i j := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hrow i).sum_le_tsum _ (fun j _ => hf0 i j)
    _ ≤ ∑' i, ∑' j, f i j :=
      houter.sum_le_tsum _ (fun i _ => tsum_nonneg (hf0 i))

lemma tsum_product_eq_rows {ι κ : Type*} {f : ι → κ → ℝ}
    (hf : Summable (fun p : ι × κ => f p.1 p.2))
    (hrow : ∀ i, Summable (f i))
    (houter : Summable (fun i => ∑' j, f i j)) :
    (∑' p : ι × κ, f p.1 p.2) = ∑' i, ∑' j, f i j := by
  have h := HasSum.prod_fiberwise hf.hasSum (fun i => (hrow i).hasSum)
  exact h.unique houter.hasSum

/-- Regroup an actually summable product-indexed series by its finite natural
antidiagonals. This is the generic diagonal identity behind the gamma series. -/
lemma hasSum_antidiagonal {f : ℕ × ℕ → ℝ} (hf : Summable f) :
    HasSum (fun n : ℕ => ∑ p ∈ Finset.antidiagonal n, f p) (∑' p, f p) := by
  classical
  let e := (Finset.sigmaAntidiagonalEquivProd :
    (Σ n : ℕ, ↥(Finset.antidiagonal n)) ≃ ℕ × ℕ)
  have hs : Summable (fun p : Σ n : ℕ, ↥(Finset.antidiagonal n) => f p.2.val) := by
    exact e.summable_iff.mpr hf
  have hs' : Summable (fun n : ℕ => ∑' p : ↥(Finset.antidiagonal n), f p.val) :=
    hs.sigma' (fun n => (hasSum_fintype _).summable)
  have he : (∑' p : ℕ × ℕ, f p) =
      ∑' n : ℕ, ∑' p : ↥(Finset.antidiagonal n), f p.val := by
    rw [← e.tsum_eq f]
    exact hs.tsum_sigma' (fun n => (hasSum_fintype _).summable)
  rw [he]
  simpa only [tsum_fintype, Finset.sum_coe_sort] using hs'.hasSum

end ErdosProblems.Erdos1049.PaperR16
