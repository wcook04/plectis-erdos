import ErdosProblems.Erdos1041.PaperCompleteR20.TwoNearestWhole

/-! The two-nearest-root bound from the derivative of the actual factored
polynomial. No logarithmic balance or geometric budget is assumed. -/
namespace ErdosProblems.Erdos1041.PaperCompleteR20
open Finset Polynomial
open scoped BigOperators

theorem two_nearest_roots_of_polynomial_critical {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (c : ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (hp : (∏ k : Fin n, (X - C (z k))).eval c ≠ 0)
    (hcrit : (∏ k : Fin n, (X - C (z k))).derivative.eval c = 0)
    (i j : Fin n) (hij : i ≠ j)
    (hi : ∀ k, ‖c - z i‖ ≤ ‖c - z k‖)
    (hj : ∀ k, k ≠ i → ‖c - z j‖ ≤ ‖c - z k‖) :
    ‖c - z i‖ + ‖c - z j‖ < 2 := by
  classical
  have hne : ∀ k, c - z k ≠ 0 := by
    intro k hk
    apply hp
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simpa only [eval_sub, eval_X, eval_C] using hk
  have hlog := PaperReflectedBoundary.product_log_derivative univ z c (fun k _ => hne k)
  have hbalance : ∑ k, (c - z k)⁻¹ = 0 := by
    rw [hcrit, zero_div] at hlog
    exact hlog.symm
  exact two_nearest_roots_open_disc hn z c hz hne hbalance i j hij hi hj

/-- Existence of the two nearest indices is part of the conclusion. -/
theorem exists_two_nearest_roots_of_polynomial_critical {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (c : ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (hp : (∏ k : Fin n, (X - C (z k))).eval c ≠ 0)
    (hcrit : (∏ k : Fin n, (X - C (z k))).derivative.eval c = 0) :
    ∃ i j : Fin n, i ≠ j ∧
      (∀ k, ‖c - z i‖ ≤ ‖c - z k‖) ∧
      (∀ k, k ≠ i → ‖c - z j‖ ≤ ‖c - z k‖) ∧
      ‖c - z i‖ + ‖c - z j‖ < 2 := by
  classical
  let d : Fin n → ℝ := fun k => ‖c - z k‖
  have huniv : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨i, _, hi⟩ := exists_min_image univ d huniv
  have herase : (univ.erase i).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hjmem, hj⟩ := exists_min_image (univ.erase i) d herase
  have hij : i ≠ j := fun h => (mem_erase.mp hjmem).1 h.symm
  have hi' : ∀ k, d i ≤ d k := fun k => hi k (mem_univ k)
  have hj' : ∀ k, k ≠ i → d j ≤ d k := fun k hk => hj k (mem_erase.mpr ⟨hk, mem_univ k⟩)
  exact ⟨i, j, hij, hi', hj',
    two_nearest_roots_of_polynomial_critical hn z c hz hp hcrit i j hij hi' hj'⟩

#print axioms two_nearest_roots_of_polynomial_critical
#print axioms exists_two_nearest_roots_of_polynomial_critical
end ErdosProblems.Erdos1041.PaperCompleteR20
