import ErdosProblems.Erdos1049.BezoutPluckerJets

/-!
# Adjacent minors with unimodular rows

The coordinate that is invertible need not be the same along a tail. In fact,
neither coordinate need be invertible: a Bézout identity for each row suffices.
For example, `(2,3)` is unimodular modulo six, although neither entry is a unit.
The middle row's Bézout identity is precisely what lets two adjacent vanishing
minors imply the outer minor vanishes, even over rings with zero divisors.

This strengthens the algebraic input to the endpoint selector collision.
It supplies no analytic remainder or nonvanishing assertion for Erdős #1049.
-/

namespace ErdosProblems.Erdos1049.BezoutPluckerJets

variable {R : Type*} [CommRing R]

/-- Only the middle row needs to be unimodular to propagate across two edges. -/
theorem det_zero_trans_of_middle_isCoprime (u v w : R × R)
    (hv : IsCoprime v.1 v.2)
    (huv : u.1 * v.2 - u.2 * v.1 = 0)
    (hvw : v.1 * w.2 - v.2 * w.1 = 0) :
    u.1 * w.2 - u.2 * w.1 = 0 := by
  have hvu : v.1 * u.2 - v.2 * u.1 = 0 := by
    calc
      v.1 * u.2 - v.2 * u.1 = -(u.1 * v.2 - u.2 * v.1) := by ring
      _ = 0 := by rw [huv]; ring
  obtain ⟨a, ha₁, ha₂⟩ := exists_scalar_eq_of_det_eq_zero hv hvu
  obtain ⟨b, hb₁, hb₂⟩ := exists_scalar_eq_of_det_eq_zero hv hvw
  rw [ha₁, ha₂, hb₁, hb₂]
  ring

/-- Adjacent vanishing propagates with rowwise Bézout identities; no fixed
coordinate is required to be a unit. -/
theorem adjacent_det_zero_forces_all_det_zero_of_isCoprime
    (w : ℕ → R × R) (hprim : ∀ n, IsCoprime (w n).1 (w n).2)
    (hadj : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) :
    ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0 := by
  have hanchor : ∀ n, (w 0).1 * (w n).2 - (w 0).2 * (w n).1 = 0 := by
    intro n
    induction n with
    | zero => ring
    | succ n ih =>
        exact det_zero_trans_of_middle_isCoprime (w 0) (w n) (w (n + 1))
          (hprim n) ih (hadj n)
  exact anchor_det_zero_forces_all_det_zero w (hprim 0) hanchor

/-- The compressed modulus-cardinality threshold survives the weaker
rowwise unimodularity hypothesis. -/
theorem zmod_binary_tail_collision_of_adjacent_det_zero_of_isCoprime
    {N k : ℕ} [NeZero N] (w : ℕ → ZMod N × ZMod N)
    (hprim : ∀ n, IsCoprime (w n).1 (w n).2)
    (hadj : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0)
    (hcard : N < 2 ^ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  have hall := adjacent_det_zero_forces_all_det_zero_of_isCoprime w hprim hadj
  apply binary_row_collision_of_anchor_det_zero (fun i : Fin k => w i) (hprim 0)
  · intro i
    exact hall 0 i
  · simpa using hcard

/-- Unimodularity can hold even when both coordinates are nonunits. -/
theorem two_three_isCoprime_zmod_six : IsCoprime (2 : ZMod 6) 3 := by
  exact ⟨-1, 1, by decide⟩

end ErdosProblems.Erdos1049.BezoutPluckerJets
