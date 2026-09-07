import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# End-to-end linear-channel obstruction

Uncompiled candidates for `lem:linear-channel-nogo` and long result 159.
These results include the rank bound and every square minor, rather than only
one determinant. No surjectivity or normalising vector hypothesis is needed:
the zero evaluation map is handled separately. This is linear algebra, not an
irrationality statement.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR7

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A family of rational linear forms annihilating ker(ev) factors through ev,
including the case ev = 0. -/
theorem relationInvariantChannels_factor {κ : Type*}
    (ev : V →ₗ[ℚ] ℚ) (channel : κ → V →ₗ[ℚ] ℚ)
    (hrel : ∀ j v, ev v = 0 → channel j v = 0) :
    ∃ c : κ → ℚ, ∀ j v, channel j v = c j * ev v := by
  classical
  by_cases hev : ev = 0
  · refine ⟨fun _ => 0, ?_⟩
    intro j v
    simpa using hrel j v (by simp [hev])
  · have hex : ∃ v : V, ev v ≠ 0 := by
      by_contra h
      push_neg at h
      apply hev
      ext v
      exact h v
    obtain ⟨v, hv⟩ := hex
    let e : V := (ev v)⁻¹ • v
    have he : ev e = 1 := by
      simp [e, map_smul, hv]
    refine ⟨fun j => channel j e, ?_⟩
    intro j x
    have hz : ev (x - ev x • e) = 0 := by
      simp [map_sub, map_smul, he]
    have hc := hrel j (x - ev x • e) hz
    simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero,
      mul_comm] using hc

/-- The complete rank statement for any finite row and column index types. -/
theorem relationInvariantChannels_rank_le_one
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ev : V →ₗ[ℚ] ℚ) (channel : κ → V →ₗ[ℚ] ℚ)
    (row : ι → V)
    (hrel : ∀ j v, ev v = 0 → channel j v = 0) :
    Matrix.rank (fun i j => channel j (row i)) ≤ 1 := by
  obtain ⟨c, hc⟩ := relationInvariantChannels_factor ev channel hrel
  have hmatrix : (fun i j => channel j (row i)) =
      Matrix.vecMulVec (fun i => ev (row i)) c := by
    funext i j
    simpa [Matrix.vecMulVec, mul_comm] using hc j (row i)
  rw [hmatrix]
  exact Matrix.rank_vecMulVec_le _ _

/-- Every square minor of size at least two has determinant zero. The row and
column selections need not even be injective. -/
theorem relationInvariantChannels_all_minors_zero
    {ι κ : Type*} (ev : V →ₗ[ℚ] ℚ) (channel : κ → V →ₗ[ℚ] ℚ)
    (row : ι → V)
    (hrel : ∀ j v, ev v = 0 → channel j v = 0)
    (k : ℕ) (hk : 2 ≤ k) (r : Fin k → ι) (c : Fin k → κ) :
    Matrix.det (fun i j : Fin k => channel (c j) (row (r i))) = 0 := by
  classical
  let M : Matrix (Fin k) (Fin k) ℚ :=
    fun i j => channel (c j) (row (r i))
  have hrank : M.rank ≤ 1 :=
    relationInvariantChannels_rank_le_one ev (fun j => channel (c j))
      (fun i => row (r i)) (fun j v hv => hrel (c j) v hv)
  change M.det = 0
  by_contra hd
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hd
  have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
  have hlower := Matrix.rank_mul_le_left M M⁻¹
  rw [hmul, Matrix.rank_one, Fintype.card_fin] at hlower
  omega

/-- Joint paper statement: one factorisation controls the rank and all minors.
This strengthens the displayed version by omitting the unnecessary witness
`∃ e, ev e = 1`. -/
theorem long_linear_channel_no_go
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ev : V →ₗ[ℚ] ℚ) (channel : κ → V →ₗ[ℚ] ℚ)
    (row : ι → V)
    (hrel : ∀ j v, ev v = 0 → channel j v = 0) :
    Matrix.rank (fun i j => channel j (row i)) ≤ 1 ∧
      ∀ k : ℕ, 2 ≤ k → ∀ r : Fin k → ι, ∀ c : Fin k → κ,
        Matrix.det (fun i j : Fin k => channel (c j) (row (r i))) = 0 := by
  exact ⟨relationInvariantChannels_rank_le_one ev channel row hrel,
    fun k hk r c => relationInvariantChannels_all_minors_zero
      ev channel row hrel k hk r c⟩

end ErdosProblems.Erdos257.PaperCompleteR7
