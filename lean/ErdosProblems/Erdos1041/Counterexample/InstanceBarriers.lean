import ErdosProblems.Erdos1041.Counterexample.BarrierSigns
/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Explicit separating barriers replacing the Riemann-Hurwitz step of Lemma 2.1, at `s = 10⁻⁶`. -/

/-!
STATEMENT-NAME DELTA: the candidate is placed in the child namespace
`S7Proof`, because the unchanged input Defs.lean already declares the requested
fully qualified name. The proposition itself below is unchanged. No reference
to the existing theorem stub is made. Compilation and axiom checks were not
available in the creation environment; see RETURN_NOTES.md.
-/
noncomputable section
namespace Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

/-- Positive rescaling of the prescribed physical-coordinate graph barrier. -/
def g1 (z : ℂ) : ℝ := G1 (z / (scaleR : ℂ))
def g2 (z : ℂ) : ℝ := G2 (z / (scaleR : ℂ))

theorem continuous_g1 : Continuous g1 := by
  exact continuous_G1.comp (by fun_prop)

theorem continuous_g2 : Continuous g2 := by
  exact continuous_G2.comp (by fun_prop)

theorem unscale (z : ℂ) :
    (ρ : ℂ) * (ε : ℂ) * (z / (scaleR : ℂ)) = z := by
  rw [← scale_cast, mul_div_assoc', mul_comm (scaleR : ℂ) z, mul_div_assoc,
    div_self scale_ne, mul_one]

theorem scaled_near (zs : ℂ)
    (hnear : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
      < (ρ : ℝ) * (ε : ℝ) / 1000) :
    ‖zs / (scaleR : ℂ) - centre‖ < 1 / 1000 := by
  have hcentre : (scaleR : ℂ) * centre =
      (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I := by
    rw [scale_cast]
    unfold centre
    norm_num
    <;> ring
  rw [norm_div_sub zs centre scaleR scale_pos, hcentre]
  apply (div_lt_iff₀ scale_pos).2
  simpa [scaleR, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hnear

theorem scaled_root_disk (j : ℕ) (w : ℂ)
    (hw : ‖w - (ρ : ℂ) * u j‖ < (ρ : ℝ) / 10) :
    ‖w / (scaleR : ℂ) - (rootScale : ℂ) * u j‖ < rootScale / 10 := by
  have hm : (scaleR : ℂ) * (rootScale : ℂ) = (ρ : ℂ) := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) scale_rootScale
    simpa using h
  rw [norm_div_sub w ((rootScale : ℂ) * u j) scaleR scale_pos]
  rw [← mul_assoc, hm]
  apply (div_lt_iff₀ scale_pos).2
  have hscale : rootScale / 10 * scaleR = (ρ : ℝ) / 10 := by
    calc
      rootScale / 10 * scaleR = (scaleR * rootScale) / 10 := by ring
      _ = (ρ : ℝ) / 10 := by rw [scale_rootScale]
  simpa only [hscale] using hw

theorem s7_barriers' (zs : ℂ)
    (hnear : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
      < (ρ : ℝ) * (ε : ℝ) / 1000) :
    ∃ g₁ g₂ : ℂ → ℝ, Continuous g₁ ∧ Continuous g₂ ∧
      (∀ z, g₁ z = 0 → 1 ≤ ‖f.eval z‖) ∧ (∀ z, g₂ z = 0 → 1 ≤ ‖f.eval z‖) ∧
      g₁ zs < 0 ∧ g₂ zs < 0 ∧
      (∀ j : Fin 7, j.val = 0 ∨ j.val = 1 ∨ j.val = 2 →
        ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₁ w) ∧
      (∀ j : Fin 7, j.val = 4 ∨ j.val = 5 →
        ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₂ w) := by
  refine ⟨g1, g2, continuous_g1, continuous_g2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h := G1_zero_norm (z / (scaleR : ℂ)) hz
    simpa only [unscale] using h
  · intro z hz
    have h := G2_zero_norm (z / (scaleR : ℂ)) hz
    simpa only [unscale] using h
  · exact G1_negative_near (zs / (scaleR : ℂ)) (scaled_near zs hnear)
  · exact G2_negative_near (zs / (scaleR : ℂ)) (scaled_near zs hnear)
  · intro j hj w hw
    exact G1_positive_disk rootScale rootScale_ge (u j.val) (w / (scaleR : ℂ))
      (centre1_margin j.val hj) (scaled_root_disk j.val w hw)
  · intro j hj w hw
    exact G2_positive_disk rootScale rootScale_ge (u j.val) (w / (scaleR : ℂ))
      (centre2_margin j.val hj) (scaled_root_disk j.val w hw)

end Erdos1041.Counterexample.S7Proof

namespace Erdos1041.Counterexample

/-- Two explicit continuous barriers separating `zs` from the five roots the
paper does not connect.  S7's obligation, at the shared-interface name. -/
theorem s7_barriers (zs : ℂ)
    (hnear : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
      < (ρ : ℝ) * (ε : ℝ) / 1000) :
    ∃ g₁ g₂ : ℂ → ℝ, Continuous g₁ ∧ Continuous g₂ ∧
      (∀ z, g₁ z = 0 → 1 ≤ ‖f.eval z‖) ∧ (∀ z, g₂ z = 0 → 1 ≤ ‖f.eval z‖) ∧
      g₁ zs < 0 ∧ g₂ zs < 0 ∧
      (∀ j : Fin 7, j.val = 0 ∨ j.val = 1 ∨ j.val = 2 →
        ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₁ w) ∧
      (∀ j : Fin 7, j.val = 4 ∨ j.val = 5 →
        ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₂ w) :=
  S7Proof.s7_barriers' zs hnear

end Erdos1041.Counterexample
