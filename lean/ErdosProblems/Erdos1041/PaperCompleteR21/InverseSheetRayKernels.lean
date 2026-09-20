import Mathlib

/-!
# Erdős #1041: ray and saddle kernels for the inverse-sheet decomposition

Partial work towards the environment of
`paper/reasoning-parts/erdos1041/core.tex` labelled `res:attachment-aware-reeb`
(line 3785).  The theorem there has four clauses about a component `U` of
`{|f| < 1}` containing `k ≥ 2` roots: that `-log|f|` is a proper excellent Morse
function with `k-1` saddles; that cutting `𝔻 ∖ {0}` along the critical-value
rays decomposes the preimage into conformal strips; that cutting each ray only
outwards gives `k` sheets whose critical transpositions form a tree; and that
the inward lifts of `[0, f(c)]` realise that tree as an embedded graph.

The environment is NOT covered.  Its load-bearing inputs are absent from Mathlib
v4.29.1 and from this tree: proper holomorphic maps of plane domains and their
degree, the component-wise Riemann–Hurwitz count in the proof of `eks2010`
Proposition 2.1, the holomorphic Morse lemma, the strip uniformisation of a
sector preimage by `-log f`, and the monodromy action of the punctured value
domain on the `k` sheets with its transitivity.  The paper itself records the
boundary at line 3873: its Lean companion "explicitly does not formalise
Riemann–Hurwitz, monodromy, the strip diffeomorphisms or the geometric
assembly".

What is proved here are the elementary plane-geometry and Morse-scale kernels
the ordinary proof uses at three separate points, none of which was present in
the tree before:

* `criticalSegment_inter_eq_zero` and `outwardSlit_ne` — the distinct-argument
  hypothesis in the exact form the proof uses it: two inward critical segments
  `[0, w]` with distinct critical-value arguments meet only at `0`, and the
  outward slits `{t w : 1 ≤ t}` never meet.  This is the embeddedness step of
  clause (4) ("an intersection would give one nonzero value on two critical
  rays") and the disjointness of the cuts in clauses (2) and (3).
* `morseLevel_pairwise_ne` — the "excellent" half of clause (1): pairwise
  distinct critical-value moduli give pairwise distinct levels of the Morse
  function `-log|f|`.
* `root_ne_criticalPoint` — clause (4)'s observation that under the nonzero
  critical-value hypothesis a root in `U` is not a critical point.
* `saddle_model_radius` — the closing `O(√δ)` sentence, in the exact local
  coordinate the paper names: with `f(z) - f(c) = A (z-c)^2` and `A = f''(c)/2`,
  a value radius `δ` matches spatial radius `√(δ/|A|) = √(2δ/|f''(c)|)`.

The combinatorial half of clause (3) — a connected graph on `k` vertices with
`k-1` edges is a tree — is already in the tree as
`ErdosProblems.Erdos1041.AttachmentAwareReeb.isTree_of_connected_of_card_eq`.
That module has no `.olean` in this build, so it is not imported here.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

/-- Two inward critical segments `[0, w₁]` and `[0, w₂]` whose critical values
have distinct arguments meet only at `0`. -/
theorem criticalSegment_inter_eq_zero {w₁ w₂ : ℂ} (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0)
    (harg : w₁.arg ≠ w₂.arg) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (heq : (s : ℂ) * w₁ = (t : ℂ) * w₂) : (s : ℂ) * w₁ = 0 := by
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · rw [← hs0]
    simp
  · exfalso
    have hsC : (s : ℂ) ≠ 0 := by
      simpa using hs0.ne'
    have hsz : (s : ℂ) * w₁ ≠ 0 := mul_ne_zero hsC h₁
    have htz : (t : ℂ) * w₂ ≠ 0 := by rw [← heq]; exact hsz
    have ht0 : 0 < t := by
      rcases eq_or_lt_of_le ht with h | h
      · exact absurd (by rw [← h]; simp) htz
      · exact h
    have e1 : ((s : ℂ) * w₁).arg = w₁.arg := Complex.arg_real_mul w₁ hs0
    have e2 : ((t : ℂ) * w₂).arg = w₂.arg := Complex.arg_real_mul w₂ ht0
    rw [heq, e2] at e1
    exact harg e1.symm

/-- The outward slits attached to two critical values with distinct arguments
are disjoint. -/
theorem outwardSlit_ne {w₁ w₂ : ℂ} (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0)
    (harg : w₁.arg ≠ w₂.arg) {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    (s : ℂ) * w₁ ≠ (t : ℂ) * w₂ := by
  intro heq
  have hzero := criticalSegment_inter_eq_zero h₁ h₂ harg (by linarith) (by linarith) heq
  have hsC : (s : ℂ) ≠ 0 := by
    have : (0 : ℝ) < s := by linarith
    simpa using this.ne'
  exact (mul_ne_zero hsC h₁) hzero

/-- The "excellent" half of clause (1): critical values of pairwise distinct
moduli sit at pairwise distinct levels of the Morse function `-log |f|`. -/
theorem morseLevel_pairwise_ne {ι : Type*} (v : ι → ℂ) (hv : ∀ i, v i ≠ 0)
    (hmod : ∀ i j, i ≠ j → ‖v i‖ ≠ ‖v j‖) :
    ∀ i j, i ≠ j → -Real.log ‖v i‖ ≠ -Real.log ‖v j‖ := by
  intro i j hij hlevel
  refine hmod i j hij ?_
  have hi : 0 < ‖v i‖ := norm_pos_iff.mpr (hv i)
  have hj : 0 < ‖v j‖ := norm_pos_iff.mpr (hv j)
  have hlog : Real.log ‖v i‖ = Real.log ‖v j‖ := by linarith
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr hi) (Set.mem_Ioi.mpr hj) hlog

/-- Clause (4): under the nonzero-critical-value hypothesis a root of `f` is not
a critical point of `f`, so the two labels exchanged by a critical
transposition are distinct roots. -/
theorem root_ne_criticalPoint {f : ℂ → ℂ} {z c : ℂ} (hz : f z = 0) (hc : f c ≠ 0) :
    z ≠ c := by
  intro h
  exact hc (h ▸ hz)

/-- The closing `O(√δ)` sentence in the paper's own coordinate.  At a simple
critical point the local model is `f(z) - f(c) = A (z - c)^2` with
`A = f''(c)/2 ≠ 0`; a value at distance `‖w‖` from the critical value therefore
sits at spatial distance `√(‖w‖/‖A‖) = √(2‖w‖/‖f''(c)‖)` from the critical
point, which is the asserted `O(√δ)` saddle scale. -/
theorem saddle_model_radius {A w z : ℂ} (hA : A ≠ 0) (h : A * z ^ 2 = w) :
    ‖z‖ = Real.sqrt (‖w‖ / ‖A‖) := by
  have hA0 : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hn : ‖A‖ * ‖z‖ ^ 2 = ‖w‖ := by
    rw [← h, norm_mul, norm_pow]
  have hsq : ‖z‖ ^ 2 = ‖w‖ / ‖A‖ := by
    rw [eq_div_iff hA0.ne']
    linarith
  rw [← hsq, Real.sqrt_sq (norm_nonneg z)]

#print axioms criticalSegment_inter_eq_zero
#print axioms outwardSlit_ne
#print axioms morseLevel_pairwise_ne
#print axioms root_ne_criticalPoint
#print axioms saddle_model_radius

end ErdosProblems.Erdos1041.PaperCompleteR21

end
