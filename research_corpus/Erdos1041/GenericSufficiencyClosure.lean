import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic

/-!
# Erdős #1041: the closed-sublevel kernel behind dense-class sufficiency

`GenericSufficiencyClosure.md` proves that the two-root lemniscate path length
`Lam` is lower semicontinuous on the compact class of monic degree-`n`
polynomials with roots in the closed unit disk, so that `{Lam <= 2}` is closed
and a dense subclass suffices.

This module checks the arithmetic and topological steps that the analytic proof
leans on, and nothing else:

* `one_le_prod_norm_sub_of_two_le_norm` — the a priori containment
  `{|g| <= 1} subset {|z| <= 2}`, uniform over the whole class.  This is what
  makes the family of admissible paths uniformly bounded.
* `dist_le_of_tendsto` — a pointwise limit of `L`-Lipschitz curves is
  `L`-Lipschitz, the length half of the Arzelà–Ascoli step.
* `isClosed_sublevel_of_isOpen_superlevel` and `eq_univ_of_isClosed_of_dense`
  — the closed-sublevel-plus-dense skeleton of Corollary D.
* `mul_lt_two_of_lt_one`, `pow_mul_lt_one_of_lt_one` — the two strict
  inequalities Corollary S produces from `R < 1` alone.
* `normSq_sub_one_le_one_iff`, `re_pow_pos_of_ne_zero`,
  `normSq_radial_sub_one_le_one` — the exact sublevel characterisation
  `|z|^(2n) <= 2 Re(z^n)` of the extremal family `z^n - 1`, the strict
  positivity of `Re(z^n)` off the origin that forces the petal split, and the
  containment of the radial segments that gives `Lam(z^n - 1) <= 2`.

Arzelà–Ascoli itself, lower semicontinuity of length, and the sector partition
of the punctured extremal sublevel set are carried by the ordinary proof and are
not encoded here.
-/

namespace ErdosProblems.Erdos1041.GenericSufficiencyClosure

open Finset

/-! ## 1. A priori containment -/

/-- If every root lies in the closed unit disk then every point at distance at
least `2` from the origin has `|g| >= 1`.  Hence `{|g| <= 1}` sits inside the
fixed compact disk `{|z| <= 2}`, uniformly over the class. -/
theorem one_le_prod_norm_sub_of_two_le_norm {n : ℕ} (b : Fin n → ℂ) (z : ℂ)
    (hb : ∀ j, ‖b j‖ ≤ 1) (hz : 2 ≤ ‖z‖) :
    1 ≤ ∏ j, ‖z - b j‖ := by
  have hfac : ∀ j ∈ (univ : Finset (Fin n)), (1 : ℝ) ≤ ‖z - b j‖ := by
    intro j _
    have h1 : ‖z‖ - ‖b j‖ ≤ ‖z - b j‖ := norm_sub_norm_le z (b j)
    have h2 := hb j
    linarith
  calc (1 : ℝ) = ∏ _j : Fin n, (1 : ℝ) := by simp
    _ ≤ ∏ j, ‖z - b j‖ := Finset.prod_le_prod (fun _ _ => zero_le_one) hfac

/-! ## 2. The Lipschitz constant survives the limit -/

/-- A pointwise limit of `L`-Lipschitz curves is `L`-Lipschitz.  Combined with
Arzelà–Ascoli this is the step that keeps the limit curve short. -/
theorem dist_le_of_tendsto {α : Type*} [PseudoMetricSpace α] {ι : Type*}
    {l : Filter ι} [l.NeBot] {L : ℝ} {γ : ι → ℝ → α} {γ₀ : ℝ → α}
    (hL : ∀ i, ∀ s t, dist (γ i s) (γ i t) ≤ L * |s - t|)
    (hconv : ∀ s, Filter.Tendsto (fun i => γ i s) l (nhds (γ₀ s))) :
    ∀ s t, dist (γ₀ s) (γ₀ t) ≤ L * |s - t| := by
  intro s t
  have hd : Filter.Tendsto (fun i => dist (γ i s) (γ i t)) l
      (nhds (dist (γ₀ s) (γ₀ t))) := (hconv s).dist (hconv t)
  exact le_of_tendsto hd (Filter.Eventually.of_forall fun i => hL i s t)

/-! ## 3. Closed sublevel set, dense hypothesis -/

/-- Lower semicontinuity in its open-superlevel form gives a closed sublevel
set. -/
theorem isClosed_sublevel_of_isOpen_superlevel {X : Type*} [TopologicalSpace X]
    (F : X → ℝ) (c : ℝ) (h : IsOpen {x | c < F x}) :
    IsClosed {x | F x ≤ c} := by
  rw [← isOpen_compl_iff]
  convert h using 1
  ext x
  simp [not_le]

/-- A closed condition that holds on a dense set holds everywhere.  This is the
whole logical content of Corollary D. -/
theorem eq_univ_of_isClosed_of_dense {X : Type*} [TopologicalSpace X]
    {S D : Set X} (hS : IsClosed S) (hD : Dense D) (hDS : D ⊆ S) :
    S = Set.univ := by
  refine Set.eq_univ_of_univ_subset ?_
  calc (Set.univ : Set X) = closure D := hD.closure_eq.symm
    _ ⊆ closure S := closure_mono hDS
    _ = S := hS.closure_eq

/-- Compact-witness projection form of the dense-class principle.  It keeps
the witness existential: no continuous selector `X → K` is required.  For
Erdős #1041 this is a logical wrapper only; applying it still requires a
closed relation of *complete path witnesses* on a dense class. -/
theorem exists_compact_witness_of_closed_relation_of_dense
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K] [CompactSpace K]
    {R : Set (X × K)} {D : Set X}
    (hR : IsClosed R) (hD : Dense D)
    (hDR : ∀ x ∈ D, ∃ k, (x, k) ∈ R) :
    ∀ x, ∃ k, (x, k) ∈ R := by
  have hclosed : IsClosed (Prod.fst '' R) :=
    isClosedMap_fst_of_compactSpace R hR
  have hDproj : D ⊆ Prod.fst '' R := by
    intro x hx
    obtain ⟨k, hk⟩ := hDR x hx
    exact ⟨(x, k), hk, rfl⟩
  have hall := eq_univ_of_isClosed_of_dense hclosed hD hDproj
  intro x
  have hx : x ∈ Prod.fst '' R := by rw [hall]; trivial
  rcases hx with ⟨⟨x', k⟩, hk, hxx'⟩
  exact ⟨k, hxx' ▸ hk⟩

/-! ## 4. The strictification is produced by `R < 1` alone -/

/-- Length transfer: a path of length at most `2` for the normalised polynomial
pulls back to a path of length strictly below `2`. -/
theorem mul_lt_two_of_lt_one {R L : ℝ} (hR0 : 0 < R) (hR1 : R < 1)
    (hL : L ≤ 2) :
    R * L < 2 := by
  nlinarith

/-- Level transfer: `|f| = R^n |g| <= R^n < 1`.  No slack is taken from the
hypothesis, which is why the Cassini degeneration cannot obstruct it. -/
theorem pow_mul_lt_one_of_lt_one {R v : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hR0 : 0 < R) (hR1 : R < 1) (hv : v ≤ 1) :
    R ^ n * v < 1 := by
  have hpow : R ^ n < 1 := pow_lt_one₀ hR0.le hR1 hn
  have hpow0 : 0 < R ^ n := pow_pos hR0 n
  nlinarith

/-! ## 5. The extremal family `z^n - 1` -/

/-- Exact sublevel characterisation: `|w - 1| <= 1` iff `|w|^2 <= 2 Re w`. -/
theorem normSq_sub_one_le_one_iff (w : ℂ) :
    Complex.normSq (w - 1) ≤ 1 ↔ Complex.normSq w ≤ 2 * w.re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith

/-- Off the origin the extremal sublevel set forces `Re(z^n) > 0`.  The `n`
sectors `|arg z - 2 pi k/n| < pi/(2n)` cut out by this inequality are pairwise
disjoint, which is the petal split used for the length lower bound. -/
theorem re_pow_pos_of_ne_zero {n : ℕ} {z : ℂ} (hz : z ≠ 0)
    (h : Complex.normSq (z ^ n - 1) ≤ 1) :
    0 < (z ^ n).re := by
  rw [normSq_sub_one_le_one_iff] at h
  have hpow : Complex.normSq (z ^ n) = Complex.normSq z ^ n := map_pow _ _ _
  have hz0 : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have : 0 < Complex.normSq z ^ n := pow_pos hz0 n
  rw [hpow] at h
  linarith

/-- Every radial segment `[0, w_k]` lies in the closed extremal lemniscate; the
statement is rotation invariant, so it is checked on the real ray.  This gives
the upper bound `Lam(z^n - 1) <= 2`. -/
theorem normSq_radial_sub_one_le_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (n : ℕ) :
    Complex.normSq ((t : ℂ) ^ n - 1) ≤ 1 := by
  have hcast : ((t : ℂ) ^ n - 1) = ((t ^ n - 1 : ℝ) : ℂ) := by push_cast; ring
  have hpow0 : 0 ≤ t ^ n := pow_nonneg h0 n
  have hpow1 : t ^ n ≤ 1 := pow_le_one₀ h0 h1
  rw [hcast, Complex.normSq_ofReal]
  nlinarith

end ErdosProblems.Erdos1041.GenericSufficiencyClosure
