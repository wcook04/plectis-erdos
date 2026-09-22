import ErdosProblems.Erdos1041.PaperCurveAssembly
import ErdosProblems.Erdos1041.PaperAnalyticTargets
import Mathlib

/-!
# Erdős 1041: the area/perimeter cluster

Three asserted environments of the long record
(`paper/reasoning-parts/erdos1041/core.tex`):

* `res:constant-factor-path` (line 739), a uniform path bound at level `2μ`;
* `res:constant-factor-arity` (line 882), the criterion using the number of
  roots at the first merger;
* `res:constant-factor-capacity` (line 924), the criterion using component
  capacity.

## What is assumed and what is proved

The paper's proof of `res:constant-factor-path` selects a regular level by
averaging `Area` against `dσ/σ`, lifts a radial direction through the univalent
inverse branches, and averages over adjacent pairs.  Its analytic inputs are
Pólya's area inequality `Area(K_T) ≤ π T^{2/n}`, the Koebe distortion theorem,
the coarea formula together with the boundary identity `|dz| = σ dφ/|f'|` and
total argument variation `2πk'`, and the area formula for the disjoint images of
univalent inverse branches.  None of Pólya, Koebe, the coarea formula for `|f|`
on regular levels, or logarithmic capacity is available in the pinned Mathlib,
and the paper states the boundary itself: "Theorem `res:constant-factor-path` is
ordinary mathematics with no Lean-checked part."

So the construction enters as one named hypothesis per row, stated as the
paper's own displayed bound with its two parameters `λ > 1`, `r ∈ (0,1)` intact:

* `CFAPathConstruction` — the bracket (CF) in full, with the factor `λ^{1/n}`;
* `CFAArityConstruction` — the same at `ρ ≤ 1` and `(λμ)^{1/n} ≤ 1`, which is
  how the arity corollary's proof uses it;
* `CFACapacityConstruction` — the rerun of the averaging proof with the
  component form `Area(C) ≤ π cap(closure C)² = π κ²(2μ)^{2/n}` of the
  area–capacity inequality at `λ = 2`, `r = 1/20`.

Proved here with no further input:

* every numerical step of all three environments — `√2 ≤ 283/200`,
  `2^{1/n} ≤ 63/50` for `n ≥ 3`, the five logarithm bounds obtained from
  `log 2` and `log q ≤ q - 1`, the resulting square-root bounds, the bracket
  estimates `< 71/10`, `< 5.7`, and the three squared-bracket estimates
  `< 34`, `< 24`, `< 20` of the arity corollary;
* the thresholds `τ_k = (√(2k) - A)/B` of the capacity corollary, the uniform
  cutoff `κ ≤ 1/3` for every `k₀ ≥ 2`, and each of the nine displayed rational
  cutoffs;
* the degenerate case `μ = 0` of both `res:constant-factor-path` and
  `res:constant-factor-arity` — a critical point of value zero forces a
  repeated root occurrence, and the constant path is exhibited;
* the degree-two case of `res:constant-factor-path`, where the root segment is
  built explicitly and its length `2ρ` and level `μ` are computed.

Names are prefixed `cfa`/`CFA` to avoid collision with the sibling
`PaperCompleteR21` modules.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial PaperCurve PaperAnalyticTargets

open scoped NNReal ENNReal BigOperators

/-! ## 1. Numerical toolkit -/

theorem cfaSqrt_le {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : Real.sqrt x ≤ y := by
  have hx : Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hy] at hx

theorem cfaSqrt_ge {x y : ℝ} (hy : 0 ≤ y) (h : y ^ 2 ≤ x) : y ≤ Real.sqrt x :=
  (Real.le_sqrt hy (le_trans (sq_nonneg y) h)).mpr h

/-- `log (2^m q) ≤ m·0.6931471808 + (q - 1)`, from `Real.log_two_lt_d9` and
`log q ≤ q - 1`.  Every logarithm the paper's brackets need has this shape. -/
theorem cfaLog_le (m : ℕ) {q : ℝ} (hq : 0 < q) :
    Real.log ((2 : ℝ) ^ m * q) ≤ (m : ℝ) * 0.6931471808 + (q - 1) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rw [Real.log_mul (ne_of_gt h2) (ne_of_gt hq), Real.log_pow]
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hq' : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos hq
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

theorem cfaLogTwo_lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9

theorem cfaPi_lt : Real.pi < 3.141593 := Real.pi_lt_d6

theorem cfaSqrtTwo_le : Real.sqrt 2 ≤ 283 / 200 := cfaSqrt_le (by norm_num) (by norm_num)

theorem cfaSqrtLogTwo_ge : (0.832 : ℝ) ≤ Real.sqrt (Real.log 2) :=
  cfaSqrt_ge (by norm_num) (by nlinarith [cfaLogTwo_lo])

theorem cfaSqrtLogFour_ge : (1.1774 : ℝ) ≤ Real.sqrt (Real.log 4) := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  rw [h4]
  exact cfaSqrt_ge (by norm_num) (by nlinarith [cfaLogTwo_lo])

theorem cfaSqrtLogEight_ge : (1.442 : ℝ) ≤ Real.sqrt (Real.log 8) := by
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
  rw [h8]
  exact cfaSqrt_ge (by norm_num) (by nlinarith [cfaLogTwo_lo])

theorem cfaPiDivSqrtLogTwo_le : Real.pi / Real.sqrt (Real.log 2) ≤ 3.776 := by
  have hge := cfaSqrtLogTwo_ge
  have hpos : (0 : ℝ) < Real.sqrt (Real.log 2) := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [cfaPi_lt, hge]

theorem cfaPiDivSqrtLogFour_le : Real.pi / Real.sqrt (Real.log 4) ≤ 2.6685 := by
  have hge := cfaSqrtLogFour_ge
  have hpos : (0 : ℝ) < Real.sqrt (Real.log 4) := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [cfaPi_lt, hge]

theorem cfaPiDivSqrtLogEight_le : Real.pi / Real.sqrt (Real.log 8) ≤ 2.1787 := by
  have hge := cfaSqrtLogEight_ge
  have hpos : (0 : ℝ) < Real.sqrt (Real.log 8) := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [cfaPi_lt, hge]

theorem cfaSqrtLog_forty_thirds_le : Real.sqrt (Real.log (40 / 3)) ≤ 1.6145 := by
  have hrw : (40 / 3 : ℝ) = (2 : ℝ) ^ (4 : ℕ) * (5 / 6) := by norm_num
  rw [hrw]
  exact cfaSqrt_le (by norm_num)
    (le_trans (cfaLog_le 4 (by norm_num)) (by norm_num))

theorem cfaSqrtLog_twohundred_thirteenths_le :
    Real.sqrt (Real.log (200 / 13)) ≤ 1.6536 := by
  have hrw : (200 / 13 : ℝ) = (2 : ℝ) ^ (4 : ℕ) * (25 / 26) := by norm_num
  rw [hrw]
  exact cfaSqrt_le (by norm_num)
    (le_trans (cfaLog_le 4 (by norm_num)) (by norm_num))

theorem cfaSqrtLog_hundred_thirds_le : Real.sqrt (Real.log (100 / 3)) ≤ 1.873 := by
  have hrw : (100 / 3 : ℝ) = (2 : ℝ) ^ (5 : ℕ) * (25 / 24) := by norm_num
  rw [hrw]
  exact cfaSqrt_le (by norm_num)
    (le_trans (cfaLog_le 5 (by norm_num)) (by norm_num))

theorem cfaSqrtLog_eighthundred_elevenths_le :
    Real.sqrt (Real.log (800 / 11)) ≤ 2.0726 := by
  have hrw : (800 / 11 : ℝ) = (2 : ℝ) ^ (6 : ℕ) * (25 / 22) := by norm_num
  rw [hrw]
  exact cfaSqrt_le (by norm_num)
    (le_trans (cfaLog_le 6 (by norm_num)) (by norm_num))

/-- The paper's bound `log 40 < (97/50)²`, in the form it is used. -/
theorem cfaSqrtLog_forty_le : Real.sqrt (Real.log 40) ≤ 97 / 50 := by
  have hrw : (40 : ℝ) = (2 : ℝ) ^ (5 : ℕ) * (5 / 4) := by norm_num
  rw [hrw]
  exact cfaSqrt_le (by norm_num)
    (le_trans (cfaLog_le 5 (by norm_num)) (by norm_num))

/-- `2^{1/3} ≤ 63/50`, because `(63/50)³ = 2.000376 > 2`. -/
theorem cfaTwoRpowThird_le : (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ 63 / 50 := by
  have hy0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by norm_num) _
  have hy3 : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = 2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 3)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hcube : (2 : ℝ) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) *
      (2 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
    have hrw : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)
        = (2 : ℝ) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) *
          (2 : ℝ) ^ ((1 : ℝ) / 3) := by ring
    rw [← hrw]; exact hy3
  by_contra hcon
  push_neg at hcon
  have h1 : (63 / 50 : ℝ) * (63 / 50) <
      (2 : ℝ) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) := by nlinarith
  have h2 : (63 / 50 : ℝ) * (63 / 50) * (63 / 50) <
      (2 : ℝ) ^ ((1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) *
        (2 : ℝ) ^ ((1 : ℝ) / 3) := by nlinarith
  rw [hcube] at h2
  norm_num at h2

/-- `2^{1/n} ≤ 63/50` for every degree `n ≥ 3`. -/
theorem cfaTwoRpow_le {n : ℕ} (hn : 3 ≤ n) : (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤ 63 / 50 := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hle : (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / 3 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle) cfaTwoRpowThird_le

/-! ## 2. Repeated roots at a zero critical value -/

/-- For `f = ∏ (X - z i)`, the derivative at a listed root is the product of the
gaps to the other listed roots. -/
theorem cfa_derivative_eval_at_root {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ}
    (hz : f = ∏ i, (X - C (z i))) (i₀ : Fin n) :
    f.derivative.eval (z i₀) = ∏ j ∈ Finset.univ.erase i₀, (z i₀ - z j) := by
  classical
  subst hz
  rw [derivative_prod_finset, eval_finset_sum]
  rw [Finset.sum_eq_single i₀]
  · simp [eval_prod]
  · intro b _ hb
    have hmem : i₀ ∈ Finset.univ.erase b := Finset.mem_erase.mpr ⟨hb.symm, Finset.mem_univ _⟩
    have : (∏ j ∈ Finset.univ.erase b, (X - C (z j))).eval (z i₀) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero hmem (by simp)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

/-- **The degenerate case.**  A critical point whose value is zero forces two
distinct occurrences of the same root: this is the paper's "a repeated zero
gives the constant path". -/
theorem cfa_repeated_occurrence {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {c : ℂ}
    (hz : f = ∏ i, (X - C (z i))) (hc : f.derivative.eval c = 0)
    (hfc : f.eval c = 0) : ∃ i j : Fin n, i ≠ j ∧ z i = z j := by
  classical
  by_contra hcon
  push_neg at hcon
  have hroot : ∃ i₀ : Fin n, c = z i₀ := by
    rw [hz, eval_prod] at hfc
    obtain ⟨i₀, -, hi₀⟩ := Finset.prod_eq_zero_iff.mp hfc
    exact ⟨i₀, by simpa [sub_eq_zero] using hi₀⟩
  obtain ⟨i₀, rfl⟩ := hroot
  rw [cfa_derivative_eval_at_root hz i₀, Finset.prod_eq_zero_iff] at hc
  obtain ⟨j, hj, hj0⟩ := hc
  exact hcon i₀ j (Ne.symm (Finset.mem_erase.mp hj).1) (by simpa [sub_eq_zero] using hj0)

/-! ## 3. The conclusion shapes -/

/-- Two zero occurrences joined by a path of length at most `L` inside the
closed sublevel set `{|f| ≤ R}`, with distinct locations when `f` is
squarefree. -/
def cfaJoinedAtMost {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ ConnectedAtMost f.eval R L (z i) (z j) ∧
    (Squarefree f → z i ≠ z j)

/-- Two zero occurrences joined by a path of length at most `L` inside the OPEN
sublevel set `{|f| < R}`. -/
def cfaJoinedBelow {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖f.eval (γ t)‖ < R) ∧
      BoundedVariationOn γ (Set.Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L) ∧
    (Squarefree f → z i ≠ z j)

theorem cfaJoinedAtMost_of_below {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {R L : ℝ}
    (h : cfaJoinedBelow f z R L) : cfaJoinedAtMost f z R L := by
  obtain ⟨i, j, hij, ⟨γ, hc, h0, h2, hlvl, hbv, hvar⟩, hsf⟩ := h
  exact ⟨i, j, hij, ⟨γ, hc, h0, h2, fun t ht => (hlvl t ht).le, hbv, hvar⟩, hsf⟩

theorem cfaJoinedBelow_mono {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {R L L' : ℝ}
    (h : cfaJoinedBelow f z R L) (hLL : L ≤ L') : cfaJoinedBelow f z R L' := by
  obtain ⟨i, j, hij, ⟨γ, hc, h0, h2, hlvl, hbv, hvar⟩, hsf⟩ := h
  exact ⟨i, j, hij, ⟨γ, hc, h0, h2, hlvl, hbv,
    le_trans hvar (ENNReal.ofReal_le_ofReal hLL)⟩, hsf⟩

/-- A repeated occurrence makes `f` non-squarefree. -/
theorem cfa_not_squarefree_of_repeated {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ}
    (hz : f = ∏ i, (X - C (z i))) {i j : Fin n} (hij : i ≠ j) (heq : z i = z j) :
    ¬ Squarefree f := by
  classical
  intro hsf
  have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have hprod : (∏ k ∈ ({i, j} : Finset (Fin n)), (X - C (z k))) ∣ f := by
    rw [hz]
    exact Finset.prod_dvd_prod_of_subset _ _ (fun k => (X - C (z k))) hsub
  have hpair : (∏ k ∈ ({i, j} : Finset (Fin n)), (X - C (z k)))
      = (X - C (z i)) * (X - C (z i)) := by
    rw [Finset.prod_pair hij, heq]
  rw [hpair] at hprod
  exact absurd (hsf _ hprod) (not_isUnit_X_sub_C (z i))

/-- The constant path at a repeated occurrence, closed level. -/
theorem cfa_constant_path {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {R L : ℝ}
    (hz : f = ∏ i, (X - C (z i))) {i j : Fin n} (hij : i ≠ j) (heq : z i = z j)
    (hR : ‖f.eval (z i)‖ ≤ R) (hL : 0 ≤ L) : cfaJoinedAtMost f z R L := by
  have hconst : ∀ u : ℝ, z i + (u : ℂ) * (z j - z i) = z i := by
    intro u; rw [← heq]; ring
  refine ⟨i, j, hij, ⟨hub (z i) (z i) (z j), (hub_continuous _ _ _).continuousOn,
    hub_zero _ _ _, hub_two _ _ _, ?_, hub_rectifiable _ _ _, ?_⟩,
    fun hsf => absurd hsf (cfa_not_squarefree_of_repeated hz hij heq)⟩
  · intro t ht
    refine hub_mem (S := {w : ℂ | ‖f.eval w‖ ≤ R}) ?_ ?_ ht
    · intro u _ _; simpa using hR
    · intro u _ _; rw [Set.mem_setOf_eq, hconst u]; exact hR
  · rw [hub_variation_ofReal]
    have hzero : ‖z i - z i‖ + ‖z j - z i‖ = 0 := by rw [← heq]; simp
    rw [hzero]
    simpa using ENNReal.ofReal_le_ofReal hL

/-- The constant path at a repeated occurrence, strict level. -/
theorem cfa_constant_path_below {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {R L : ℝ}
    (hz : f = ∏ i, (X - C (z i))) {i j : Fin n} (hij : i ≠ j) (heq : z i = z j)
    (hR : ‖f.eval (z i)‖ < R) (hL : 0 ≤ L) : cfaJoinedBelow f z R L := by
  have hconst : ∀ u : ℝ, z i + (u : ℂ) * (z j - z i) = z i := by
    intro u; rw [← heq]; ring
  refine ⟨i, j, hij, ⟨hub (z i) (z i) (z j), (hub_continuous _ _ _).continuousOn,
    hub_zero _ _ _, hub_two _ _ _, ?_, hub_rectifiable _ _ _, ?_⟩,
    fun hsf => absurd hsf (cfa_not_squarefree_of_repeated hz hij heq)⟩
  · intro t ht
    refine hub_mem (S := {w : ℂ | ‖f.eval w‖ < R}) ?_ ?_ ht
    · intro u _ _; simpa using hR
    · intro u _ _; rw [Set.mem_setOf_eq, hconst u]; exact hR
  · rw [hub_variation_ofReal]
    have hzero : ‖z i - z i‖ + ‖z j - z i‖ = 0 := by rw [← heq]; simp
    rw [hzero]
    simpa using ENNReal.ofReal_le_ofReal hL

/-- The degenerate branch, packaged: a least critical modulus `0` forces a
repeated occurrence and hence both constant-path conclusions. -/
theorem cfa_degenerate {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) (hμ0 : μ = 0) :
    ∃ i j : Fin n, i ≠ j ∧ z i = z j ∧ f.eval (z i) = 0 := by
  obtain ⟨⟨c, hc, hμc⟩, -⟩ := hμ
  have hfc : f.eval c = 0 := by
    have : ‖f.eval c‖ = 0 := by rw [← hμc, hμ0]
    simpa using this
  obtain ⟨i, j, hij, heq⟩ := cfa_repeated_occurrence hz hc hfc
  refine ⟨i, j, hij, heq, ?_⟩
  rw [hz, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-! ## 4. `res:constant-factor-path` -/

/-- The paper's displayed bracket (CF). -/
def cfaBracket (n k : ℕ) (lam r : ℝ) : ℝ :=
  Real.sqrt (2 / (k : ℝ)) *
    (Real.sqrt 2 * r / (1 - r) ^ 2 +
      lam ^ ((1 : ℝ) / (n : ℝ)) *
        (Real.sqrt (Real.log (lam / r)) + Real.pi / Real.sqrt (Real.log lam)))

/-- **External input for `res:constant-factor-path`.**  The paper's construction:
for a squarefree monic `f` of degree `n ≥ 3` with least critical modulus `μ > 0`,
every `r ∈ (0,1)` and `λ > 1` give a selected component with `k ≥ 2` roots and a
path in `{|f| < λμ}` between two zero occurrences of length at most the bracket
(CF) times `ρ = μ^{1/n}`.  Its ingredients are Pólya's area inequality, the
Koebe distortion theorem, the coarea formula with the boundary identity
`|dz| = σ dφ/|f'|` and total argument variation `2πk'`, the area formula for the
disjoint images of the univalent inverse branches, and the mean-value selection
of a regular level and of a direction avoiding the critical-value arguments.
The containment is strict because the proof selects a regular level strictly
inside its positive-measure window, which is what the paper's own `{|f| < 1}`
clause uses. -/
def CFAPathConstruction : Prop :=
  ∀ (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (μ lam r : ℝ),
    3 ≤ n → f.Monic → f.natDegree = n → RootEnumeration f z →
    CriticalMinimum f μ → 0 < μ → 0 < r → r < 1 → 1 < lam →
    ∃ k : ℕ, 2 ≤ k ∧
      cfaJoinedBelow f z (lam * μ) (cfaBracket n k lam r * μ ^ ((1 : ℝ) / (n : ℝ)))

/-- The bracket at `λ = 2`, `r = 3/20` is below `71/10` in every degree `n ≥ 3`
and for every root count `k ≥ 2`.  The largest case is `n = 3`, `k = 2`. -/
theorem cfaBracket_two_three_twentieths_lt {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k) :
    cfaBracket n k 2 (3 / 20) ≤ 71 / 10 := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hfac : Real.sqrt (2 / (k : ℝ)) ≤ 1 :=
    cfaSqrt_le (by norm_num) (by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (k : ℝ))]; nlinarith)
  have hfac0 : 0 ≤ Real.sqrt (2 / (k : ℝ)) := Real.sqrt_nonneg _
  have hlam : (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤ 63 / 50 := cfaTwoRpow_le hn
  have hlam0 : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hratio : (2 : ℝ) / (3 / 20) = 40 / 3 := by norm_num
  have hlog : Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) ≤ 1.6145 := by
    rw [hratio]; exact cfaSqrtLog_forty_thirds_le
  have hlog0 : 0 ≤ Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) := Real.sqrt_nonneg _
  have hpi := cfaPiDivSqrtLogTwo_le
  have hpi0 : 0 ≤ Real.pi / Real.sqrt (Real.log 2) := by positivity
  have hfirst : Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 ≤ 0.2938 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (1 - 3 / 20 : ℝ) ^ 2)]
    nlinarith [cfaSqrtTwo_le, Real.sqrt_nonneg 2]
  have hfirst0 : 0 ≤ Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 := by positivity
  have hinner : Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 +
      (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) *
        (Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) + Real.pi / Real.sqrt (Real.log 2))
      ≤ 71 / 10 := by
    have hsum : Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) +
        Real.pi / Real.sqrt (Real.log 2) ≤ 5.3905 := by linarith
    nlinarith [hlam, hlam0, hfirst, hsum, hlog0, hpi0]
  have hinner0 : 0 ≤ Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 +
      (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) *
        (Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) + Real.pi / Real.sqrt (Real.log 2)) := by
    have : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) *
        (Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) + Real.pi / Real.sqrt (Real.log 2)) :=
      mul_nonneg hlam0 (by linarith)
    linarith
  unfold cfaBracket
  nlinarith [hfac, hfac0, hinner, hinner0]

/-- At `μ ≤ 1/2` the same bracket is below `5.7`, because `λ^{1/n}ρ = (2μ)^{1/n} ≤ 1`
and `ρ ≤ 1`.  This is the closing numerical display of the theorem's proof. -/
theorem cfaBracket_five_point_seven {k : ℕ} (hk : 2 ≤ k) :
    Real.sqrt (2 / (k : ℝ)) *
        (Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 +
          (Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) + Real.pi / Real.sqrt (Real.log 2)))
      ≤ 5.7 := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hfac : Real.sqrt (2 / (k : ℝ)) ≤ 1 :=
    cfaSqrt_le (by norm_num) (by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (k : ℝ))]; nlinarith)
  have hfac0 : 0 ≤ Real.sqrt (2 / (k : ℝ)) := Real.sqrt_nonneg _
  have hratio : (2 : ℝ) / (3 / 20) = 40 / 3 := by norm_num
  have hlog : Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) ≤ 1.6145 := by
    rw [hratio]; exact cfaSqrtLog_forty_thirds_le
  have hlog0 : 0 ≤ Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) := Real.sqrt_nonneg _
  have hpi := cfaPiDivSqrtLogTwo_le
  have hpi0 : 0 ≤ Real.pi / Real.sqrt (Real.log 2) := by positivity
  have hfirst : Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 ≤ 0.2938 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (1 - 3 / 20 : ℝ) ^ 2)]
    nlinarith [cfaSqrtTwo_le, Real.sqrt_nonneg 2]
  have hfirst0 : 0 ≤ Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 := by positivity
  nlinarith [hfac, hfac0, hfirst, hfirst0, hlog, hlog0, hpi, hpi0]

/-! ## 5. `res:constant-factor-arity` -/

/-- The arity corollary's bracket: the (CF) bracket after the reductions
`ρ ≤ 1` and `(λμ)^{1/n} ≤ 1` that its proof performs. -/
def cfaArityBracket (lam r : ℝ) : ℝ :=
  Real.sqrt 2 * r / (1 - r) ^ 2 + Real.sqrt (Real.log (lam / r)) +
    Real.pi / Real.sqrt (Real.log lam)

/-- **External input for `res:constant-factor-arity`.**  The same construction as
`CFAPathConstruction`, in the shape its corollary's proof uses: every selected
component contains the first-merge component, so its root count is at least
`k₀`, and the reductions `ρ ≤ 1`, `(λμ)^{1/n} ≤ 1` available when `λμ ≤ 1` have
already been made. -/
def CFAArityConstruction (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (k₀ : ℕ) (lam r : ℝ) : Prop :=
  cfaJoinedBelow f z 1 (Real.sqrt (2 / (k₀ : ℝ)) * cfaArityBracket lam r)

theorem cfaArityBracket_nonneg {lam r : ℝ} (hr : 0 < r) (hr1 : r < 1) (hlam : 1 < lam) :
    0 ≤ cfaArityBracket lam r := by
  unfold cfaArityBracket
  have h1 : 0 ≤ Real.sqrt 2 * r / (1 - r) ^ 2 := by positivity
  have h2 : 0 ≤ Real.sqrt (Real.log (lam / r)) := Real.sqrt_nonneg _
  have h3 : 0 ≤ Real.pi / Real.sqrt (Real.log lam) := by positivity
  linarith

/-- `λ = 2`, `r = 13/100`: the squared bracket is below `34`. -/
theorem cfaArityBracket_case_one : (cfaArityBracket 2 (13 / 100)) ^ 2 ≤ 34 := by
  have hratio : (2 : ℝ) / (13 / 100) = 200 / 13 := by norm_num
  have hlog : Real.sqrt (Real.log ((2 : ℝ) / (13 / 100))) ≤ 1.6536 := by
    rw [hratio]; exact cfaSqrtLog_twohundred_thirteenths_le
  have hlog0 : 0 ≤ Real.sqrt (Real.log ((2 : ℝ) / (13 / 100))) := Real.sqrt_nonneg _
  have hpi := cfaPiDivSqrtLogTwo_le
  have hpi0 : 0 ≤ Real.pi / Real.sqrt (Real.log 2) := by positivity
  have hfirst : Real.sqrt 2 * (13 / 100) / (1 - 13 / 100) ^ 2 ≤ 0.2431 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (1 - 13 / 100 : ℝ) ^ 2)]
    nlinarith [cfaSqrtTwo_le, Real.sqrt_nonneg 2]
  have hfirst0 : 0 ≤ Real.sqrt 2 * (13 / 100) / (1 - 13 / 100) ^ 2 := by positivity
  unfold cfaArityBracket
  nlinarith [hfirst, hfirst0, hlog, hlog0, hpi, hpi0]

/-- `λ = 4`, `r = 3/25`: the squared bracket is below `24`. -/
theorem cfaArityBracket_case_two : (cfaArityBracket 4 (3 / 25)) ^ 2 ≤ 24 := by
  have hratio : (4 : ℝ) / (3 / 25) = 100 / 3 := by norm_num
  have hlog : Real.sqrt (Real.log ((4 : ℝ) / (3 / 25))) ≤ 1.873 := by
    rw [hratio]; exact cfaSqrtLog_hundred_thirds_le
  have hlog0 : 0 ≤ Real.sqrt (Real.log ((4 : ℝ) / (3 / 25))) := Real.sqrt_nonneg _
  have hpi := cfaPiDivSqrtLogFour_le
  have hpi0 : 0 ≤ Real.pi / Real.sqrt (Real.log 4) := by positivity
  have hfirst : Real.sqrt 2 * (3 / 25) / (1 - 3 / 25) ^ 2 ≤ 0.2193 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (1 - 3 / 25 : ℝ) ^ 2)]
    nlinarith [cfaSqrtTwo_le, Real.sqrt_nonneg 2]
  have hfirst0 : 0 ≤ Real.sqrt 2 * (3 / 25) / (1 - 3 / 25) ^ 2 := by positivity
  unfold cfaArityBracket
  nlinarith [hfirst, hfirst0, hlog, hlog0, hpi, hpi0]

/-- `λ = 8`, `r = 11/100`: the squared bracket is below `20`. -/
theorem cfaArityBracket_case_three : (cfaArityBracket 8 (11 / 100)) ^ 2 ≤ 20 := by
  have hratio : (8 : ℝ) / (11 / 100) = 800 / 11 := by norm_num
  have hlog : Real.sqrt (Real.log ((8 : ℝ) / (11 / 100))) ≤ 2.0726 := by
    rw [hratio]; exact cfaSqrtLog_eighthundred_elevenths_le
  have hlog0 : 0 ≤ Real.sqrt (Real.log ((8 : ℝ) / (11 / 100))) := Real.sqrt_nonneg _
  have hpi := cfaPiDivSqrtLogEight_le
  have hpi0 : 0 ≤ Real.pi / Real.sqrt (Real.log 8) := by positivity
  have hfirst : Real.sqrt 2 * (11 / 100) / (1 - 11 / 100) ^ 2 ≤ 0.1966 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (1 - 11 / 100 : ℝ) ^ 2)]
    nlinarith [cfaSqrtTwo_le, Real.sqrt_nonneg 2]
  have hfirst0 : 0 ≤ Real.sqrt 2 * (11 / 100) / (1 - 11 / 100) ^ 2 := by positivity
  unfold cfaArityBracket
  nlinarith [hfirst, hfirst0, hlog, hlog0, hpi, hpi0]

/-- The arity step: a squared bracket below `2k₀` closes the path below `2`. -/
theorem cfaArity_length_le {k₀ : ℕ} {B : ℝ} (hk : 2 ≤ k₀) (hB0 : 0 ≤ B)
    (hB : B ^ 2 ≤ 2 * (k₀ : ℝ)) : Real.sqrt (2 / (k₀ : ℝ)) * B ≤ 2 := by
  have hkR : (2 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k₀ : ℝ) := by linarith
  have hsq : Real.sqrt (2 / (k₀ : ℝ)) ^ 2 = 2 / (k₀ : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (2 / (k₀ : ℝ)) := Real.sqrt_nonneg _
  have hprod : (Real.sqrt (2 / (k₀ : ℝ)) * B) ^ 2 ≤ 4 := by
    rw [mul_pow, hsq, div_mul_eq_mul_div, div_le_iff₀ hkpos]
    nlinarith [hB, hkpos]
  nlinarith [hprod, mul_nonneg hs0 hB0]

/-! ## 6. `res:constant-factor-capacity` -/

/-- The paper's `A = 283/3610` and `B = 52029/9100`. -/
def cfaA : ℝ := 283 / 3610

def cfaB : ℝ := 52029 / 9100

/-- The paper's threshold `τ_k = (√(2k) - A)/B`. -/
def cfaTau (k : ℕ) : ℝ := (Real.sqrt (2 * (k : ℝ)) - cfaA) / cfaB

/-- The paper's exact bound `A ≥ √2·(1/20)/(19/20)²`. -/
theorem cfaA_bound : Real.sqrt 2 * (1 / 20) / (1 - 1 / 20) ^ 2 ≤ cfaA := by
  unfold cfaA
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (1 - 1 / 20 : ℝ) ^ 2)]
  nlinarith [cfaSqrtTwo_le, Real.sqrt_nonneg 2]

/-- The paper's exact bound `B ≥ √(log 40) + π/√(log 2)`. -/
theorem cfaB_bound :
    Real.sqrt (Real.log 40) + Real.pi / Real.sqrt (Real.log 2) ≤ cfaB := by
  unfold cfaB
  have h1 := cfaSqrtLog_forty_le
  have h2 := cfaPiDivSqrtLogTwo_le
  norm_num
  linarith

/-- **External input for `res:constant-factor-capacity`.**  The averaging proof of
`res:constant-factor-path`, rerun on the component `C` of `{|f| < 2μ}` containing
the first-merge critical point, with the global area input replaced by the
component form `Area(C) ≤ π cap(closure C)² = π κ²(2μ)^{2/n}` of the
area–capacity inequality, at `λ = 2`, `r = 1/20`.  `κ` is the paper's capacity
ratio `cap(closure C)/(2μ)^{1/n}`; the pinned Mathlib has no logarithmic
capacity, so `κ` enters as the real parameter this hypothesis is stated for. -/
def CFACapacityConstruction (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (κ : ℝ) (k₀ : ℕ) : Prop :=
  cfaJoinedBelow f z 1
    (Real.sqrt (2 / (k₀ : ℝ)) *
      (Real.sqrt 2 * (1 / 20) / (1 - 1 / 20) ^ 2 +
        κ * (Real.sqrt (Real.log 40) + Real.pi / Real.sqrt (Real.log 2))))

/-- **`res:constant-factor-capacity`, main clause.**  If the capacity ratio `κ` of
the selected component is at most `τ_{k₀}`, the construction closes below `2`,
so Erdős #1041 holds for `f`. -/
theorem cfa_capacity_criterion {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {κ : ℝ} {k₀ : ℕ}
    (hk₀ : 2 ≤ k₀) (hκ0 : 0 ≤ κ) (hκ : κ ≤ cfaTau k₀)
    (hext : CFACapacityConstruction n f z κ k₀) :
    cfaJoinedBelow f z 1 2 := by
  obtain ⟨i, j, hij, ⟨γ, hc, h0, h2, hlvl, hbv, hvar⟩, hsf⟩ := hext
  refine ⟨i, j, hij, ⟨γ, hc, h0, h2, hlvl, hbv, ?_⟩, hsf⟩
  refine le_trans hvar (ENNReal.ofReal_le_ofReal ?_)
  have hkR : (2 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
  have hkpos : (0 : ℝ) < (k₀ : ℝ) := by linarith
  have hB0 : (0 : ℝ) < cfaB := by unfold cfaB; norm_num
  have hkey : Real.sqrt 2 * (1 / 20) / (1 - 1 / 20) ^ 2 +
      κ * (Real.sqrt (Real.log 40) + Real.pi / Real.sqrt (Real.log 2))
      ≤ Real.sqrt (2 * (k₀ : ℝ)) := by
    have h1 := cfaA_bound
    have h2' : κ * (Real.sqrt (Real.log 40) + Real.pi / Real.sqrt (Real.log 2))
        ≤ κ * cfaB := mul_le_mul_of_nonneg_left cfaB_bound hκ0
    have h3 : cfaA + cfaB * κ ≤ Real.sqrt (2 * (k₀ : ℝ)) := by
      unfold cfaTau at hκ
      rw [le_div_iff₀ hB0] at hκ
      linarith
    linarith [h1, h2', h3]
  have hs0 : 0 ≤ Real.sqrt (2 / (k₀ : ℝ)) := Real.sqrt_nonneg _
  have hmul : Real.sqrt (2 / (k₀ : ℝ)) * Real.sqrt (2 * (k₀ : ℝ)) = 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (2 / (k₀ : ℝ)) * (2 * (k₀ : ℝ)) = 4 by field_simp; ring]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc Real.sqrt (2 / (k₀ : ℝ)) *
        (Real.sqrt 2 * (1 / 20) / (1 - 1 / 20) ^ 2 +
          κ * (Real.sqrt (Real.log 40) + Real.pi / Real.sqrt (Real.log 2)))
      ≤ Real.sqrt (2 / (k₀ : ℝ)) * Real.sqrt (2 * (k₀ : ℝ)) :=
        mul_le_mul_of_nonneg_left hkey hs0
    _ = 2 := hmul

/-- Every rational cutoff `q` with `(A + Bq)² ≤ 2k` lies below `τ_k`. -/
theorem cfaTau_ge_of_sq {k : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (h : (cfaA + cfaB * q) ^ 2 ≤ 2 * (k : ℝ)) : q ≤ cfaTau k := by
  have hB0 : (0 : ℝ) < cfaB := by unfold cfaB; norm_num
  have hA0 : (0 : ℝ) < cfaA := by unfold cfaA; norm_num
  have hnn : 0 ≤ cfaA + cfaB * q := by positivity
  have hsq : cfaA + cfaB * q ≤ Real.sqrt (2 * (k : ℝ)) := cfaSqrt_ge hnn h
  unfold cfaTau
  rw [le_div_iff₀ hB0]
  linarith

/-- **`κ ≤ 1/3` suffices for every root count `k₀ ≥ 2`.** -/
theorem cfaTau_third {k : ℕ} (hk : 2 ≤ k) : (1 : ℝ) / 3 ≤ cfaTau k := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  refine cfaTau_ge_of_sq (by norm_num) ?_
  unfold cfaA cfaB
  nlinarith [hkR]

/-- **The displayed rational cutoffs** `2/5, 12/25, 1/2, 7/12, 16/25, 2/3, 7/10`
at `k₀ = 3, …, 9`, rising to `39/40` at `k₀ = 16`. -/
theorem cfaTau_cutoffs :
    (2 / 5 : ℝ) ≤ cfaTau 3 ∧ (12 / 25 : ℝ) ≤ cfaTau 4 ∧ (1 / 2 : ℝ) ≤ cfaTau 5 ∧
    (7 / 12 : ℝ) ≤ cfaTau 6 ∧ (16 / 25 : ℝ) ≤ cfaTau 7 ∧ (2 / 3 : ℝ) ≤ cfaTau 8 ∧
    (7 / 10 : ℝ) ≤ cfaTau 9 ∧ (39 / 40 : ℝ) ≤ cfaTau 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (refine cfaTau_ge_of_sq (by norm_num) ?_; unfold cfaA cfaB; norm_num)

/-! ## 7. The degree-two case of `res:constant-factor-path` -/

theorem cfaJoinedBelow_mono_level {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {R R' L : ℝ}
    (h : cfaJoinedBelow f z R L) (hRR : R ≤ R') : cfaJoinedBelow f z R' L := by
  obtain ⟨i, j, hij, ⟨γ, hc, h0, h2, hlvl, hbv, hvar⟩, hsf⟩ := h
  exact ⟨i, j, hij, ⟨γ, hc, h0, h2, fun t ht => lt_of_lt_of_le (hlvl t ht) hRR, hbv, hvar⟩, hsf⟩

/-- In degree two the least critical modulus is the squared half-gap. -/
theorem cfa_degree_two_mu {f : ℂ[X]} {z : Fin 2 → ℂ} {μ : ℝ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) :
    μ = ‖(z 0 - z 1) / 2‖ ^ 2 := by
  have hz' : f = ∏ i, (X - C (z i)) := hz
  obtain ⟨⟨c, hc, hμc⟩, -⟩ := hμ
  have hev : ∀ w : ℂ, f.eval w = (w - z 0) * (w - z 1) := by
    intro w; rw [hz', Fin.prod_univ_two]; simp
  have hd : ∀ w : ℂ, f.derivative.eval w = 2 * w - z 0 - z 1 := by
    intro w
    rw [hz', Fin.prod_univ_two, derivative_mul]
    simp
    ring
  rw [hd c] at hc
  have hc' : c = (z 0 + z 1) / 2 := by linear_combination hc / 2
  rw [hμc, hc', hev]
  have hfac : ((z 0 + z 1) / 2 - z 0) * ((z 0 + z 1) / 2 - z 1)
      = -(((z 0 - z 1) / 2) ^ 2) := by ring
  rw [hfac, norm_neg, norm_pow]

/-- The degree-two root segment: it lies below every level above `μ` and has
length `2ρ`. -/
theorem cfa_degree_two_below {f : ℂ[X]} {z : Fin 2 → ℂ} {μ R L : ℝ}
    (hz' : f = ∏ i, (X - C (z i))) (hmu : μ = ‖(z 0 - z 1) / 2‖ ^ 2)
    (hR : μ < R) (hL : ‖z 0 - z 1‖ ≤ L) : cfaJoinedBelow f z R L := by
  have hij : (0 : Fin 2) ≠ 1 := by decide
  have hev : ∀ w : ℂ, f.eval w = (w - z 0) * (w - z 1) := by
    intro w; rw [hz', Fin.prod_univ_two]; simp
  have hd2 : ‖(z 0 - z 1) / 2‖ = ‖z 0 - z 1‖ / 2 := by
    rw [norm_div]; norm_num
  have hmu' : μ = (‖z 0 - z 1‖ / 2) ^ 2 := by rw [hmu, hd2]
  have hμ0 : 0 ≤ μ := by rw [hmu]; positivity
  refine ⟨0, 1, hij, ⟨hub (z 0) (z 1) (z 1), (hub_continuous _ _ _).continuousOn,
    hub_zero _ _ _, hub_two _ _ _, ?_, hub_rectifiable _ _ _, ?_⟩,
    fun hsf heq => cfa_not_squarefree_of_repeated hz' hij heq hsf⟩
  · intro t ht
    refine hub_mem (S := {w : ℂ | ‖f.eval w‖ < R}) ?_ ?_ ht
    · intro u hu0 hu1
      rw [Set.mem_setOf_eq, hev]
      have he : (z 1 + (u : ℂ) * (z 0 - z 1) - z 0) * (z 1 + (u : ℂ) * (z 0 - z 1) - z 1)
          = ((u : ℂ) * ((u : ℂ) - 1)) * (z 0 - z 1) ^ 2 := by ring
      rw [he, norm_mul, norm_mul, norm_pow]
      have hun : ‖(u : ℂ)‖ = u := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      have hun1 : ‖((u : ℂ) - 1)‖ = 1 - u := by
        have hcast : ((u : ℂ) - 1) = (((u - 1 : ℝ)) : ℂ) := by push_cast; ring
        rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - u)]
      rw [hun, hun1]
      nlinarith [mul_nonneg (sq_nonneg (u - 1 / 2)) (sq_nonneg ‖z 0 - z 1‖),
        norm_nonneg (z 0 - z 1), hR, hmu']
    · intro u _ _
      have he : z 1 + (u : ℂ) * (z 1 - z 1) = z 1 := by ring
      rw [Set.mem_setOf_eq, he, hev]
      have : (z 1 - z 0) * (z 1 - z 1) = 0 := by ring
      rw [this, norm_zero]
      linarith
  · rw [hub_variation_ofReal]
    have hsum : ‖z 1 - z 0‖ + ‖z 1 - z 1‖ = ‖z 0 - z 1‖ := by
      rw [norm_sub_rev]; simp
    rw [hsum]
    exact ENNReal.ofReal_le_ofReal hL

/-! ## 8. `res:constant-factor-path`, assembled -/

/-- **`res:constant-factor-path` (core.tex line 739).**

Conditional on `CFAPathConstruction`: for every monic `f` of degree `n ≥ 2`, two
zero occurrences are joined by a possibly degenerate path of length at most
`(71/10)ρ` inside `K_{2μ}`, with distinct locations when `f` is squarefree; and
if `μ ≤ 1/2` the construction may be chosen inside `{|f| < 1}` with length at
most `5.7`. -/
theorem cfa_constant_factor_path (hext : CFAPathConstruction)
    {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hn : 2 ≤ n) (hmonic : f.Monic) (hdeg : f.natDegree = n)
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) :
    cfaJoinedAtMost f z (2 * μ) ((71 / 10) * μ ^ ((1 : ℝ) / (n : ℝ))) ∧
      (μ ≤ 1 / 2 → cfaJoinedBelow f z 1 5.7) := by
  have hz' : f = ∏ i, (X - C (z i)) := hz
  have hμ0 : 0 ≤ μ := by
    obtain ⟨⟨c, hc, hμc⟩, -⟩ := hμ
    rw [hμc]; exact norm_nonneg _
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hexp0 : (1 : ℝ) / (n : ℝ) ≠ 0 := by positivity
  have hexpnn : (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) := by positivity
  rcases eq_or_lt_of_le hμ0 with h0 | hpos
  · obtain ⟨i, j, hij, heq, hroot⟩ := cfa_degenerate hz hμ h0.symm
    have hrho : μ ^ ((1 : ℝ) / (n : ℝ)) = 0 := by
      rw [← h0]; exact Real.zero_rpow hexp0
    constructor
    · refine cfa_constant_path hz' hij heq ?_ ?_
      · rw [hroot, norm_zero, ← h0]; norm_num
      · rw [hrho]; norm_num
    · intro _
      exact cfa_constant_path_below hz' hij heq (by rw [hroot, norm_zero]; norm_num)
        (by norm_num)
  · have hrho0 : (0 : ℝ) ≤ μ ^ ((1 : ℝ) / (n : ℝ)) := Real.rpow_nonneg hμ0 _
    rcases eq_or_lt_of_le hn with hn2 | hn3
    · subst hn2
      have hmu := cfa_degree_two_mu hz hμ
      have hd2 : ‖(z 0 - z 1) / 2‖ = ‖z 0 - z 1‖ / 2 := by rw [norm_div]; norm_num
      have hbase : (0 : ℝ) ≤ ‖z 0 - z 1‖ / 2 := by positivity
      have hrho : μ ^ ((1 : ℝ) / (((2 : ℕ) : ℝ))) = ‖z 0 - z 1‖ / 2 := by
        rw [hmu, hd2, ← Real.rpow_natCast (‖z 0 - z 1‖ / 2) 2, ← Real.rpow_mul hbase]
        norm_num
      constructor
      · refine cfaJoinedAtMost_of_below (cfa_degree_two_below hz' hmu (by linarith) ?_)
        rw [hrho]
        linarith [norm_nonneg (z 0 - z 1)]
      · intro hhalf
        refine cfa_degree_two_below hz' hmu (by linarith) ?_
        nlinarith [norm_nonneg (z 0 - z 1), hmu, hd2, hhalf]
    · have hn3' : 3 ≤ n := hn3
      obtain ⟨k, hk, hjoin⟩ := hext n f z μ 2 (3 / 20) hn3' hmonic hdeg hz hμ hpos
        (by norm_num) (by norm_num) (by norm_num)
      constructor
      · refine cfaJoinedAtMost_of_below (cfaJoinedBelow_mono hjoin ?_)
        exact mul_le_mul_of_nonneg_right
          (cfaBracket_two_three_twentieths_lt hn3' hk) hrho0
      · intro hhalf
        refine cfaJoinedBelow_mono_level (cfaJoinedBelow_mono hjoin ?_) (by linarith)
        have hfac0 : (0 : ℝ) ≤ Real.sqrt (2 / (k : ℝ)) := Real.sqrt_nonneg _
        have hA0 : (0 : ℝ) ≤ Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 := by positivity
        have hSP0 : (0 : ℝ) ≤ Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) +
            Real.pi / Real.sqrt (Real.log 2) := by positivity
        have hrho1 : μ ^ ((1 : ℝ) / (n : ℝ)) ≤ 1 :=
          Real.rpow_le_one hμ0 (by linarith) hexpnn
        have htwo : (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * μ ^ ((1 : ℝ) / (n : ℝ))
            = (2 * μ) ^ ((1 : ℝ) / (n : ℝ)) := (Real.mul_rpow (by norm_num) hμ0).symm
        have htwo1 : (2 * μ) ^ ((1 : ℝ) / (n : ℝ)) ≤ 1 :=
          Real.rpow_le_one (by linarith) (by linarith) hexpnn
        have hexpand : cfaBracket n k 2 (3 / 20) * μ ^ ((1 : ℝ) / (n : ℝ))
            = Real.sqrt (2 / (k : ℝ)) *
              ((Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2) * μ ^ ((1 : ℝ) / (n : ℝ)) +
                ((2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * μ ^ ((1 : ℝ) / (n : ℝ))) *
                  (Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) +
                    Real.pi / Real.sqrt (Real.log 2))) := by
          unfold cfaBracket; ring
        rw [hexpand]
        refine le_trans (mul_le_mul_of_nonneg_left ?_ hfac0)
          (cfaBracket_five_point_seven hk)
        have h1 : (Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2) * μ ^ ((1 : ℝ) / (n : ℝ))
            ≤ Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 := by nlinarith
        have h2 : ((2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) * μ ^ ((1 : ℝ) / (n : ℝ))) *
            (Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) +
              Real.pi / Real.sqrt (Real.log 2))
            ≤ Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) +
              Real.pi / Real.sqrt (Real.log 2) := by
          rw [htwo]; nlinarith
        linarith

/-! ## 9. `res:constant-factor-arity`, assembled -/

/-- **`res:constant-factor-arity` (core.tex line 882).**

Conditional on `CFAArityConstruction` in the relevant case: Erdős #1041 holds
for `f` in each of `μ ≤ 1/2` with `k₀ ≥ 17`, `μ ≤ 1/4` with `k₀ ≥ 12`, and
`μ ≤ 1/8` with `k₀ ≥ 10`.  The degenerate case `μ = 0` is proved outright. -/
theorem cfa_arity_criterion {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ} {k₀ : ℕ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ)
    (hcase : 0 < μ →
      (μ ≤ 1 / 2 ∧ 17 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 2 (13 / 100)) ∨
      (μ ≤ 1 / 4 ∧ 12 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 4 (3 / 25)) ∨
      (μ ≤ 1 / 8 ∧ 10 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 8 (11 / 100))) :
    cfaJoinedBelow f z 1 2 := by
  have hz' : f = ∏ i, (X - C (z i)) := hz
  have hμ0 : 0 ≤ μ := by
    obtain ⟨⟨c, hc, hμc⟩, -⟩ := hμ
    rw [hμc]; exact norm_nonneg _
  rcases eq_or_lt_of_le hμ0 with h0 | hpos
  · obtain ⟨i, j, hij, heq, hroot⟩ := cfa_degenerate hz hμ h0.symm
    exact cfa_constant_path_below hz' hij heq (by rw [hroot, norm_zero]; norm_num)
      (by norm_num)
  · rcases hcase hpos with ⟨-, hk, hjoin⟩ | ⟨-, hk, hjoin⟩ | ⟨-, hk, hjoin⟩
    · refine cfaJoinedBelow_mono hjoin (cfaArity_length_le (by omega)
        (cfaArityBracket_nonneg (by norm_num) (by norm_num) (by norm_num)) ?_)
      have hkR : (17 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk
      linarith [cfaArityBracket_case_one]
    · refine cfaJoinedBelow_mono hjoin (cfaArity_length_le (by omega)
        (cfaArityBracket_nonneg (by norm_num) (by norm_num) (by norm_num)) ?_)
      have hkR : (12 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk
      linarith [cfaArityBracket_case_two]
    · refine cfaJoinedBelow_mono hjoin (cfaArity_length_le (by omega)
        (cfaArityBracket_nonneg (by norm_num) (by norm_num) (by norm_num)) ?_)
      have hkR : (10 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk
      linarith [cfaArityBracket_case_three]

#print axioms cfaSqrt_le
#print axioms cfaSqrt_ge
#print axioms cfa_not_squarefree_of_repeated
#print axioms cfa_degenerate
#print axioms cfa_degree_two_mu
#print axioms cfa_degree_two_below
#print axioms cfa_constant_factor_path
#print axioms cfa_arity_criterion
#print axioms cfaLog_le
#print axioms cfaSqrtTwo_le
#print axioms cfaPiDivSqrtLogTwo_le
#print axioms cfaSqrtLog_forty_thirds_le
#print axioms cfaSqrtLog_twohundred_thirteenths_le
#print axioms cfaSqrtLog_hundred_thirds_le
#print axioms cfaSqrtLog_eighthundred_elevenths_le
#print axioms cfaSqrtLog_forty_le
#print axioms cfaTwoRpow_le
#print axioms cfa_derivative_eval_at_root
#print axioms cfa_repeated_occurrence
#print axioms cfaBracket_two_three_twentieths_lt
#print axioms cfaBracket_five_point_seven
#print axioms cfaArityBracket_case_one
#print axioms cfaArityBracket_case_two
#print axioms cfaArityBracket_case_three
#print axioms cfaArity_length_le
#print axioms cfaA_bound
#print axioms cfaB_bound
#print axioms cfa_capacity_criterion
#print axioms cfaTau_third
#print axioms cfaTau_cutoffs

end ErdosProblems.Erdos1041.PaperCompleteR21
