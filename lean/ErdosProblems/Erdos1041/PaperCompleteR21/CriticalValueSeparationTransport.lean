import Mathlib

/-!
# Erdős 1041: the all-degree critical-value separation theorem and its uniform radius

This file carries four asserted environments of the #1041 papers.

* `res:critical-value-separation`, long record
  (`paper/reasoning-parts/erdos1041/core.tex`, line 1341) and short note
  (`paper/1041/erdos-1041-lemniscate-newton-flow.tex`, line 653).
* `res:critical-value-thresholds`, long record (line 1534) and short note
  (line 678).

## What is proved outright and what is assumed

The paper's proof of the separation theorem runs
*component degree two* → *square-root resolution* → *conformal chart onto the
disc* → *Bergman segment inequality* → *exterior-Blaschke fibre capacity gap* →
*Pólya's area–capacity inequality*.  The pinned Mathlib has no Riemann mapping
theorem, no Bergman kernel or Bergman space, no logarithmic capacity and no
Pólya inequality, so that chain cannot be carried out here.  It enters as the
single named hypothesis `DiscSepBergmanArea`, stated in exactly the shape the
paper's proof produces it: for a normalised separation datum there are a
square-root connector of length `L` and a component area `area` with

* `L² ≤ (2/π) · log((1 + q²)/(1 - q²)) · area`   (the paper's display (7)), and
* `area ≤ π (S/(n-1))^(2/n)`                     (capacity gap plus Pólya),

where `q² = S/(S² + p)` is the squared radius of the image of `[-1,1]` under the
paper's explicit chart `ζ`.

Everything else is proved here with no further input:

* the chart geometry — `S² - S + p = (S - w₀)(S - (1 - w₀))`, hence `0 < q² < 1`,
  and the Bergman-factor identity `(1 + q²)/(1 - q²) = (S² + S + p)/(S² - S + p)`,
  which is exactly where the lower bound `S > max(w₀, 1 - w₀)` enters;
* the star-shapedness of the square-root target `{ξ : |ξ² - a| < S}` and the fact
  that the Möbius map `w ↦ Sw/(S² + aw - a²)` carries `D(a,S)` into the unit disc
  and sends `1` to `q²`;
* the derived clauses of the theorem — the endpoints of the connector are
  distinct roots and the connector lies in `{|P| ≤ 1}`;
* the substitution giving the displayed bound (5) and its consequence (6);
* the unnormalised (short-note) form, by constructing the paper's normalisation
  `P(w) = f(c + |v|^{1/n} w)/v` as an actual polynomial, verifying every
  normalised hypothesis for it, and transporting the connector through
  `z = c + |v|^{1/n} w`;
* the whole numerical half of `res:critical-value-thresholds`, namely
  `(S/(n-1))^(2/n) log((S²+S+p)/(S²-S+p)) < 2` for `n ≥ 3`, `p ≥ 0`,
  `4/3 ≤ S ≤ 2`, and the degree-three branch-centred constant
  `(3/5)^(2/3) log 11 < 2`.

Names are prefixed `discSep`/`DiscSep` so that they do not collide with
`PaperCompleteR21/DiskFamilySeparationThreshold.lean`, which carries the same
numerical threshold under the names `separationCoefficient*`.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial

open scoped NNReal ENNReal

/-! ## 1. The paper's hypotheses and its connector -/

/-- The hypotheses of the long record's Theorem `res:critical-value-separation`
(`core.tex` line 1341) on the normalised polynomial `P`: degree `n ≥ 3`, leading
coefficient of modulus one, `P(0) = 1`, `P'(0) = 0`, `P''(0) ≠ 0`, a real centre
`w₀ ∈ [0,1]`, a radius `S > max(w₀, 1 - w₀)`, and the separation `|P(d) - w₀| ≥ S`
at every other critical point. -/
structure DiscSepNormalised (P : ℂ[X]) (n : ℕ) (w₀ S : ℝ) : Prop where
  three_le : 3 ≤ n
  degree : P.natDegree = n
  leading : ‖P.leadingCoeff‖ = 1
  value_zero : P.eval 0 = 1
  crit_zero : P.derivative.eval 0 = 0
  simple : P.derivative.derivative.eval 0 ≠ 0
  centre_nonneg : 0 ≤ w₀
  centre_le_one : w₀ ≤ 1
  radius : max w₀ (1 - w₀) < S
  separated : ∀ d : ℂ, d ≠ 0 → P.derivative.eval d = 0 → S ≤ ‖P.eval d - (w₀ : ℂ)‖

/-- The paper's connector: the two local solutions of `P(Z ξ) = 1 - ξ²` with
`Z 0 = 0`, continued along the real segment `[-1,1]` into one injective
rectifiable curve of length at most `L`. -/
structure DiscSepConnector (P : ℂ[X]) (Z : ℝ → ℂ) (L : ℝ) : Prop where
  cont : ContinuousOn Z (Set.Icc (-1 : ℝ) 1)
  inj : Set.InjOn Z (Set.Icc (-1 : ℝ) 1)
  centre : Z 0 = 0
  equation : ∀ ξ ∈ Set.Icc (-1 : ℝ) 1, P.eval (Z ξ) = 1 - (ξ : ℂ) ^ 2
  rect : BoundedVariationOn Z (Set.Icc (-1 : ℝ) 1)
  length_nonneg : 0 ≤ L
  length : eVariationOn Z (Set.Icc (-1 : ℝ) 1) ≤ ENNReal.ofReal L

namespace DiscSepConnector

variable {P : ℂ[X]} {Z : ℝ → ℂ} {L : ℝ}

theorem mem_left : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num

theorem mem_right : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num

/-- The right endpoint of the connector is a root of `P`. -/
theorem eval_right (h : DiscSepConnector P Z L) : P.eval (Z 1) = 0 := by
  rw [h.equation 1 mem_right]
  push_cast
  norm_num

/-- The left endpoint of the connector is a root of `P`. -/
theorem eval_left (h : DiscSepConnector P Z L) : P.eval (Z (-1)) = 0 := by
  rw [h.equation (-1) mem_left]
  push_cast
  norm_num

/-- The two endpoints are distinct. -/
theorem endpoints_ne (h : DiscSepConnector P Z L) : Z (-1) ≠ Z 1 := by
  intro hEq
  have h' := h.inj mem_left mem_right hEq
  norm_num at h'

/-- `Γ ⊆ {|P| ≤ 1}`: the containment clause follows from the functional
equation alone. -/
theorem contained (h : DiscSepConnector P Z L) :
    ∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (Z ξ)‖ ≤ 1 := by
  intro ξ hξ
  rw [h.equation ξ hξ]
  have hcast : (1 : ℂ) - (ξ : ℂ) ^ 2 = (((1 - ξ ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast]
  have hn : ‖(((1 - ξ ^ 2 : ℝ)) : ℂ)‖ = |1 - ξ ^ 2| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hn, abs_le]
  obtain ⟨h1, h2⟩ := hξ
  constructor <;> nlinarith

end DiscSepConnector

/-! ## 2. The chart radius and the disc-family coefficient -/

/-- The squared radius `q² = S/(S² + p)` of the image of `[-1,1]` under the
paper's chart `ζ`. -/
def discSepQsq (S p : ℝ) : ℝ := S / (S ^ 2 + p)

/-- The left-hand side of the paper's display (6),
`(S/(n-1))^(2/n) · log((S² + S + p)/(S² - S + p))`. -/
def discSepCoefficient (n : ℕ) (S p : ℝ) : ℝ :=
  (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
    Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))

/-- The paper's factorisation `S² - S + p = (S - w₀)(S - (1 - w₀))`. -/
theorem discSep_denominator_factor (w₀ S : ℝ) :
    S ^ 2 - S + w₀ * (1 - w₀) = (S - w₀) * (S - (1 - w₀)) := by ring

/-- This is exactly where `S > max(w₀, 1 - w₀)` enters the length estimate. -/
theorem discSep_denominator_pos {w₀ S : ℝ} (h : max w₀ (1 - w₀) < S) :
    0 < S ^ 2 - S + w₀ * (1 - w₀) := by
  rw [discSep_denominator_factor]
  have h1 : w₀ < S := lt_of_le_of_lt (le_max_left _ _) h
  have h2 : 1 - w₀ < S := lt_of_le_of_lt (le_max_right _ _) h
  nlinarith

theorem discSep_radius_pos {w₀ S : ℝ} (hw₀ : 0 ≤ w₀) (h : max w₀ (1 - w₀) < S) :
    0 < S :=
  lt_of_le_of_lt (le_trans hw₀ (le_max_left _ _)) h

/-- `0 < q² < 1`, as the Bergman segment inequality requires. -/
theorem discSep_qsq_mem {w₀ S : ℝ} (hw₀ : 0 ≤ w₀) (h : max w₀ (1 - w₀) < S) :
    0 < discSepQsq S (w₀ * (1 - w₀)) ∧ discSepQsq S (w₀ * (1 - w₀)) < 1 := by
  have hS := discSep_radius_pos hw₀ h
  have hden := discSep_denominator_pos h
  have hsum : 0 < S ^ 2 + w₀ * (1 - w₀) := by linarith
  refine ⟨div_pos hS hsum, ?_⟩
  unfold discSepQsq
  rw [div_lt_one hsum]
  linarith

/-- The Bergman factor in the chart coordinate is the paper's ratio:
`(1 + q²)/(1 - q²) = (S² + S + p)/(S² - S + p)`. -/
theorem discSep_bergman_factor {S p : ℝ} (hS : 0 < S) (hden : 0 < S ^ 2 - S + p) :
    (1 + discSepQsq S p) / (1 - discSepQsq S p)
      = (S ^ 2 + S + p) / (S ^ 2 - S + p) := by
  have hsum : (0 : ℝ) < S ^ 2 + p := by linarith
  have h1 : (S ^ 2 + p) ≠ 0 := ne_of_gt hsum
  have h2 : (S ^ 2 - S + p) ≠ 0 := ne_of_gt hden
  have e2 : 1 - discSepQsq S p = (S ^ 2 - S + p) / (S ^ 2 + p) := by
    unfold discSepQsq
    field_simp
    try ring
  have e2ne : 1 - discSepQsq S p ≠ 0 := by
    rw [e2]; exact div_ne_zero h2 h1
  rw [div_eq_div_iff e2ne h2]
  unfold discSepQsq
  field_simp
  try ring

/-- The logarithmic factor is nonnegative in the admissible range. -/
theorem discSep_log_nonneg {S p : ℝ} (hS : 0 < S) (hden : 0 < S ^ 2 - S + p) :
    0 ≤ Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ hden]
  linarith

/-! ## 3. The square-root target and the explicit chart -/

/-- The square-root target `Q̃ = {ξ : |ξ² - a| < S}` is star-shaped about `0`:
`t²ξ²` is a convex combination of `ξ²` and `0`, both in the disc `D(a,S)` because
`S > a ≥ 0`.  Hence `Q̃` is connected and simply connected, which is what the
paper's covering argument uses. -/
theorem discSep_target_starShaped {a S : ℝ} (ha : 0 ≤ a) (haS : a < S) {ξ : ℂ}
    (hξ : ‖ξ ^ 2 - (a : ℂ)‖ < S) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((t : ℂ) * ξ) ^ 2 - (a : ℂ)‖ < S := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have key : ((t : ℂ) * ξ) ^ 2 - (a : ℂ)
      = ((t ^ 2 : ℝ) : ℂ) * (ξ ^ 2 - (a : ℂ)) + (((t ^ 2 - 1 : ℝ)) : ℂ) * (a : ℂ) := by
    push_cast; ring
  have e1 : ‖((t ^ 2 : ℝ) : ℂ)‖ = t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  have e2 : ‖(((t ^ 2 - 1 : ℝ)) : ℂ)‖ = 1 - t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t ^ 2)]
  have e3 : ‖((a : ℝ) : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have hb : ‖((t : ℂ) * ξ) ^ 2 - (a : ℂ)‖
      ≤ t ^ 2 * ‖ξ ^ 2 - (a : ℂ)‖ + (1 - t ^ 2) * a := by
    rw [key]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, e1, e2, e3]
  rcases eq_or_lt_of_le (sq_nonneg t) with h0 | h0
  · have hzero : t ^ 2 = 0 := h0.symm
    rw [hzero] at hb
    linarith
  · nlinarith [hb, mul_pos h0 (sub_pos.mpr hξ),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t ^ 2) (by linarith : (0 : ℝ) ≤ S - a)]

/-- The paper's Möbius map `w ↦ Sw/(S² + aw - a²)` carries the disc `D(a,S)`
into the unit disc.  Stated as a strict comparison of the two moduli, which also
shows that its denominator does not vanish on `D(a,S)`. -/
theorem discSep_mobius_norm_lt {a S : ℝ} (ha : 0 ≤ a) (haS : a < S) {w : ℂ}
    (hw : ‖w - (a : ℂ)‖ < S) :
    ‖(S : ℂ) * w‖ < ‖(S : ℂ) ^ 2 + (a : ℂ) * w - (a : ℂ) ^ 2‖ := by
  have hS : 0 < S := lt_of_le_of_lt ha haS
  have hD : 0 < S ^ 2 - a ^ 2 := by nlinarith
  have hw2 : Complex.normSq (w - (a : ℂ)) < S ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (w - (a : ℂ))]
  have hre : (w - (a : ℂ)).re = w.re - a := by simp
  have him : (w - (a : ℂ)).im = w.im := by simp
  rw [Complex.normSq_apply, hre, him] at hw2
  have hz : (S : ℂ) ^ 2 + (a : ℂ) * w - (a : ℂ) ^ 2
      = (((S ^ 2 - a ^ 2 : ℝ)) : ℂ) + (a : ℂ) * w := by push_cast; ring
  have hnum : Complex.normSq ((S : ℂ) * w) = S ^ 2 * (w.re * w.re + w.im * w.im) := by
    rw [Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hden : Complex.normSq ((((S ^ 2 - a ^ 2 : ℝ)) : ℂ) + (a : ℂ) * w)
      = ((S ^ 2 - a ^ 2) + a * w.re) * ((S ^ 2 - a ^ 2) + a * w.re)
        + (a * w.im) * (a * w.im) := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hgap : 0 < (S ^ 2 - a ^ 2) + 2 * a * w.re - (w.re * w.re + w.im * w.im) := by
    nlinarith [hw2]
  have hkey : Complex.normSq ((S : ℂ) * w)
      < Complex.normSq ((S : ℂ) ^ 2 + (a : ℂ) * w - (a : ℂ) ^ 2) := by
    rw [hz, hnum, hden]
    nlinarith [mul_pos hD hgap]
  have h1 : ‖(S : ℂ) * w‖ ^ 2 < ‖(S : ℂ) ^ 2 + (a : ℂ) * w - (a : ℂ) ^ 2‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    exact hkey
  nlinarith [norm_nonneg ((S : ℂ) * w),
    norm_nonneg ((S : ℂ) ^ 2 + (a : ℂ) * w - (a : ℂ) ^ 2), h1]

/-- At `ξ = 1` the chart lands on `q² = S/(S² + p)`, with `a = 1 - w₀` and
`p = w₀(1 - w₀)`.  This identifies the paper's radius `q`. -/
theorem discSep_mobius_at_one (w₀ S : ℝ) :
    S * 1 / (S ^ 2 + (1 - w₀) * 1 - (1 - w₀) ^ 2) = discSepQsq S (w₀ * (1 - w₀)) := by
  unfold discSepQsq
  ring_nf

/-! ## 4. The external classical input and the long-record theorem -/

/-- **The external classical input.**

In the paper's proof of `res:critical-value-separation` this is the chain
Riemann-mapping/covering theory (the proper local biholomorphism `ξ : U → Q̃` is a
conformal bijection because `Q̃` is star-shaped, hence simply connected) → the
Bergman segment inequality, display (7) → the exterior-Blaschke fibre capacity
gap `cap(closure U')ⁿ/S' < 1/(n-1)` → Pólya's area–capacity inequality
`Area(K) ≤ π cap(K)²`.  None of Riemann mapping, the Bergman kernel, logarithmic
capacity or Pólya is available in the pinned Mathlib, so the chain is taken here
as one named hypothesis, in exactly the form the paper's proof delivers it. -/
def DiscSepBergmanArea : Prop :=
  ∀ (P : ℂ[X]) (n : ℕ) (w₀ S : ℝ), DiscSepNormalised P n w₀ S →
    ∃ (Z : ℝ → ℂ) (L area : ℝ),
      DiscSepConnector P Z L ∧
      L ^ 2 ≤ 2 / Real.pi *
        Real.log ((1 + discSepQsq S (w₀ * (1 - w₀))) /
          (1 - discSepQsq S (w₀ * (1 - w₀)))) * area ∧
      area ≤ Real.pi * (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ))

/-- Substituting the area bound into the Bergman segment inequality gives the
paper's display (5).  This is the step where the chart radius `q` is eliminated
in favour of `(S² + S + p)/(S² - S + p)`. -/
theorem discSep_squared_length_le {n : ℕ} {w₀ S L area : ℝ}
    (hw₀ : 0 ≤ w₀) (hS : max w₀ (1 - w₀) < S)
    (hBergman : L ^ 2 ≤ 2 / Real.pi *
      Real.log ((1 + discSepQsq S (w₀ * (1 - w₀))) /
        (1 - discSepQsq S (w₀ * (1 - w₀)))) * area)
    (hArea : area ≤ Real.pi * (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ))) :
    L ^ 2 ≤ 2 * discSepCoefficient n S (w₀ * (1 - w₀)) := by
  have hSpos := discSep_radius_pos hw₀ hS
  have hdenp := discSep_denominator_pos hS
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  rw [discSep_bergman_factor (p := w₀ * (1 - w₀)) hSpos hdenp] at hBergman
  have hlg0 : 0 ≤ Real.log ((S ^ 2 + S + w₀ * (1 - w₀)) /
      (S ^ 2 - S + w₀ * (1 - w₀))) := discSep_log_nonneg hSpos hdenp
  have hcoef0 : 0 ≤ 2 / Real.pi * Real.log ((S ^ 2 + S + w₀ * (1 - w₀)) /
      (S ^ 2 - S + w₀ * (1 - w₀))) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hArea hcoef0
  have hval : 2 / Real.pi * Real.log ((S ^ 2 + S + w₀ * (1 - w₀)) /
        (S ^ 2 - S + w₀ * (1 - w₀))) *
        (Real.pi * (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)))
      = 2 * discSepCoefficient n S (w₀ * (1 - w₀)) := by
    unfold discSepCoefficient
    field_simp
    try ring
  rw [hval] at hstep
  linarith

/-- The consumer of display (6): a squared bound by twice a coefficient below
two forces the connector to be shorter than two. -/
theorem discSep_length_lt_two {M L : ℝ} (hL : 0 ≤ L) (hbound : L ^ 2 ≤ 2 * M)
    (hM : M < 2) : L < 2 := by nlinarith

/-- **`res:critical-value-separation`, long record (`core.tex` line 1341).**

Conditional on the classical chain `DiscSepBergmanArea`, a normalised separation
datum yields one injective connector `Z` obtained by continuing the two local
solutions of `P(Z ξ) = 1 - ξ²` with `Z 0 = 0` along the real segment; its
endpoints are distinct roots of `P`; it lies in `{|P| ≤ 1}`; its length obeys
display (5); and, whenever display (6) holds, it is shorter than `2`. -/
theorem discSep_separation_long (hext : DiscSepBergmanArea)
    {P : ℂ[X]} {n : ℕ} {w₀ S : ℝ} (hyp : DiscSepNormalised P n w₀ S) :
    ∃ (Z : ℝ → ℂ) (L : ℝ),
      DiscSepConnector P Z L ∧
      P.eval (Z (-1)) = 0 ∧ P.eval (Z 1) = 0 ∧ Z (-1) ≠ Z 1 ∧
      (∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (Z ξ)‖ ≤ 1) ∧
      L ^ 2 ≤ 2 * discSepCoefficient n S (w₀ * (1 - w₀)) ∧
      (discSepCoefficient n S (w₀ * (1 - w₀)) < 2 → L < 2) := by
  obtain ⟨Z, L, area, hZ, hBergman, hArea⟩ := hext P n w₀ S hyp
  have hsq := discSep_squared_length_le hyp.centre_nonneg hyp.radius hBergman hArea
  exact ⟨Z, L, hZ, hZ.eval_left, hZ.eval_right, hZ.endpoints_ne, hZ.contained, hsq,
    fun hcoef => discSep_length_lt_two hZ.length_nonneg hsq hcoef⟩

/-! ## 5. The paper's normalisation `P(w) = f(c + |v|^{1/n} w)/v` -/

/-- The paper's normalisation, as an actual polynomial. -/
def discSepNormalise (f : ℂ[X]) (c : ℂ) (r : ℝ) (v : ℂ) : ℂ[X] :=
  (f.comp (C (r : ℂ) * X + C c)) * C v⁻¹

theorem discSepNormalise_eval (f : ℂ[X]) (c : ℂ) (r : ℝ) (v w : ℂ) :
    (discSepNormalise f c r v).eval w = f.eval ((r : ℂ) * w + c) * v⁻¹ := by
  unfold discSepNormalise
  simp [eval_comp]

/-- Differentiating the normalisation renormalises it: the same construction on
`f'`, with `v` replaced by `v/r`. -/
theorem discSepNormalise_derivative (f : ℂ[X]) (c : ℂ) (r : ℝ) (v : ℂ) :
    (discSepNormalise f c r v).derivative
      = discSepNormalise f.derivative c r (v * (r : ℂ)⁻¹) := by
  have hq : derivative (C (r : ℂ) * X + C c) = C (r : ℂ) := by simp
  have hinv : ((v * (r : ℂ)⁻¹)⁻¹) = (r : ℂ) * v⁻¹ := by
    rw [mul_inv, inv_inv]; ring
  unfold discSepNormalise
  rw [derivative_mul, derivative_C, mul_zero, add_zero, derivative_comp, hq, hinv, C_mul]
  ring

theorem discSepNormalise_natDegree {f : ℂ[X]} {c v : ℂ} {r : ℝ}
    (hr : r ≠ 0) (hv : v ≠ 0) (hf : f ≠ 0) :
    (discSepNormalise f c r v).natDegree = f.natDegree := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hq : (C (r : ℂ) * X + C c).natDegree = 1 := natDegree_linear hrC
  have hlc : (f.comp (C (r : ℂ) * X + C c)).leadingCoeff
      = f.leadingCoeff * (r : ℂ) ^ f.natDegree := by
    rw [leadingCoeff_comp (by rw [hq]; norm_num), leadingCoeff_linear hrC]
  have hfl : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hcne : f.comp (C (r : ℂ) * X + C c) ≠ 0 := by
    intro hzero
    rw [hzero, leadingCoeff_zero] at hlc
    exact (mul_ne_zero hfl (pow_ne_zero _ hrC)) hlc.symm
  unfold discSepNormalise
  rw [natDegree_mul hcne (C_ne_zero.mpr (inv_ne_zero hv)), natDegree_C, add_zero,
    natDegree_comp, hq, mul_one]

theorem discSepNormalise_leadingCoeff {f : ℂ[X]} {c v : ℂ} {r : ℝ}
    (hr : r ≠ 0) (hv : v ≠ 0) :
    (discSepNormalise f c r v).leadingCoeff
      = f.leadingCoeff * (r : ℂ) ^ f.natDegree * v⁻¹ := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hq : (C (r : ℂ) * X + C c).natDegree = 1 := natDegree_linear hrC
  unfold discSepNormalise
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp (by rw [hq]; norm_num),
    leadingCoeff_linear hrC]

/-- The construction satisfies every hypothesis of `DiscSepNormalised` when `f`
is monic of degree `n ≥ 3`, `c` is a simple critical point, `v = f(c) ≠ 0` and
`r = |v|^{1/n}`. -/
theorem discSepNormalise_spec {f : ℂ[X]} {n : ℕ} {c v : ℂ} {r w₀ S : ℝ}
    (hn : 3 ≤ n) (hdeg : f.natDegree = n) (hmonic : f.Monic)
    (hcrit : f.derivative.eval c = 0)
    (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hvdef : v = f.eval c) (hv : v ≠ 0)
    (hrdef : r = ‖v‖ ^ (1 / (n : ℝ)))
    (hw₀ : 0 ≤ w₀) (hw₁ : w₀ ≤ 1) (hS : max w₀ (1 - w₀) < S)
    (hsep : ∀ d : ℂ, d ≠ c → f.derivative.eval d = 0 → S ≤ ‖f.eval d / v - (w₀ : ℂ)‖) :
    DiscSepNormalised (discSepNormalise f c r v) n w₀ S := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hrpos : 0 < r := by rw [hrdef]; exact Real.rpow_pos_of_pos hvpos _
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hrne
  have hfne : f ≠ 0 := hmonic.ne_zero
  have hrpow : r ^ n = ‖v‖ := by
    rw [hrdef, one_div]
    exact Real.rpow_inv_natCast_pow (le_of_lt hvpos) (by omega)
  have hdegP : (discSepNormalise f c r v).natDegree = n := by
    rw [discSepNormalise_natDegree hrne hv hfne, hdeg]
  have hleadP : ‖(discSepNormalise f c r v).leadingCoeff‖ = 1 := by
    rw [discSepNormalise_leadingCoeff hrne hv, hmonic.leadingCoeff, one_mul, hdeg,
      norm_mul, norm_pow, norm_inv]
    have hrn : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hrpos]
    rw [hrn, hrpow]
    field_simp
  have hderiv : ∀ w : ℂ, (discSepNormalise f c r v).derivative.eval w
      = f.derivative.eval ((r : ℂ) * w + c) * (v * (r : ℂ)⁻¹)⁻¹ := by
    intro w
    rw [discSepNormalise_derivative, discSepNormalise_eval]
  have hderiv2 : ∀ w : ℂ, (discSepNormalise f c r v).derivative.derivative.eval w
      = f.derivative.derivative.eval ((r : ℂ) * w + c) *
        (v * (r : ℂ)⁻¹ * (r : ℂ)⁻¹)⁻¹ := by
    intro w
    rw [discSepNormalise_derivative, discSepNormalise_derivative, discSepNormalise_eval]
  refine ⟨hn, hdegP, hleadP, ?_, ?_, ?_, hw₀, hw₁, hS, ?_⟩
  · rw [discSepNormalise_eval]
    simp only [mul_zero, zero_add, ← hvdef]
    exact mul_inv_cancel₀ hv
  · rw [hderiv 0]
    simp only [mul_zero, zero_add, hcrit, zero_mul]
  · rw [hderiv2 0]
    simp only [mul_zero, zero_add]
    exact mul_ne_zero hsimple
      (inv_ne_zero (mul_ne_zero (mul_ne_zero hv (inv_ne_zero hrC)) (inv_ne_zero hrC)))
  · intro d hd hcritd
    have hh := hderiv d
    rw [hcritd] at hh
    have hne : (v * (r : ℂ)⁻¹)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hv (inv_ne_zero hrC))
    have hfd : f.derivative.eval ((r : ℂ) * d + c) = 0 :=
      (mul_eq_zero.mp hh.symm).resolve_right hne
    have hdne : (r : ℂ) * d + c ≠ c := by
      intro hEq
      have h0 : (r : ℂ) * d = 0 := by linear_combination hEq
      rcases mul_eq_zero.mp h0 with h | h
      · exact hrC h
      · exact hd h
    have hres := hsep ((r : ℂ) * d + c) hdne hfd
    rw [discSepNormalise_eval, ← div_eq_mul_inv]
    exact hres

/-! ## 6. Transporting the connector back to `f` -/

/-- Scaling the normalised connector by `z = c + r w`.  This is the paper's
closing step: the length is multiplied by `r`, the level `{|P| ≤ 1}` becomes
`{|f| ≤ |v|}`, and the endpoints stay distinct roots. -/
theorem discSep_transport {f P : ℂ[X]} {c v : ℂ} {r L : ℝ} {Z : ℝ → ℂ}
    (hr : 0 < r) (hv : v ≠ 0)
    (hP : ∀ w : ℂ, P.eval w = f.eval ((r : ℂ) * w + c) * v⁻¹)
    (hZ : DiscSepConnector P Z L) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (-1 : ℝ) 1) ∧
      γ (-1) ≠ γ 1 ∧ f.eval (γ (-1)) = 0 ∧ f.eval (γ 1) = 0 ∧
      (∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖f.eval (γ ξ)‖ ≤ ‖v‖) ∧
      BoundedVariationOn γ (Set.Icc (-1 : ℝ) 1) ∧
      eVariationOn γ (Set.Icc (-1 : ℝ) 1) ≤ ENNReal.ofReal (r * L) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hrn : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  have hlip : LipschitzWith (Real.toNNReal r) (fun z : ℂ => (r : ℂ) * z + c) := by
    apply LipschitzWith.of_dist_le_mul
    intro z1 z2
    simp only [dist_eq_norm]
    have hsub : ((r : ℂ) * z1 + c) - ((r : ℂ) * z2 + c) = (r : ℂ) * (z1 - z2) := by ring
    rw [hsub, norm_mul, hrn, Real.coe_toNNReal _ hr.le]
  have hcontφ : Continuous (fun z : ℂ => (r : ℂ) * z + c) :=
    (continuous_const.mul continuous_id).add continuous_const
  have hfeval : ∀ w : ℂ, f.eval ((r : ℂ) * w + c) = v * P.eval w := by
    intro w
    rw [hP w]
    field_simp
  refine ⟨fun ξ => (r : ℂ) * Z ξ + c, hcontφ.comp_continuousOn hZ.cont, ?_, ?_, ?_, ?_,
    hlip.comp_boundedVariationOn hZ.rect, ?_⟩
  · intro hEq
    apply hZ.endpoints_ne
    have h2 : (r : ℂ) * Z (-1) = (r : ℂ) * Z 1 := by
      have := hEq
      simp only at this
      linear_combination this
    exact mul_left_cancel₀ hrC h2
  · show f.eval ((r : ℂ) * Z (-1) + c) = 0
    rw [hfeval, hZ.eval_left, mul_zero]
  · show f.eval ((r : ℂ) * Z 1 + c) = 0
    rw [hfeval, hZ.eval_right, mul_zero]
  · intro ξ hξ
    show ‖f.eval ((r : ℂ) * Z ξ + c)‖ ≤ ‖v‖
    rw [hfeval, norm_mul]
    have hc := hZ.contained ξ hξ
    nlinarith [norm_nonneg v, norm_nonneg (P.eval (Z ξ)), hc]
  · calc eVariationOn (fun ξ : ℝ => (r : ℂ) * Z ξ + c) (Set.Icc (-1 : ℝ) 1)
        ≤ (Real.toNNReal r : ℝ≥0∞) * eVariationOn Z (Set.Icc (-1 : ℝ) 1) :=
          hlip.lipschitzOnWith.comp_eVariationOn_le (Set.mapsTo_univ _ _)
      _ ≤ (Real.toNNReal r : ℝ≥0∞) * ENNReal.ofReal L := mul_le_mul_left' hZ.length _
      _ = ENNReal.ofReal r * ENNReal.ofReal L := rfl
      _ = ENNReal.ofReal (r * L) := (ENNReal.ofReal_mul hr.le).symm

/-! ## 7. The short-note separation theorem -/

/-- **`res:critical-value-separation`, short note
(`erdos-1041-lemniscate-newton-flow.tex` line 653).**

Conditional on `DiscSepBergmanArea`: with `f` monic of degree `n ≥ 3`, `c` a
simple critical point, `v = f(c) ≠ 0`, `w₀ ∈ [0,1]`, `S > max(w₀, 1-w₀)` and
`|f(d)/v - w₀| ≥ S` at every other critical point `d`, two distinct roots of `f`
are joined inside `{|f| ≤ |v|}` by a rectifiable curve `Γ` with

`length(Γ)² ≤ 2 |v|^{2/n} (S/(n-1))^{2/n} log((S²+S+p)/(S²-S+p))`,  `p = w₀(1-w₀)`. -/
theorem discSep_separation_short (hext : DiscSepBergmanArea)
    {f : ℂ[X]} {n : ℕ} {c : ℂ} {w₀ S : ℝ}
    (hn : 3 ≤ n) (hdeg : f.natDegree = n) (hmonic : f.Monic)
    (hcrit : f.derivative.eval c = 0)
    (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hv : f.eval c ≠ 0)
    (hw₀ : 0 ≤ w₀) (hw₁ : w₀ ≤ 1) (hS : max w₀ (1 - w₀) < S)
    (hsep : ∀ d : ℂ, d ≠ c → f.derivative.eval d = 0 →
      S ≤ ‖f.eval d / f.eval c - (w₀ : ℂ)‖) :
    ∃ (a b : ℂ) (γ : ℝ → ℂ) (Lf : ℝ), a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      ContinuousOn γ (Set.Icc (-1 : ℝ) 1) ∧ γ (-1) = a ∧ γ 1 = b ∧
      (∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖f.eval (γ ξ)‖ ≤ ‖f.eval c‖) ∧
      BoundedVariationOn γ (Set.Icc (-1 : ℝ) 1) ∧
      0 ≤ Lf ∧ eVariationOn γ (Set.Icc (-1 : ℝ) 1) ≤ ENNReal.ofReal Lf ∧
      Lf ^ 2 ≤ 2 * ‖f.eval c‖ ^ ((2 : ℝ) / (n : ℝ)) *
        discSepCoefficient n S (w₀ * (1 - w₀)) := by
  have hvpos : 0 < ‖f.eval c‖ := norm_pos_iff.mpr hv
  have hrpos : 0 < ‖f.eval c‖ ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos hvpos _
  have hspec := discSepNormalise_spec (v := f.eval c) (r := ‖f.eval c‖ ^ (1 / (n : ℝ)))
    hn hdeg hmonic hcrit hsimple rfl hv rfl hw₀ hw₁ hS hsep
  obtain ⟨Z, L, hZ, -, -, -, -, hsq, -⟩ := discSep_separation_long hext hspec
  obtain ⟨γ, hγcont, hγne, hγ0l, hγ0r, hγlvl, hγbv, hγvar⟩ :=
    discSep_transport hrpos hv
      (discSepNormalise_eval f c (‖f.eval c‖ ^ (1 / (n : ℝ))) (f.eval c)) hZ
  refine ⟨γ (-1), γ 1, γ, ‖f.eval c‖ ^ (1 / (n : ℝ)) * L, hγne, hγ0l, hγ0r, hγcont,
    rfl, rfl, hγlvl, hγbv, mul_nonneg hrpos.le hZ.length_nonneg, hγvar, ?_⟩
  have hr2 : (‖f.eval c‖ ^ (1 / (n : ℝ))) ^ 2 = ‖f.eval c‖ ^ ((2 : ℝ) / (n : ℝ)) := by
    rw [← Real.rpow_natCast (‖f.eval c‖ ^ (1 / (n : ℝ))) 2,
      ← Real.rpow_mul (le_of_lt hvpos)]
    congr 1
    push_cast
    ring
  have hexp : (‖f.eval c‖ ^ (1 / (n : ℝ)) * L) ^ 2
      = ‖f.eval c‖ ^ ((2 : ℝ) / (n : ℝ)) * L ^ 2 := by
    rw [mul_pow, hr2]
  rw [hexp]
  have hpos : (0 : ℝ) < ‖f.eval c‖ ^ ((2 : ℝ) / (n : ℝ)) := Real.rpow_pos_of_pos hvpos _
  calc ‖f.eval c‖ ^ ((2 : ℝ) / (n : ℝ)) * L ^ 2
      ≤ ‖f.eval c‖ ^ ((2 : ℝ) / (n : ℝ)) *
          (2 * discSepCoefficient n S (w₀ * (1 - w₀))) :=
        mul_le_mul_of_nonneg_left hsq (le_of_lt hpos)
    _ = 2 * ‖f.eval c‖ ^ ((2 : ℝ) / (n : ℝ)) *
          discSepCoefficient n S (w₀ * (1 - w₀)) := by ring

/-! ## 8. `res:critical-value-thresholds`: the numerical half -/

private theorem discSep_exp_one_gt : (2.7 : ℝ) < Real.exp 1 := by
  nlinarith [Real.exp_one_gt_d9]

private theorem discSep_log_seven_lt_two : Real.log 7 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hE := discSep_exp_one_gt
  have e2 : Real.exp 1 * Real.exp 1 = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have h : (7.29 : ℝ) < Real.exp 1 * Real.exp 1 := by
    nlinarith [hE, Real.exp_pos 1]
  rw [e2] at h
  linarith

private theorem discSep_log_eleven_lt : Real.log 11 < 5 / 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hE := discSep_exp_one_gt
  have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have e2 : Real.exp (5 / 2) * Real.exp (5 / 2) = Real.exp 5 := by
    rw [← Real.exp_add]; norm_num
  have e5 : Real.exp 5
      = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
  have h2 : (7.29 : ℝ) < Real.exp 1 * Real.exp 1 := by nlinarith
  have h4 : (53.1 : ℝ) < Real.exp 1 * Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
    nlinarith [h2]
  have h5 : (143 : ℝ) < Real.exp 5 := by
    rw [e5]; nlinarith [h4, hE, hEpos]
  have hpos : (0 : ℝ) < Real.exp (5 / 2) := Real.exp_pos _
  nlinarith [e2, h5, hpos]

private theorem discSep_three_fifths_rpow_le : (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) ≤ 18 / 25 := by
  have hy0 : (0 : ℝ) ≤ (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by norm_num) _
  have hy3 : ((3 / 5 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = 9 / 25 := by
    rw [← Real.rpow_natCast ((3 / 5 : ℝ) ^ ((2 : ℝ) / 3)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3 / 5)]
    norm_num
  have hcube : (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) * (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) *
      (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) = 9 / 25 := by
    rw [← hy3]; ring
  by_contra hcon
  push_neg at hcon
  have h1 : (18 / 25 : ℝ) * (18 / 25) <
      (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) * (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) := by nlinarith
  have h2 : (18 / 25 : ℝ) * (18 / 25) * (18 / 25) <
      (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) * (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) *
        (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) := by nlinarith
  rw [hcube] at h2
  norm_num at h2

/-- For `S > 1` and `p ≥ 0`, the centre parameter only lowers the ratio. -/
theorem discSep_ratio_le_branch {S p : ℝ} (hS : 1 < S) (hp : 0 ≤ p) :
    (S ^ 2 + S + p) / (S ^ 2 - S + p) ≤ (S + 1) / (S - 1) := by
  have hden1 : 0 < S ^ 2 - S + p := by nlinarith
  have hden2 : 0 < S - 1 := by linarith
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith

/-- The branch ratio is at most `7` once `S ≥ 4/3`. -/
theorem discSep_branch_le_seven {S : ℝ} (hS : 4 / 3 ≤ S) : (S + 1) / (S - 1) ≤ 7 := by
  have hden : 0 < S - 1 := by linarith
  rw [div_le_iff₀ hden]
  linarith

/-- **First clause of `res:critical-value-thresholds`.**  The paper's display (6)
holds for every degree `n ≥ 3`, every centre parameter `p ≥ 0` (in particular
`p = w₀(1-w₀)` with `w₀ ∈ [0,1]`), and every radius `4/3 ≤ S ≤ 2`. -/
theorem discSepCoefficient_lt_two {n : ℕ} (hn : 3 ≤ n) {S p : ℝ}
    (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2) (hp0 : 0 ≤ p) :
    discSepCoefficient n S p < 2 := by
  have hS1 : 1 < S := by linarith
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hSn : S ≤ (n : ℝ) - 1 := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hbase0 : 0 < S / ((n : ℝ) - 1) := div_pos (by linarith) hn1
  have hbase1 : S / ((n : ℝ) - 1) ≤ 1 := by rw [div_le_one hn1]; exact hSn
  have hexp : (0 : ℝ) ≤ (2 : ℝ) / (n : ℝ) := by positivity
  have hr1 : (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) ≤ 1 :=
    Real.rpow_le_one hbase0.le hbase1 hexp
  have hden : 0 < S ^ 2 - S + p := by nlinarith
  have hlog0 : 0 ≤ Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) :=
    discSep_log_nonneg (by linarith) hden
  have hratio_pos : 0 < (S ^ 2 + S + p) / (S ^ 2 - S + p) :=
    div_pos (by nlinarith) hden
  have hlog7 : Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) ≤ Real.log 7 :=
    Real.log_le_log hratio_pos
      (le_trans (discSep_ratio_le_branch hS1 hp0) (discSep_branch_le_seven hS))
  unfold discSepCoefficient
  calc (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
        Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))
      ≤ 1 * Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) :=
        mul_le_mul_of_nonneg_right hr1 hlog0
    _ = Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p)) := one_mul _
    _ ≤ Real.log 7 := hlog7
    _ < 2 := discSep_log_seven_lt_two

/-- **The degree-three branch-centred constant** of the short note's corollary:
at `w₀ = 1` (so `p = 0`) the radius `6/5` already works, because
`(3/5)^{2/3} log 11 < 2`. -/
theorem discSepCoefficient_three_six_fifths : discSepCoefficient 3 (6 / 5) 0 < 2 := by
  unfold discSepCoefficient
  have hval : ((6 / 5 : ℝ) ^ 2 + 6 / 5 + 0) / ((6 / 5 : ℝ) ^ 2 - 6 / 5 + 0) = 11 := by
    norm_num
  have hbase : (6 / 5 : ℝ) / (((3 : ℕ) : ℝ) - 1) = 3 / 5 := by norm_num
  have hexp : ((2 : ℝ) / (((3 : ℕ) : ℝ))) = (2 : ℝ) / 3 := by norm_num
  rw [hval, hbase, hexp]
  have hlogpos : 0 ≤ Real.log (11 : ℝ) := Real.log_nonneg (by norm_num)
  calc (3 / 5 : ℝ) ^ ((2 : ℝ) / 3) * Real.log 11
      ≤ (18 / 25 : ℝ) * Real.log 11 :=
        mul_le_mul_of_nonneg_right discSep_three_fifths_rpow_le hlogpos
    _ < (18 / 25 : ℝ) * (5 / 2) :=
        mul_lt_mul_of_pos_left discSep_log_eleven_lt (by norm_num)
    _ < 2 := by norm_num

/-! ## 9. `res:critical-value-thresholds`: the geometric half -/

/-- **Second clause of `res:critical-value-thresholds`, both records.**

Conditional on `DiscSepBergmanArea`: if `f` is monic of degree `n ≥ 3` with all
roots in the open unit disc, `c` is a simple critical point with `v = f(c)`,
`0 < |v| < 1`, and some centre `w₀ ∈ [0,1]` has `|f(d)/v - w₀| ≥ S` at every
other critical point for a radius `4/3 ≤ S ≤ 2`, then two distinct roots of `f`
are joined inside `{|f| < 1}` by a rectifiable curve of length strictly below
`2`. -/
theorem discSep_uniform_radius (hext : DiscSepBergmanArea)
    {f : ℂ[X]} {n : ℕ} {c : ℂ} {w₀ S : ℝ}
    (hn : 3 ≤ n) (hdeg : f.natDegree = n) (hmonic : f.Monic)
    (hroots : ∀ z : ℂ, f.eval z = 0 → ‖z‖ < 1)
    (hcrit : f.derivative.eval c = 0)
    (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hv : f.eval c ≠ 0) (hv1 : ‖f.eval c‖ < 1)
    (hw₀ : 0 ≤ w₀) (hw₁ : w₀ ≤ 1) (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2)
    (hsep : ∀ d : ℂ, d ≠ c → f.derivative.eval d = 0 →
      S ≤ ‖f.eval d / f.eval c - (w₀ : ℂ)‖) :
    ∃ (a b : ℂ) (γ : ℝ → ℂ), a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      ContinuousOn γ (Set.Icc (-1 : ℝ) 1) ∧ γ (-1) = a ∧ γ 1 = b ∧
      (∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖f.eval (γ ξ)‖ < 1) ∧
      BoundedVariationOn γ (Set.Icc (-1 : ℝ) 1) ∧
      eVariationOn γ (Set.Icc (-1 : ℝ) 1) < ENNReal.ofReal 2 := by
  have hmaxle : max w₀ (1 - w₀) ≤ 1 := max_le hw₁ (by linarith)
  have hSmax : max w₀ (1 - w₀) < S := by linarith
  obtain ⟨a, b, γ, Lf, hab, hfa, hfb, hcont, hγl, hγr, hlvl, hbv, hLf0, hvar, hsq⟩ :=
    discSep_separation_short hext hn hdeg hmonic hcrit hsimple hv hw₀ hw₁ hSmax hsep
  have hvpos : 0 < ‖f.eval c‖ := norm_pos_iff.mpr hv
  have hcoef : discSepCoefficient n S (w₀ * (1 - w₀)) < 2 :=
    discSepCoefficient_lt_two hn hS hS2 (mul_nonneg hw₀ (by linarith))
  have hA0 : 0 < ‖f.eval c‖ ^ ((2 : ℝ) / (n : ℝ)) := Real.rpow_pos_of_pos hvpos _
  have hA1 : ‖f.eval c‖ ^ ((2 : ℝ) / (n : ℝ)) ≤ 1 :=
    Real.rpow_le_one hvpos.le hv1.le (by positivity)
  have hkey : 0 < ‖f.eval c‖ ^ ((2 : ℝ) / (n : ℝ)) *
      (2 - discSepCoefficient n S (w₀ * (1 - w₀))) := mul_pos hA0 (by linarith)
  have hlt4 : Lf ^ 2 < 4 := by nlinarith [hsq, hA1, hkey]
  have hLlt : Lf < 2 := by nlinarith [hLf0, hlt4]
  refine ⟨a, b, γ, hab, hfa, hfb, hcont, hγl, hγr, ?_, hbv, ?_⟩
  · intro ξ hξ
    exact lt_of_le_of_lt (hlvl ξ hξ) hv1
  · exact lt_of_le_of_lt hvar ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hLlt)

/-- **The degree-three branch-centred case** of the short note's corollary: in
degree three the choice `w₀ = 1` works with `4/3` replaced by `6/5`. -/
theorem discSep_cubic_six_fifths (hext : DiscSepBergmanArea)
    {f : ℂ[X]} {c : ℂ}
    (hdeg : f.natDegree = 3) (hmonic : f.Monic)
    (hroots : ∀ z : ℂ, f.eval z = 0 → ‖z‖ < 1)
    (hcrit : f.derivative.eval c = 0)
    (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hv : f.eval c ≠ 0) (hv1 : ‖f.eval c‖ < 1)
    (hsep : ∀ d : ℂ, d ≠ c → f.derivative.eval d = 0 →
      6 / 5 ≤ ‖f.eval d / f.eval c - (1 : ℂ)‖) :
    ∃ (a b : ℂ) (γ : ℝ → ℂ), a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      ContinuousOn γ (Set.Icc (-1 : ℝ) 1) ∧ γ (-1) = a ∧ γ 1 = b ∧
      (∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖f.eval (γ ξ)‖ < 1) ∧
      BoundedVariationOn γ (Set.Icc (-1 : ℝ) 1) ∧
      eVariationOn γ (Set.Icc (-1 : ℝ) 1) < ENNReal.ofReal 2 := by
  have hsep' : ∀ d : ℂ, d ≠ c → f.derivative.eval d = 0 →
      (6 / 5 : ℝ) ≤ ‖f.eval d / f.eval c - (((1 : ℝ)) : ℂ)‖ := by
    intro d hd hcd
    simpa using hsep d hd hcd
  obtain ⟨a, b, γ, Lf, hab, hfa, hfb, hcont, hγl, hγr, hlvl, hbv, hLf0, hvar, hsq⟩ :=
    discSep_separation_short hext (le_refl 3) hdeg hmonic hcrit hsimple hv
      (by norm_num : (0 : ℝ) ≤ 1) (le_refl (1 : ℝ)) (by norm_num) hsep'
  have hvpos : 0 < ‖f.eval c‖ := norm_pos_iff.mpr hv
  have hp0 : (1 : ℝ) * (1 - 1) = 0 := by norm_num
  rw [hp0] at hsq
  have hcoef : discSepCoefficient 3 (6 / 5) 0 < 2 := discSepCoefficient_three_six_fifths
  have hA0 : 0 < ‖f.eval c‖ ^ ((2 : ℝ) / ((3 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hvpos _
  have hA1 : ‖f.eval c‖ ^ ((2 : ℝ) / ((3 : ℕ) : ℝ)) ≤ 1 :=
    Real.rpow_le_one hvpos.le hv1.le (by positivity)
  have hkey : 0 < ‖f.eval c‖ ^ ((2 : ℝ) / ((3 : ℕ) : ℝ)) *
      (2 - discSepCoefficient 3 (6 / 5) 0) := mul_pos hA0 (by linarith)
  have hlt4 : Lf ^ 2 < 4 := by nlinarith [hsq, hA1, hkey]
  have hLlt : Lf < 2 := by nlinarith [hLf0, hlt4]
  refine ⟨a, b, γ, hab, hfa, hfb, hcont, hγl, hγr, ?_, hbv, ?_⟩
  · intro ξ hξ
    exact lt_of_le_of_lt (hlvl ξ hξ) hv1
  · exact lt_of_le_of_lt hvar ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hLlt)

#print axioms discSep_denominator_factor
#print axioms discSep_denominator_pos
#print axioms discSep_qsq_mem
#print axioms discSep_bergman_factor
#print axioms discSep_log_nonneg
#print axioms discSep_target_starShaped
#print axioms discSep_mobius_norm_lt
#print axioms discSep_mobius_at_one
#print axioms discSep_squared_length_le
#print axioms discSep_length_lt_two
#print axioms discSep_separation_long
#print axioms discSepNormalise_spec
#print axioms discSep_transport
#print axioms discSep_separation_short
#print axioms discSep_ratio_le_branch
#print axioms discSep_branch_le_seven
#print axioms discSepCoefficient_lt_two
#print axioms discSepCoefficient_three_six_fifths
#print axioms discSep_uniform_radius
#print axioms discSep_cubic_six_fifths

end ErdosProblems.Erdos1041.PaperCompleteR21
