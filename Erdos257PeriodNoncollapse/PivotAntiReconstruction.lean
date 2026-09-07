import Erdos257PeriodNoncollapse.AdjacentPhaseSeparation
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Anchored first-harmonic defect and pivot anti-reconstruction

This module gives the exact affine certificate consumed by the established
first-harmonic backplane.  For a finite set `T`, the anchor defect is

`sum N in T, (2 - 2 * windowFirstCos h N L)`.

Because every `windowFirstExp` has norm one, this is the squared distance of
the phase vector from the distinguished constant phase `1`.  The threshold
`T.card / 5` is exactly the `9/10` real-part saving, not a heuristic
decorrelation condition.

The canonical natural-prime predicates at the end are intentionally unproved.
The weakest is a singleton first-harmonic escape; the fibre-average window gap
is a convenient stronger target, while centred variance and residual-weighted
cancellation remain optional spectral routes rather than proof prerequisites.

The fibre-free window-pair predicate is characterized exactly: it is
equivalent to irrationality of the #249 totient series.  The converse uses
only expansivity of the doubling orbit and an explicit two-point sample, so
this endpoint is a geometric reformulation rather than a weaker open producer.
-/

namespace Erdos257PeriodNoncollapse
namespace TotientTailPeriodKiller

open Finset

noncomputable section

/-! ## Exact tail-orbit phase normal form -/

/-- First additive character of the infinite tail difference. -/
noncomputable def tailOrbitFirstExp (h N : ℕ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (totientTail (N + h) - totientTail N) : ℝ) : ℂ) *
      Complex.I)

/-- First additive character of the scaled #249 series orbit. -/
noncomputable def scaledTotientSeriesFirstExp (h N : ℕ) : ℂ :=
  Complex.exp
    (((2 * Real.pi *
      ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) : ℝ) : ℂ) *
      Complex.I)

/-- Exact real normal form behind the period-lock orbit: the tail difference
is the scaled #249 series minus an explicit integer prefix difference. -/
theorem tail_diff_eq_scaled_totient_series_sub_prefix (h N : ℕ) :
    totientTail (N + h) - totientTail N =
      (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) -
        ((totientPrefix (N + h) : ℝ) - (totientPrefix N : ℝ)) := by
  have hNh := two_pow_mul_totient_series_eq (N + h)
  have hN := two_pow_mul_totient_series_eq N
  rw [pow_add] at hNh
  nlinarith

/-- Exact tail-orbit conjugacy.  Integer prefixes disappear under the first
additive character, so rationality locks precisely the scaled `W₀` orbit. -/
theorem tailOrbitFirstExp_eq_scaledTotientSeriesFirstExp (h N : ℕ) :
    tailOrbitFirstExp h N = scaledTotientSeriesFirstExp h N := by
  rw [tailOrbitFirstExp, scaledTotientSeriesFirstExp,
    tail_diff_eq_scaled_totient_series_sub_prefix]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-((totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ)), ?_⟩
  push_cast
  ring

/-- The reduced finite-window character equals the character of the
unreduced integer discrepancy. -/
theorem windowFirstExp_eq_unreduced (h N L : ℕ) :
    windowFirstExp h N L =
      Complex.exp
        ((((2 * Real.pi *
          (((windowDiscrepancy h N L : ℤ) : ℝ) / 2 ^ L)) : ℝ) : ℂ) *
          Complex.I) := by
  rw [windowFirstExp, windowFirstAngle]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  let q : ℤ := windowDiscrepancy h N L / (2 ^ L : ℤ)
  refine ⟨-q, ?_⟩
  have hP : ((2 : ℝ) ^ L) ≠ 0 := by positivity
  have hdiv := Int.ediv_mul_add_emod
    (windowDiscrepancy h N L) (2 ^ L : ℤ)
  change windowDiscrepancy h N L / (2 ^ L : ℤ) * (2 ^ L : ℤ) +
      windowDiscrepancy h N L % (2 ^ L : ℤ) =
        windowDiscrepancy h N L at hdiv
  have hdivR :
      ((windowDiscrepancy h N L / (2 ^ L : ℤ) : ℤ) : ℝ) * 2 ^ L +
        ((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) =
          (windowDiscrepancy h N L : ℝ) := by
    exact_mod_cast hdiv
  have hscalar :
      2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
            ((2 ^ L : ℤ) : ℝ)) =
        2 * Real.pi *
            ((windowDiscrepancy h N L : ℝ) / (2 : ℝ) ^ L) +
          ((-(windowDiscrepancy h N L / (2 ^ L : ℤ)) : ℤ) : ℝ) *
            (2 * Real.pi) := by
    norm_num
    have hr :
        ((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) =
          (windowDiscrepancy h N L : ℝ) -
            ((windowDiscrepancy h N L / (2 ^ L : ℤ) : ℤ) : ℝ) *
              (2 : ℝ) ^ L := by
      linarith
    rw [hr]
    field_simp [hP]
    ring
  dsimp [q]
  calc
    _ = ((2 * Real.pi *
          ((windowDiscrepancy h N L : ℝ) / (2 : ℝ) ^ L) +
        ((-(windowDiscrepancy h N L / (2 ^ L : ℤ)) : ℤ) : ℝ) *
          (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      exact congrArg (fun x : ℝ => (x : ℂ) * Complex.I) hscalar
    _ = _ := by push_cast; ring

/-- Equal dyadic discrepancy residues give exactly equal first-harmonic
phases.  This is the finite lattice interface for an arithmetic collision
argument: no choice of integer representatives or analytic approximation is
left at the call site. -/
theorem windowFirstExp_eq_of_discrepancy_emod_eq
    {h N N' L : ℕ}
    (hres :
      windowDiscrepancy h N L % (2 ^ L : ℤ) =
        windowDiscrepancy h N' L % (2 ^ L : ℤ)) :
    windowFirstExp h N L = windowFirstExp h N' L := by
  simp [windowFirstExp, windowFirstAngle, hres]

/-- Real-part version of the exact dyadic residue collision interface. -/
theorem windowFirstCos_eq_of_discrepancy_emod_eq
    {h N N' L : ℕ}
    (hres :
      windowDiscrepancy h N L % (2 ^ L : ℤ) =
        windowDiscrepancy h N' L % (2 ^ L : ℤ)) :
    windowFirstCos h N L = windowFirstCos h N' L := by
  rw [← windowFirstExp_re, ← windowFirstExp_re,
    windowFirstExp_eq_of_discrepancy_emod_eq hres]

/-- Exact finite-window/infinite-orbit phase factorisation.  The second
factor is the translated tail omitted at depth `L`. -/
theorem tailOrbitFirstExp_eq_window_mul_remainder (h N L : ℕ) :
    tailOrbitFirstExp h N =
      windowFirstExp h N L *
        Complex.exp
          (Complex.I *
            (((2 * Real.pi *
              ((totientTail (N + L + h) - totientTail (N + L)) /
                2 ^ L)) : ℝ) : ℂ)) := by
  rw [tailOrbitFirstExp, tail_diff_eq_windowDiscrepancy_div_add_shifted,
    windowFirstExp_eq_unreduced]
  rw [show
      (((2 * Real.pi *
        (((windowDiscrepancy h N L : ℤ) : ℝ) / 2 ^ L +
          (totientTail (N + L + h) - totientTail (N + L)) / 2 ^ L)) : ℝ) : ℂ) *
          Complex.I =
        (((2 * Real.pi *
          (((windowDiscrepancy h N L : ℤ) : ℝ) / 2 ^ L)) : ℝ) : ℂ) *
            Complex.I +
          Complex.I *
            (((2 * Real.pi *
              ((totientTail (N + L + h) - totientTail (N + L)) /
                2 ^ L)) : ℝ) : ℂ) by push_cast; ring]
  exact Complex.exp_add _ _

/-- The phase error is bounded by the exact omitted tail difference. -/
theorem norm_windowFirstExp_sub_tailOrbitFirstExp_le (h N L : ℕ) :
    ‖windowFirstExp h N L - tailOrbitFirstExp h N‖ ≤
      2 * Real.pi *
        |totientTail (N + L + h) - totientTail (N + L)| / 2 ^ L := by
  rw [tailOrbitFirstExp_eq_window_mul_remainder]
  let x : ℝ := 2 * Real.pi *
    ((totientTail (N + L + h) - totientTail (N + L)) / 2 ^ L)
  calc
    ‖windowFirstExp h N L -
        windowFirstExp h N L * Complex.exp (Complex.I * (x : ℂ))‖ =
        ‖windowFirstExp h N L *
          (1 - Complex.exp (Complex.I * (x : ℂ)))‖ := by congr 1; ring
    _ = ‖1 - Complex.exp (Complex.I * (x : ℂ))‖ := by
      rw [norm_mul, norm_windowFirstExp, one_mul]
    _ = ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ := by
      rw [← norm_neg]
      congr 1
      ring
    _ ≤ ‖x‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi *
        |totientTail (N + L + h) - totientTail (N + L)| / 2 ^ L := by
      rw [Real.norm_eq_abs]
      dsimp [x]
      simp only [abs_mul, abs_div, abs_of_nonneg Real.pi_pos.le,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ L)]
      ring

/-- Closed phase-error bound obtained from the universal totient-tail strip. -/
theorem norm_windowFirstExp_sub_tailOrbitFirstExp_lt (h N L : ℕ) :
    ‖windowFirstExp h N L - tailOrbitFirstExp h N‖ <
      2 * Real.pi * ((N : ℝ) + L + h + 2) / 2 ^ L := by
  refine lt_of_le_of_lt (norm_windowFirstExp_sub_tailOrbitFirstExp_le h N L) ?_
  have htail := abs_tail_diff_lt h (N + L)
  push_cast at htail
  have hfac : 0 < 2 * Real.pi / (2 : ℝ) ^ L := by positivity
  calc
    2 * Real.pi * |totientTail (N + L + h) - totientTail (N + L)| / 2 ^ L =
        (2 * Real.pi / (2 : ℝ) ^ L) *
          |totientTail (N + L + h) - totientTail (N + L)| := by ring
    _ < (2 * Real.pi / (2 : ℝ) ^ L) * ((N : ℝ) + L + h + 2) :=
      mul_lt_mul_of_pos_left htail hfac
    _ = 2 * Real.pi * ((N : ℝ) + L + h + 2) / 2 ^ L := by ring

/-- Any real-part gap in the infinite orbit survives finite truncation with
exactly the supplied additive error budget.  This is the packet-facing seam:
arithmetic input may come from a lattice, variance, or anti-concentration
argument without being normalized in advance to `4/5`. -/
theorem windowFirstCos_le_add_of_tailOrbitGap
    {h N L : ℕ} {a ε : ℝ}
    (htail : (tailOrbitFirstExp h N).re ≤ a)
    (herror :
      2 * Real.pi * ((N : ℝ) + L + h + 2) / 2 ^ L ≤ ε) :
    windowFirstCos h N L ≤ a + ε := by
  have hnorm := norm_windowFirstExp_sub_tailOrbitFirstExp_lt h N L
  have hre := Complex.re_le_norm (windowFirstExp h N L - tailOrbitFirstExp h N)
  rw [Complex.sub_re, windowFirstExp_re] at hre
  nlinarith

/-- A `4/5` real-part gap in the infinite orbit survives as the `9/10`
finite-window gap once the explicit truncation budget is at most `1/10`. -/
theorem windowFirstCos_le_nine_tenths_of_tailOrbitGap
    {h N L : ℕ}
    (htail : (tailOrbitFirstExp h N).re ≤ (4 / 5 : ℝ))
    (herror :
      2 * Real.pi * ((N : ℝ) + L + h + 2) / 2 ^ L ≤ (1 / 10 : ℝ)) :
    windowFirstCos h N L ≤ (9 / 10 : ℝ) := by
  have h := windowFirstCos_le_add_of_tailOrbitGap htail herror
  norm_num at h ⊢
  exact h

private theorem tendsto_linear_mul_half_pow (c : ℕ) :
    Filter.Tendsto
      (fun L : ℕ => ((c : ℝ) + L) * (1 / 2 : ℝ) ^ L)
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun L : ℕ => (1 / 2 : ℝ) ^ L)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hself : Filter.Tendsto (fun L : ℕ => (L : ℝ) * (1 / 2 : ℝ) ^ L)
      Filter.atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  simpa [add_mul] using (tendsto_const_nhds.mul hpow).add hself

/-- Exponential depth simultaneously pays the certificate room inequality
and any positive phase-error budget past any prescribed depth. -/
theorem exists_natural_window_depth_with_error
    (h N L₀ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, L₀ ≤ L ∧
      16 * (2 * N + h + L + 2) ≤ 2 ^ L ∧
      2 * Real.pi * ((N : ℝ) + L + h + 2) / 2 ^ L ≤ ε := by
  obtain ⟨L₁, hL₁⟩ := Metric.tendsto_atTop.1
    (tendsto_linear_mul_half_pow (2 * N + h + 2))
    (1 / 16 : ℝ) (by norm_num)
  obtain ⟨L₂, hL₂⟩ := Metric.tendsto_atTop.1
    (tendsto_linear_mul_half_pow (N + h + 2))
    (ε / (2 * Real.pi)) (by positivity)
  let L := max L₀ (max L₁ L₂)
  have hL₀ : L₀ ≤ L := Nat.le_max_left _ _
  have hL₁' : L₁ ≤ L := le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hL₂' : L₂ ≤ L := le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hs₁ := hL₁ L hL₁'
  have hs₂ := hL₂ L hL₂'
  have hnonneg₁ :
      0 ≤ (((2 * N + h + 2 : ℕ) : ℝ) + L) * (1 / 2 : ℝ) ^ L := by
    positivity
  have hnonneg₂ :
      0 ≤ (((N + h + 2 : ℕ) : ℝ) + L) * (1 / 2 : ℝ) ^ L := by
    positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg₁] at hs₁
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg₂] at hs₂
  have hhalf : (1 / 2 : ℝ) ^ L = 1 / (2 : ℝ) ^ L := by
    rw [div_pow, one_pow]
  rw [hhalf] at hs₁ hs₂
  have hs₁div :
      ((((2 * N + h + 2 : ℕ) : ℝ) + L) / 2 ^ L) < (1 / 16 : ℝ) := by
    simpa [div_eq_mul_inv] using hs₁
  have hs₂div :
      ((((N + h + 2 : ℕ) : ℝ) + L) / 2 ^ L) <
        ε / (2 * Real.pi) := by
    simpa [div_eq_mul_inv] using hs₂
  have hpowpos : (0 : ℝ) < 2 ^ L := by positivity
  have hroomR :
      (16 : ℝ) * ((2 * N + h + L + 2 : ℕ) : ℝ) < 2 ^ L := by
    have hdivroom :
        (16 : ℝ) * ((2 * N + h + L + 2 : ℕ) : ℝ) / 2 ^ L < 1 := by
      calc
        (16 : ℝ) * ((2 * N + h + L + 2 : ℕ) : ℝ) / 2 ^ L =
            16 * ((((2 * N + h + 2 : ℕ) : ℝ) + L) / 2 ^ L) := by
          push_cast
          ring
        _ < 16 * (1 / 16 : ℝ) :=
          mul_lt_mul_of_pos_left hs₁div (by norm_num)
        _ = 1 := by norm_num
    simpa using (div_lt_iff₀ hpowpos).mp hdivroom
  have hroom : 16 * (2 * N + h + L + 2) ≤ 2 ^ L := by
    have hroomNat : 16 * (2 * N + h + L + 2) < 2 ^ L := by
      exact_mod_cast hroomR
    omega
  have herror :
      2 * Real.pi * ((N : ℝ) + L + h + 2) / 2 ^ L ≤ ε := by
    apply le_of_lt
    calc
      2 * Real.pi * ((N : ℝ) + L + h + 2) / 2 ^ L =
          (2 * Real.pi) * ((((N + h + 2 : ℕ) : ℝ) + L) / 2 ^ L) := by
        push_cast
        ring
      _ < (2 * Real.pi) * (ε / (2 * Real.pi)) :=
        mul_lt_mul_of_pos_left hs₂div (by positivity)
      _ = ε := by
        field_simp [Real.pi_ne_zero]
  exact ⟨L, hL₀, hroom, herror⟩

/-! ## Expansivity of the doubling orbit -/

/-- A real number is dyadic when some power-of-two multiple is an integer.
This multiplicative form avoids quotient normalization in orbit arguments. -/
def IsDyadicReal (x : ℝ) : Prop :=
  ∃ k : ℕ, ∃ z : ℤ, (2 : ℝ) ^ k * x = z

/-- A unit-modulus squaring orbit which never reaches `1` has cofinally many
adjacent chords of length at least `1`.  This is the elementary expansivity
input behind the two-point characterization below; no equidistribution is
used. -/
theorem cofinally_adjacent_chord_ge_one_of_unit_squaring
    (z : ℕ → ℂ)
    (hnorm : ∀ N, ‖z N‖ = 1)
    (hsq : ∀ N, z (N + 1) = (z N) ^ 2)
    (hne : ∀ N, z N ≠ 1) :
    ∀ N₀, ∃ N ≥ N₀, 1 ≤ ‖z (N + 1) - z N‖ := by
  intro N₀
  by_contra hcontra
  push Not at hcontra
  let y : ℕ → ℝ := fun N => 1 - (z N).re
  have hchord (N : ℕ) :
      ‖z (N + 1) - z N‖ = ‖z N - 1‖ := by
    rw [hsq]
    calc
      ‖z N ^ 2 - z N‖ = ‖z N * (z N - 1)‖ := by congr 1; ring
      _ = ‖z N - 1‖ := by rw [norm_mul, hnorm, one_mul]
  have hy_bounds (N : ℕ) (hN : N₀ ≤ N) :
      0 < y N ∧ y N < (1 / 2 : ℝ) := by
    have hsmall : ‖z N - 1‖ < 1 := by
      rw [← hchord]
      exact hcontra N hN
    have hnormSq : Complex.normSq (z N) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have hdistSq : ‖z N - 1‖ ^ 2 = 2 - 2 * (z N).re := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, hnormSq]
      norm_num
    have hrelt : (1 / 2 : ℝ) < (z N).re := by
      have hsquare : ‖z N - 1‖ ^ 2 < 1 := by
        nlinarith [norm_nonneg (z N - 1)]
      nlinarith
    have hrele : (z N).re ≤ 1 := by
      simpa [hnorm] using Complex.re_le_norm (z N)
    have hy_nonneg : 0 ≤ y N := by
      dsimp [y]
      linarith
    have hy_ne : y N ≠ 0 := by
      intro hy0
      have hre : (z N).re = 1 := by
        dsimp [y] at hy0
        linarith
      have himsq : (z N).im * (z N).im = 0 := by
        rw [Complex.normSq_apply] at hnormSq
        nlinarith
      have him : (z N).im = 0 := mul_self_eq_zero.mp himsq
      apply hne N
      apply Complex.ext
      · simp [hre]
      · simp [him]
    exact ⟨lt_of_le_of_ne hy_nonneg (Ne.symm hy_ne), by
      dsimp [y]
      linarith⟩
  have hy_grows (N : ℕ) (hN : N₀ ≤ N) : 3 * y N < y (N + 1) := by
    have hnormSq : Complex.normSq (z N) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have hyrec :
        y (N + 1) = 2 * (1 + (z N).re) * y N := by
      dsimp [y]
      rw [hsq]
      rw [Complex.normSq_apply] at hnormSq
      simp only [pow_two, Complex.mul_re]
      nlinarith
    rw [hyrec]
    have hypos := (hy_bounds N hN).1
    have hre := (hy_bounds N hN).2
    dsimp [y] at hre
    nlinarith
  have hy0 : 0 < y N₀ := (hy_bounds N₀ le_rfl).1
  have hlower (k : ℕ) :
      (((k : ℝ) + 1) * y N₀) ≤ y (N₀ + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hgrow := hy_grows (N₀ + k) (by omega)
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hfactor :
            (((k : ℝ) + 2) * y N₀) ≤
              3 * (((k : ℝ) + 1) * y N₀) := by
          nlinarith [mul_nonneg (by nlinarith : 0 ≤ 2 * (k : ℝ) + 1) hy0.le]
        calc
          (((k + 1 : ℕ) : ℝ) + 1) * y N₀ =
              ((k : ℝ) + 2) * y N₀ := by push_cast; ring
          _ ≤ 3 * (((k : ℝ) + 1) * y N₀) := hfactor
          _ ≤ 3 * y (N₀ + k) := mul_le_mul_of_nonneg_left ih (by norm_num)
          _ ≤ y ((N₀ + k) + 1) := hgrow.le
          _ = y (N₀ + (k + 1)) := by congr 1
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (2 * y N₀))
  have hlarge : (1 / 2 : ℝ) < (k : ℝ) * y N₀ := by
    have hmul := mul_lt_mul_of_pos_right hk hy0
    field_simp [ne_of_gt hy0] at hmul
    nlinarith
  have hupper := (hy_bounds (N₀ + k) (by omega)).2
  have hlower' := hlower k
  nlinarith

/-- The exact #249 scaled phase orbit is a squaring orbit. -/
theorem scaledTotientSeriesFirstExp_succ (h N : ℕ) :
    scaledTotientSeriesFirstExp h (N + 1) =
      (scaledTotientSeriesFirstExp h N) ^ 2 := by
  rw [scaledTotientSeriesFirstExp, scaledTotientSeriesFirstExp]
  let θ : ℝ :=
    2 * Real.pi *
      ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
  let θ' : ℝ :=
    2 * Real.pi *
      ((2 : ℝ) ^ (N + 1) * ((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
  let x : ℂ := (θ : ℂ) * Complex.I
  change Complex.exp ((θ' : ℂ) * Complex.I) = Complex.exp x ^ 2
  have hθ : θ' = 2 * θ := by
    dsimp [θ', θ]
    rw [pow_succ]
    ring
  have hexponent : (θ' : ℂ) * Complex.I = (2 : ℕ) * x := by
    rw [hθ]
    dsimp [x]
    norm_num
    ring
  rw [hexponent]
  exact Complex.exp_nat_mul x 2

/-- Every point of the exact #249 scaled phase orbit has unit norm. -/
theorem norm_scaledTotientSeriesFirstExp (h N : ℕ) :
    ‖scaledTotientSeriesFirstExp h N‖ = 1 := by
  let θ : ℝ :=
    2 * Real.pi *
      ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
  change ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1
  rw [Complex.norm_exp]
  simp

/-- Non-dyadicity of the fixed scaled series is exactly the hypothesis needed
to prevent the corresponding doubling orbit from landing at `1`. -/
theorem cofinally_scaledTotientSeriesFirstExp_adjacent_chord_ge_one_of_not_dyadic
    (h : ℕ)
    (hnd : ¬ IsDyadicReal
      (((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))) :
    ∀ N₀, ∃ N ≥ N₀,
      1 ≤ ‖scaledTotientSeriesFirstExp h (N + 1) -
        scaledTotientSeriesFirstExp h N‖ := by
  apply cofinally_adjacent_chord_ge_one_of_unit_squaring
    (scaledTotientSeriesFirstExp h)
    (norm_scaledTotientSeriesFirstExp h)
    (scaledTotientSeriesFirstExp_succ h)
  intro N hphase
  let β : ℝ :=
    (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
  have hphase' :
      Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) = 1 := by
    simpa [scaledTotientSeriesFirstExp, β] using hphase
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hphase'
  have him := congrArg Complex.im hm
  have hscalar : 2 * Real.pi * β = (m : ℝ) * (2 * Real.pi) := by
    simpa using him
  have hβm : β = (m : ℝ) := by
    have hpi : 0 < 2 * Real.pi := by positivity
    nlinarith
  apply hnd
  refine ⟨N, m, ?_⟩
  simpa [β, mul_assoc] using hβm

/-- Irrationality of the #249 series prevents the scaled phase orbit from
ever landing at `1`; doubling expansivity then gives cofinally many adjacent
chords of length at least `1`. -/
theorem cofinally_scaledTotientSeriesFirstExp_adjacent_chord_ge_one
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
    (h : ℕ) (hh : 0 < h) :
    ∀ N₀, ∃ N ≥ N₀,
      1 ≤ ‖scaledTotientSeriesFirstExp h (N + 1) -
        scaledTotientSeriesFirstExp h N‖ := by
  apply cofinally_adjacent_chord_ge_one_of_unit_squaring
    (scaledTotientSeriesFirstExp h)
    (norm_scaledTotientSeriesFirstExp h)
    (scaledTotientSeriesFirstExp_succ h)
  intro N hphase
  let scale : ℕ := 2 ^ N * (2 ^ h - 1)
  let α : ℝ :=
    (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
  have hpow : 1 < 2 ^ h :=
    one_lt_pow' (by norm_num : 1 < (2 : ℕ)) (Nat.ne_of_gt hh)
  have hscale : scale ≠ 0 := by
    dsimp [scale]
    exact Nat.ne_of_gt (Nat.mul_pos (pow_pos (by norm_num) N)
      (Nat.sub_pos_of_lt hpow))
  have hα : Irrational α := by
    have hirr :
        Irrational ((scale : ℝ) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :=
      irrational_natCast_mul_iff.mpr ⟨hscale, hS⟩
    simpa [α, scale, Nat.cast_sub hpow.le] using hirr
  have hphase' :
      Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) = 1 := by
    simpa [scaledTotientSeriesFirstExp, α] using hphase
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hphase'
  have him := congrArg Complex.im hm
  have hscalar : 2 * Real.pi * α = (m : ℝ) * (2 * Real.pi) := by
    simpa using him
  have hαm : α = (m : ℝ) := by
    have hpi : 0 < 2 * Real.pi := by positivity
    nlinarith
  exact hα.ne_int m hαm

/-- Squared affine distance from the distinguished first-harmonic phase `1`,
written in real coordinates so the certificate kernel needs no complex API. -/
noncomputable def firstHarmonicAnchorDefect
    (h L : ℕ) (T : Finset ℕ) : ℝ :=
  ∑ N ∈ T, (2 - 2 * windowFirstCos h N L)

/-- The anchor defect is exactly the cardinality-minus-real-part expression. -/
theorem firstHarmonicAnchorDefect_eq
    (h L : ℕ) (T : Finset ℕ) :
    firstHarmonicAnchorDefect h L T =
      2 * (T.card : ℝ) - 2 * ∑ N ∈ T, windowFirstCos h N L := by
  classical
  rw [firstHarmonicAnchorDefect, Finset.sum_sub_distrib,
    Finset.sum_const, ← Finset.mul_sum]
  simp only [nsmul_eq_mul]
  ring

/-- The real-coordinate defect is the squared complex distance from the
distinguished phase `1`. -/
theorem firstHarmonicAnchorDefect_eq_sum_norm_sq
    (h L : ℕ) (T : Finset ℕ) :
    firstHarmonicAnchorDefect h L T =
      ∑ N ∈ T, ‖windowFirstExp h N L - 1‖ ^ 2 := by
  rw [firstHarmonicAnchorDefect]
  apply Finset.sum_congr rfl
  intro N hN
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp [Complex.normSq_eq_norm_sq, norm_windowFirstExp, windowFirstExp_re]
  norm_num

/-- The one-fifth anchor-defect threshold is exactly, in both directions,
the nine-tenths real first-harmonic threshold on the same finite set. -/
theorem firstHarmonicAnchorDefect_ge_iff_first_harmonic_gap
    (h L : ℕ) (T : Finset ℕ) :
    (T.card : ℝ) / 5 ≤ firstHarmonicAnchorDefect h L T ↔
      (∑ N ∈ T, windowFirstCos h N L) ≤
        (9 / 10 : ℝ) * T.card := by
  rw [firstHarmonicAnchorDefect_eq]
  constructor <;> intro hbound <;> nlinarith

/-! ## Finite-fibre variance intake -/

/-- Additive real pairwise energy does not by itself force first-harmonic
phase separation.  At every prescribed scale there is a two-point sample
whose squared real gap is at least that scale while its exponential chord is
exactly zero: integer-period aliasing erases the entire gap.  Consequently a
variance input for real lifts must be supplemented by residue small-ball or
phase anti-concentration information before it can feed
`DTWWindowSeparatedPairs`. -/
theorem exists_large_real_pair_energy_with_zero_first_harmonic_chord
    (B : ℕ) :
    ∃ x y : ℝ,
      (B : ℝ) ≤ (x - y) ^ 2 ∧
      ‖Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)‖ ^ 2 = 0 := by
  refine ⟨0, ((B + 1 : ℕ) : ℝ), ?_, ?_⟩
  · push_cast
    have hB : (0 : ℝ) ≤ (B : ℝ) := by positivity
    nlinarith [sq_nonneg (B : ℝ)]
  · have hexponent :
        (((2 * Real.pi * (((B + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) =
          ((B + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    have hperiod :
        Complex.exp
            (((2 * Real.pi * (((B + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
              Complex.I) = 1 := by
      rw [hexponent]
      exact Complex.exp_nat_mul_two_pi_mul_I (B + 1)
    rw [hperiod]
    norm_num

/-- Exact finite complex bias--variance identity.  This is kept independent
of the pivot definitions so an arithmetic producer may first establish
variance for whatever explicit complex error vector its prime toggles expose. -/
theorem sum_norm_sq_eq_centered_add_mean
    {α : Type*} [DecidableEq α] (T : Finset α) (z : α → ℂ)
    (hT : T.Nonempty) :
    (∑ i ∈ T, ‖z i‖ ^ 2) =
      (∑ i ∈ T,
        ‖z i - ((T.card : ℂ)⁻¹ * ∑ j ∈ T, z j)‖ ^ 2) +
      (T.card : ℝ) * ‖(T.card : ℂ)⁻¹ * ∑ j ∈ T, z j‖ ^ 2 := by
  let μ : ℂ := (T.card : ℂ)⁻¹ * ∑ j ∈ T, z j
  have hcardNat : T.card ≠ 0 := Finset.card_ne_zero.mpr hT
  have hcardComplex : (T.card : ℂ) ≠ 0 := by
    exact_mod_cast hcardNat
  have hcard_mul_mean : (T.card : ℂ) * μ = ∑ j ∈ T, z j := by
    dsimp [μ]
    rw [← mul_assoc, mul_inv_cancel₀ hcardComplex, one_mul]
  have hcentered : ∑ i ∈ T, (z i - μ) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hcard_mul_mean]
    exact sub_self _
  have hcross : ∑ i ∈ T, (((z i - μ) * starRingEnd ℂ μ).re) = 0 := by
    calc
      (∑ i ∈ T, (((z i - μ) * starRingEnd ℂ μ).re)) =
          ((∑ i ∈ T, (z i - μ) * starRingEnd ℂ μ)).re := by
            simp
      _ = (((∑ i ∈ T, (z i - μ)) * starRingEnd ℂ μ)).re := by
            rw [Finset.sum_mul]
      _ = 0 := by rw [hcentered]; simp
  change (∑ i ∈ T, ‖z i‖ ^ 2) =
    (∑ i ∈ T, ‖z i - μ‖ ^ 2) +
      (T.card : ℝ) * ‖μ‖ ^ 2
  simp_rw [← Complex.normSq_eq_norm_sq]
  calc
    (∑ i ∈ T, Complex.normSq (z i)) =
        ∑ i ∈ T, Complex.normSq ((z i - μ) + μ) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          ring
    _ = ∑ i ∈ T,
          (Complex.normSq (z i - μ) + Complex.normSq μ +
            2 * (((z i - μ) * starRingEnd ℂ μ).re)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Complex.normSq_add _ _
    _ = (∑ i ∈ T, Complex.normSq (z i - μ)) +
          (T.card : ℝ) * Complex.normSq μ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, hcross, mul_zero, add_zero,
            Finset.sum_const, nsmul_eq_mul]

/-- Exact pairwise-energy form of finite complex variance.  This is the
prime-toggle-friendly companion to `sum_norm_sq_eq_centered_add_mean`: an
arithmetic producer may lower-bound separated pairs directly, without first
guessing or estimating the fibre mean. -/
theorem sum_pairwise_norm_sq_eq_two_card_mul_centered
    {α : Type*} [DecidableEq α] (T : Finset α) (z : α → ℂ)
    (hT : T.Nonempty) :
    (∑ i ∈ T, ∑ j ∈ T, ‖z i - z j‖ ^ 2) =
      2 * (T.card : ℝ) *
        ∑ i ∈ T,
          ‖z i - ((T.card : ℂ)⁻¹ * ∑ j ∈ T, z j)‖ ^ 2 := by
  let μ : ℂ := (T.card : ℂ)⁻¹ * ∑ j ∈ T, z j
  let y : α → ℂ := fun i => z i - μ
  have hcardNat : T.card ≠ 0 := Finset.card_ne_zero.mpr hT
  have hcardComplex : (T.card : ℂ) ≠ 0 := by
    exact_mod_cast hcardNat
  have hcentered : ∑ i ∈ T, y i = 0 := by
    dsimp [y, μ]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hcardComplex, one_mul, sub_self]
  have hcrossRow (i : α) : ∑ j ∈ T,
      2 * (((y i) * starRingEnd ℂ (y j)).re) = 0 := by
    calc
      (∑ j ∈ T, 2 * (((y i) * starRingEnd ℂ (y j)).re)) =
          2 * ∑ j ∈ T, (((y i) * starRingEnd ℂ (y j)).re) := by
            rw [Finset.mul_sum]
      _ = 2 * ((∑ j ∈ T, y i * starRingEnd ℂ (y j)).re) := by
            simp
      _ = 2 * ((y i * starRingEnd ℂ (∑ j ∈ T, y j)).re) := by
            rw [map_sum, Finset.mul_sum]
      _ = 0 := by rw [hcentered]; simp
  have hcross : ∑ i ∈ T, ∑ j ∈ T,
      2 * (((y i) * starRingEnd ℂ (y j)).re) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hcrossRow i
  have hdiff (i j : α) : z i - z j = y i - y j := by
    dsimp [y]
    ring
  simp_rw [hdiff]
  change (∑ i ∈ T, ∑ j ∈ T, ‖y i - y j‖ ^ 2) =
    2 * (T.card : ℝ) * ∑ i ∈ T, ‖y i‖ ^ 2
  simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul]
  rw [hcross, sub_zero]
  rw [← Finset.mul_sum]
  ring

/-- A counted set of separated ordered pairs lower-bounds the full pairwise
energy.  Arithmetic arguments may therefore work on any explicitly selected
subset of the fibre square; they do not need to estimate every pair or the
unknown fibre mean. -/
theorem card_mul_sq_le_sum_pairwise_norm_sq_of_separatedPairs
    {α : Type*} [DecidableEq α] (T : Finset α) (z : α → ℂ)
    (P : Finset (α × α)) (δ : ℝ)
    (hP : P ⊆ T.product T)
    (hδ : 0 ≤ δ)
    (hsep : ∀ p ∈ P, δ ≤ ‖z p.1 - z p.2‖) :
    (P.card : ℝ) * δ ^ 2 ≤
      ∑ i ∈ T, ∑ j ∈ T, ‖z i - z j‖ ^ 2 := by
  calc
    (P.card : ℝ) * δ ^ 2 = ∑ p ∈ P, δ ^ 2 := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ p ∈ P, ‖z p.1 - z p.2‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hnorm : 0 ≤ ‖z p.1 - z p.2‖ := norm_nonneg _
      have := hsep p hp
      nlinarith
    _ ≤ ∑ p ∈ T.product T, ‖z p.1 - z p.2‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hP
        (fun p _ _ => sq_nonneg ‖z p.1 - z p.2‖)
    _ = ∑ i ∈ T, ∑ j ∈ T, ‖z i - z j‖ ^ 2 := by
      simpa using Finset.sum_product T T
        (fun p : α × α => ‖z p.1 - z p.2‖ ^ 2)

/-- Pairwise energy of the original vectors already controls their squared
distance from any fixed anchor.  This is the mean-free form needed by the
window-phase route: the unknown empirical mean contributes only a
nonnegative bias, so it never has to be estimated by the arithmetic
producer. -/
theorem card_div_five_le_sum_anchor_norm_sq_of_pairwise
    {α : Type*} [DecidableEq α] (T : Finset α) (z : α → ℂ) (a : ℂ)
    (hT : T.Nonempty)
    (hpair :
      2 * (T.card : ℝ) ^ 2 / 5 ≤
        ∑ i ∈ T, ∑ j ∈ T, ‖z i - z j‖ ^ 2) :
    (T.card : ℝ) / 5 ≤ ∑ i ∈ T, ‖z i - a‖ ^ 2 := by
  let y : α → ℂ := fun i => z i - a
  have hpairY :
      2 * (T.card : ℝ) ^ 2 / 5 ≤
        ∑ i ∈ T, ∑ j ∈ T, ‖y i - y j‖ ^ 2 := by
    simpa [y, sub_sub_sub_cancel_right] using hpair
  have henergy := sum_pairwise_norm_sq_eq_two_card_mul_centered T y hT
  have hdecomp := sum_norm_sq_eq_centered_add_mean T y hT
  have hcard : (0 : ℝ) < T.card := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hbias :
      0 ≤ (T.card : ℝ) * ‖(T.card : ℂ)⁻¹ * ∑ j ∈ T, y j‖ ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  rw [henergy] at hpairY
  change (T.card : ℝ) / 5 ≤ ∑ i ∈ T, ‖y i‖ ^ 2
  nlinarith [hdecomp]

/-- Actual reconstruction error on a canonical supplier fibre. -/
noncomputable def pivotReconstructionError (h N L s : ℕ) : ℂ :=
  pivotResidualAt h N L s -
    (starRingEnd ℂ) (pivotPhaseAt h N L s)

/-- The reconstruction error is the actual window anchor error, rotated by
the conjugate pivot phase.  In particular, this identity retains the full
residual coupling; no independence or phase-only surrogate is introduced. -/
theorem pivotReconstructionError_eq_conj_phase_mul_window_sub_one
    (h N L s : ℕ) :
    pivotReconstructionError h N L s =
      (starRingEnd ℂ) (pivotPhaseAt h N L s) *
        (windowFirstExp h N L - 1) := by
  have hphase : ‖pivotPhaseAt h N L s‖ = 1 := by
    simp [pivotPhaseAt]
  rw [pivotReconstructionError, pivotResidualAt, div_eq_mul_inv,
    Complex.inv_eq_conj hphase]
  ring

/-- Unweighted first mode of the actual window phase on one supplier fibre. -/
noncomputable def pivotFiberWindowMode
    (h X L s m : ℕ) : ℂ :=
  ∑ N ∈ pivotFiber X L s m, windowFirstExp h N L

/-- Residual-weighted first mode on one supplier fibre.  This is the
anti-lock coefficient: the conjugate pivot phase multiplies the complete
window phase, rather than a truncated or independently averaged proxy. -/
noncomputable def pivotFiberResidualMode
    (h X L s m : ℕ) : ℂ :=
  ∑ N ∈ pivotFiber X L s m,
    (starRingEnd ℂ) (pivotPhaseAt h N L s) * windowFirstExp h N L

/-- Bare conjugate-pivot mode on one supplier fibre. -/
noncomputable def pivotFiberConjugatePhaseMode
    (h X L s m : ℕ) : ℂ :=
  ∑ N ∈ pivotFiber X L s m,
    (starRingEnd ℂ) (pivotPhaseAt h N L s)

/-- The total reconstruction error is exactly the residual-weighted mode
minus the bare conjugate-pivot mode. -/
theorem pivotFiberReconstructionErrorSum_eq_twoMode
    (h X L s m : ℕ) :
    (∑ N ∈ pivotFiber X L s m, pivotReconstructionError h N L s) =
      pivotFiberResidualMode h X L s m -
        pivotFiberConjugatePhaseMode h X L s m := by
  simp only [pivotReconstructionError_eq_conj_phase_mul_window_sub_one,
    mul_sub, mul_one, pivotFiberResidualMode,
    pivotFiberConjugatePhaseMode, Finset.sum_sub_distrib]

/-- Mean reconstruction error on one canonical supplier fibre. -/
noncomputable def pivotFiberReconstructionErrorMean
    (h X L s m : ℕ) : ℂ :=
  ((pivotFiber X L s m).card : ℂ)⁻¹ *
    ∑ N ∈ pivotFiber X L s m, pivotReconstructionError h N L s

/-- Centred reconstruction-error energy on one canonical supplier fibre.
This is the literal variance socket for a prime-toggle producer. -/
noncomputable def pivotFiberReconstructionVariance
    (h X L s m : ℕ) : ℝ :=
  ∑ N ∈ pivotFiber X L s m,
    ‖pivotReconstructionError h N L s -
      pivotFiberReconstructionErrorMean h X L s m‖ ^ 2

/-- The actual pivot-fibre variance is exactly normalized pairwise energy.
This removes the unknown fibre mean from the remaining arithmetic producer. -/
theorem pivotFiberReconstructionVariance_eq_pairwise
    (h X L s m : ℕ) (hne : (pivotFiber X L s m).Nonempty) :
    2 * ((pivotFiber X L s m).card : ℝ) *
        pivotFiberReconstructionVariance h X L s m =
      ∑ N ∈ pivotFiber X L s m,
        ∑ N' ∈ pivotFiber X L s m,
          ‖pivotReconstructionError h N L s -
            pivotReconstructionError h N' L s‖ ^ 2 := by
  rw [sum_pairwise_norm_sq_eq_two_card_mul_centered
    (pivotFiber X L s m) (pivotReconstructionError h · L s) hne]
  rfl

/-- Pairwise-energy intake at the exact one-fifth threshold used by the
#249 consumer.  A prime-toggle or separated-pairs argument can target this
double sum directly; division by the unknown fibre cardinality is handled
here once and for all. -/
theorem pivotFiberReconstructionVariance_ge_one_fifth_of_pairwise
    {h X L s m : ℕ} (hne : (pivotFiber X L s m).Nonempty)
    (hpair :
      2 * ((pivotFiber X L s m).card : ℝ) ^ 2 / 5 ≤
        ∑ N ∈ pivotFiber X L s m,
          ∑ N' ∈ pivotFiber X L s m,
            ‖pivotReconstructionError h N L s -
              pivotReconstructionError h N' L s‖ ^ 2) :
    ((pivotFiber X L s m).card : ℝ) / 5 ≤
      pivotFiberReconstructionVariance h X L s m := by
  have hcard : (0 : ℝ) < (pivotFiber X L s m).card := by
    exact_mod_cast Finset.card_pos.mpr hne
  have henergy := pivotFiberReconstructionVariance_eq_pairwise h X L s m hne
  nlinarith

/-- A defect of at least one fifth per phase is exactly enough to invoke the
arbitrary-subset first-harmonic consumer. -/
theorem exists_certifiedKill_of_firstHarmonicAnchorDefect
    {h X L : ℕ} (T : Finset ℕ)
    (hTlt : ∀ N ∈ T, N < 2 * X)
    (hTne : T.Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hdefect :
      (T.card : ℝ) / 5 ≤ firstHarmonicAnchorDefect h L T) :
    ∃ N ∈ T, certifiedKill h N L := by
  apply exists_certifiedKill_of_first_harmonic_gap_subset
    T hTlt hTne hroom
  rw [firstHarmonicAnchorDefect_eq] at hdefect
  nlinarith

/-- Anchor defect restricted to one canonical large-prime supplier fibre. -/
noncomputable def pivotFiberReconstructionDefect
    (h X L s m : ℕ) : ℝ :=
  firstHarmonicAnchorDefect h L (pivotFiber X L s m)

/-- The uncentred part of reconstruction energy is the first of the two
actual fibre modes: cardinality minus the real window mode. -/
theorem pivotFiberReconstructionDefect_eq_twoModeAnchor
    (h X L s m : ℕ) :
    pivotFiberReconstructionDefect h X L s m =
      2 * ((pivotFiber X L s m).card : ℝ) -
        2 * (pivotFiberWindowMode h X L s m).re := by
  rw [pivotFiberReconstructionDefect, firstHarmonicAnchorDefect_eq]
  simp [pivotFiberWindowMode]

@[simp]
theorem norm_pivotResidualAt (h N L s : ℕ) :
    ‖pivotResidualAt h N L s‖ = 1 := by
  rw [pivotResidualAt, norm_div, norm_windowFirstExp]
  simp [pivotPhaseAt]

/-- On one pivot fibre, anchor defect is exactly squared distance of the
actual residual vector from the locked reconstruction `conj phase`. -/
theorem pivotFiberReconstructionDefect_eq_sum_residual_norm_sq
    (h X L s m : ℕ) :
    pivotFiberReconstructionDefect h X L s m =
      ∑ N ∈ pivotFiber X L s m,
        ‖pivotResidualAt h N L s -
          (starRingEnd ℂ) (pivotPhaseAt h N L s)‖ ^ 2 := by
  rw [pivotFiberReconstructionDefect,
    firstHarmonicAnchorDefect_eq_sum_norm_sq]
  apply Finset.sum_congr rfl
  intro N hN
  have hz : ‖pivotPhaseAt h N L s‖ = 1 := by
    simp [pivotPhaseAt]
  have hz0 : pivotPhaseAt h N L s ≠ 0 := by
    exact norm_ne_zero_iff.mp (by simp [hz])
  rw [windowFirstExp_eq_pivotResidualAt_mul_phase]
  congr 1
  calc
    ‖pivotResidualAt h N L s * pivotPhaseAt h N L s - 1‖
        = ‖(pivotResidualAt h N L s - (pivotPhaseAt h N L s)⁻¹) *
            pivotPhaseAt h N L s‖ := by
              congr 1
              rw [sub_mul, inv_mul_cancel₀ hz0]
    _ = ‖pivotResidualAt h N L s - (pivotPhaseAt h N L s)⁻¹‖ := by
          rw [norm_mul, hz, mul_one]
    _ = ‖pivotResidualAt h N L s -
          (starRingEnd ℂ) (pivotPhaseAt h N L s)‖ := by
          rw [Complex.inv_eq_conj hz]

/-- The existing reconstruction defect is variance plus the squared bias of
the same error vector.  In particular, positive conditional variance feeds
the #249 consumer without estimating the four-term pivot budget. -/
theorem pivotFiberReconstructionDefect_eq_variance_add_bias
    (h X L s m : ℕ) (hne : (pivotFiber X L s m).Nonempty) :
    pivotFiberReconstructionDefect h X L s m =
      pivotFiberReconstructionVariance h X L s m +
      ((pivotFiber X L s m).card : ℝ) *
        ‖pivotFiberReconstructionErrorMean h X L s m‖ ^ 2 := by
  rw [pivotFiberReconstructionDefect_eq_sum_residual_norm_sq]
  simpa [pivotReconstructionError, pivotFiberReconstructionVariance,
    pivotFiberReconstructionErrorMean] using
    sum_norm_sq_eq_centered_add_mean
      (pivotFiber X L s m) (pivotReconstructionError h · L s) hne

/-- Normalizing a complex sum by a nonempty finite cardinality converts its
squared mean contribution to the usual `‖sum‖² / card` form. -/
theorem card_mul_norm_inv_natCast_mul_sq_eq_div
    {α : Type*} [DecidableEq α] (T : Finset α) (hT : T.Nonempty) (z : ℂ) :
    (T.card : ℝ) * ‖(T.card : ℂ)⁻¹ * z‖ ^ 2 =
      ‖z‖ ^ 2 / (T.card : ℝ) := by
  have hcard : (T.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hT
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  field_simp

/-- Exact two-mode formula for centred reconstruction variance.  The first
mode is the unweighted window phase.  The second is the complete
residual-weighted mode, centred against the bare conjugate-pivot mode. -/
theorem pivotFiberReconstructionVariance_eq_twoMode
    (h X L s m : ℕ) (hne : (pivotFiber X L s m).Nonempty) :
    pivotFiberReconstructionVariance h X L s m =
      2 * ((pivotFiber X L s m).card : ℝ) -
        2 * (pivotFiberWindowMode h X L s m).re -
        ((pivotFiber X L s m).card : ℝ) *
          ‖((pivotFiber X L s m).card : ℂ)⁻¹ *
            (pivotFiberResidualMode h X L s m -
              pivotFiberConjugatePhaseMode h X L s m)‖ ^ 2 := by
  have hdecomp :=
    pivotFiberReconstructionDefect_eq_variance_add_bias h X L s m hne
  rw [pivotFiberReconstructionDefect_eq_twoModeAnchor,
    pivotFiberReconstructionErrorMean,
    pivotFiberReconstructionErrorSum_eq_twoMode] at hdecomp
  linarith

/-- Quotient form of the exact two-mode identity:
`V = 2|F| - 2 Re W₀ - ‖W₁-C₁‖²/|F|`. -/
theorem pivotFiberReconstructionVariance_eq_twoMode_div_card
    (h X L s m : ℕ) (hne : (pivotFiber X L s m).Nonempty) :
    pivotFiberReconstructionVariance h X L s m =
      2 * ((pivotFiber X L s m).card : ℝ) -
        2 * (pivotFiberWindowMode h X L s m).re -
        ‖pivotFiberResidualMode h X L s m -
          pivotFiberConjugatePhaseMode h X L s m‖ ^ 2 /
          ((pivotFiber X L s m).card : ℝ) := by
  rw [pivotFiberReconstructionVariance_eq_twoMode h X L s m hne,
    card_mul_norm_inv_natCast_mul_sq_eq_div (pivotFiber X L s m) hne]

/-- Lean-friendly sufficient two-mode bounds with strict slack over the
one-fifth consumer threshold.  The second hypothesis is the normalized
anti-lock coefficient `‖(W₁-C₁)/|F|‖ ≤ 2/5`. -/
theorem pivotFiberReconstructionVariance_ge_six_div_twentyfive_of_twoMode
    {h X L s m : ℕ} (hne : (pivotFiber X L s m).Nonempty)
    (hwindow :
      (pivotFiberWindowMode h X L s m).re ≤
        (4 / 5 : ℝ) * (pivotFiber X L s m).card)
    (hantilock :
      ‖((pivotFiber X L s m).card : ℂ)⁻¹ *
        (pivotFiberResidualMode h X L s m -
          pivotFiberConjugatePhaseMode h X L s m)‖ ≤ (2 / 5 : ℝ)) :
    (6 / 25 : ℝ) * (pivotFiber X L s m).card ≤
      pivotFiberReconstructionVariance h X L s m := by
  have hcard : (0 : ℝ) < (pivotFiber X L s m).card := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hnorm : 0 ≤ ‖((pivotFiber X L s m).card : ℂ)⁻¹ *
      (pivotFiberResidualMode h X L s m -
        pivotFiberConjugatePhaseMode h X L s m)‖ := norm_nonneg _
  have hnormsq :
      ‖((pivotFiber X L s m).card : ℂ)⁻¹ *
        (pivotFiberResidualMode h X L s m -
          pivotFiberConjugatePhaseMode h X L s m)‖ ^ 2 ≤ (4 / 25 : ℝ) := by
    nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hnormsq hcard.le
  rw [pivotFiberReconstructionVariance_eq_twoMode h X L s m hne]
  nlinarith

/-- The packet's separate `‖W₁‖ ≤ |F|/3` and `‖C₁‖ ≤ |F|/15`
bounds imply the normalized anti-lock bound used above. -/
theorem pivotFiberNormalizedAntiLock_le_two_fifths
    {h X L s m : ℕ} (hne : (pivotFiber X L s m).Nonempty)
    (hresidual :
      ‖pivotFiberResidualMode h X L s m‖ ≤
        ((pivotFiber X L s m).card : ℝ) / 3)
    (hphase :
      ‖pivotFiberConjugatePhaseMode h X L s m‖ ≤
        ((pivotFiber X L s m).card : ℝ) / 15) :
    ‖((pivotFiber X L s m).card : ℂ)⁻¹ *
      (pivotFiberResidualMode h X L s m -
        pivotFiberConjugatePhaseMode h X L s m)‖ ≤ (2 / 5 : ℝ) := by
  have hcard : (0 : ℝ) < (pivotFiber X L s m).card := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hsub :
      ‖pivotFiberResidualMode h X L s m -
        pivotFiberConjugatePhaseMode h X L s m‖ ≤
          (2 / 5 : ℝ) * (pivotFiber X L s m).card := by
    calc
      ‖pivotFiberResidualMode h X L s m -
          pivotFiberConjugatePhaseMode h X L s m‖
          ≤ ‖pivotFiberResidualMode h X L s m‖ +
              ‖pivotFiberConjugatePhaseMode h X L s m‖ := norm_sub_le _ _
      _ ≤ ((pivotFiber X L s m).card : ℝ) / 3 +
            ((pivotFiber X L s m).card : ℝ) / 15 := add_le_add hresidual hphase
      _ = (2 / 5 : ℝ) * (pivotFiber X L s m).card := by ring
  rw [norm_mul, norm_inv]
  simp only [Complex.norm_natCast]
  calc
    ((pivotFiber X L s m).card : ℝ)⁻¹ *
        ‖pivotFiberResidualMode h X L s m -
          pivotFiberConjugatePhaseMode h X L s m‖
        ≤ ((pivotFiber X L s m).card : ℝ)⁻¹ *
            ((2 / 5 : ℝ) * (pivotFiber X L s m).card) :=
          mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr hcard.le)
    _ = 2 / 5 := by field_simp

/-- The three concrete mode estimates from the natural-prime contour give
centred variance at least `6|F|/25`, hence strictly more than the consumer's
required `|F|/5`. -/
theorem pivotFiberReconstructionVariance_ge_six_div_twentyfive_of_modeBounds
    {h X L s m : ℕ} (hne : (pivotFiber X L s m).Nonempty)
    (hwindow :
      (pivotFiberWindowMode h X L s m).re ≤
        (4 / 5 : ℝ) * (pivotFiber X L s m).card)
    (hresidual :
      ‖pivotFiberResidualMode h X L s m‖ ≤
        ((pivotFiber X L s m).card : ℝ) / 3)
    (hphase :
      ‖pivotFiberConjugatePhaseMode h X L s m‖ ≤
        ((pivotFiber X L s m).card : ℝ) / 15) :
    (6 / 25 : ℝ) * (pivotFiber X L s m).card ≤
      pivotFiberReconstructionVariance h X L s m :=
  pivotFiberReconstructionVariance_ge_six_div_twentyfive_of_twoMode hne
    hwindow (pivotFiberNormalizedAntiLock_le_two_fifths hne hresidual hphase)

/-- A one-fibre anti-reconstruction bound produces a certificate in that
same fibre. -/
theorem exists_certifiedKill_of_pivotFiberReconstructionDefect
    {h X L s m : ℕ}
    (hne : (pivotFiber X L s m).Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hdefect :
      ((pivotFiber X L s m).card : ℝ) / 5 ≤
        pivotFiberReconstructionDefect h X L s m) :
    ∃ N ∈ pivotFiber X L s m, certifiedKill h N L := by
  refine exists_certifiedKill_of_firstHarmonicAnchorDefect
    (pivotFiber X L s m) ?_ hne hroom ?_
  · intro N hN
    have hNsupplier : N ∈ pivotSupplierBases X L s :=
      (Finset.mem_filter.mp hN).1
    exact (Finset.mem_Ico.mp (Finset.mem_filter.mp hNsupplier).1).2
  · simpa [pivotFiberReconstructionDefect] using hdefect

/-- A one-fifth lower bound on centred reconstruction variance is already
enough for the established one-fibre certificate consumer. -/
theorem exists_certifiedKill_of_pivotFiberReconstructionVariance
    {h X L s m : ℕ}
    (hne : (pivotFiber X L s m).Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hvariance :
      ((pivotFiber X L s m).card : ℝ) / 5 ≤
        pivotFiberReconstructionVariance h X L s m) :
    ∃ N ∈ pivotFiber X L s m, certifiedKill h N L := by
  apply exists_certifiedKill_of_pivotFiberReconstructionDefect hne hroom
  rw [pivotFiberReconstructionDefect_eq_variance_add_bias h X L s m hne]
  exact hvariance.trans (le_add_of_nonneg_right <| mul_nonneg
    (Nat.cast_nonneg _) (sq_nonneg _))

/-- Pairwise-energy version of the one-fibre certificate intake.  This is the
direct target for prime toggles or separated-pair counts: no fibre mean or
intermediate variance estimate remains at the call site. -/
theorem exists_certifiedKill_of_pivotFiberPairwiseEnergy
    {h X L s m : ℕ}
    (hne : (pivotFiber X L s m).Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hpair :
      2 * ((pivotFiber X L s m).card : ℝ) ^ 2 / 5 ≤
        ∑ N ∈ pivotFiber X L s m,
          ∑ N' ∈ pivotFiber X L s m,
            ‖pivotReconstructionError h N L s -
              pivotReconstructionError h N' L s‖ ^ 2) :
    ∃ N ∈ pivotFiber X L s m, certifiedKill h N L := by
  apply exists_certifiedKill_of_pivotFiberReconstructionVariance hne hroom
  exact pivotFiberReconstructionVariance_ge_one_fifth_of_pairwise hne hpair

/-- Counted-separated-pairs version of the one-fibre certificate intake.
This is a direct finite combinatorial target: supply a subset `P` of the
ordered fibre square, a uniform separation `δ`, and enough total mass
`|P| δ²`; the analytic variance layer and certificate extraction are then
automatic. -/
theorem exists_certifiedKill_of_pivotFiberSeparatedPairs
    {h X L s m : ℕ}
    (hne : (pivotFiber X L s m).Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (P : Finset (ℕ × ℕ)) (δ : ℝ)
    (hP : P ⊆ (pivotFiber X L s m).product (pivotFiber X L s m))
    (hδ : 0 ≤ δ)
    (hsep : ∀ p ∈ P,
      δ ≤ ‖pivotReconstructionError h p.1 L s -
        pivotReconstructionError h p.2 L s‖)
    (hmass :
      2 * ((pivotFiber X L s m).card : ℝ) ^ 2 / 5 ≤
        (P.card : ℝ) * δ ^ 2) :
    ∃ N ∈ pivotFiber X L s m, certifiedKill h N L := by
  apply exists_certifiedKill_of_pivotFiberPairwiseEnergy hne hroom
  exact hmass.trans
    (card_mul_sq_le_sum_pairwise_norm_sq_of_separatedPairs
      (pivotFiber X L s m) (pivotReconstructionError h · L s)
      P δ hP hδ hsep)

/-- Pairwise energy of the actual window phases controls the established
anchor defect directly.  Unlike reconstruction-error energy, this input has
no pivot phase or residual weighting: it is exactly a two-point
anti-concentration statement for the dyadic window character. -/
theorem pivotFiberReconstructionDefect_ge_one_fifth_of_windowPairwise
    {h X L s m : ℕ} (hne : (pivotFiber X L s m).Nonempty)
    (hpair :
      2 * ((pivotFiber X L s m).card : ℝ) ^ 2 / 5 ≤
        ∑ N ∈ pivotFiber X L s m,
          ∑ N' ∈ pivotFiber X L s m,
            ‖windowFirstExp h N L - windowFirstExp h N' L‖ ^ 2) :
    ((pivotFiber X L s m).card : ℝ) / 5 ≤
      pivotFiberReconstructionDefect h X L s m := by
  rw [pivotFiberReconstructionDefect,
    firstHarmonicAnchorDefect_eq_sum_norm_sq]
  exact card_div_five_le_sum_anchor_norm_sq_of_pairwise
    (pivotFiber X L s m) (windowFirstExp h · L) 1 hne hpair

/-- Direct finite certificate intake for window-phase pairwise energy. -/
theorem exists_certifiedKill_of_pivotFiberWindowPairwiseEnergy
    {h X L s m : ℕ}
    (hne : (pivotFiber X L s m).Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hpair :
      2 * ((pivotFiber X L s m).card : ℝ) ^ 2 / 5 ≤
        ∑ N ∈ pivotFiber X L s m,
          ∑ N' ∈ pivotFiber X L s m,
            ‖windowFirstExp h N L - windowFirstExp h N' L‖ ^ 2) :
    ∃ N ∈ pivotFiber X L s m, certifiedKill h N L := by
  apply exists_certifiedKill_of_pivotFiberReconstructionDefect hne hroom
  exact pivotFiberReconstructionDefect_ge_one_fifth_of_windowPairwise hne hpair

/-- Counted separated pairs of raw window phases feed the direct pairwise
energy intake.  This is the arithmetic-facing finite lattice socket: a
producer may count phase-separated dyadic residues without reconstructing
or estimating the pivot residual. -/
theorem exists_certifiedKill_of_pivotFiberWindowSeparatedPairs
    {h X L s m : ℕ}
    (hne : (pivotFiber X L s m).Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (P : Finset (ℕ × ℕ)) (δ : ℝ)
    (hP : P ⊆ (pivotFiber X L s m).product (pivotFiber X L s m))
    (hδ : 0 ≤ δ)
    (hsep : ∀ p ∈ P,
      δ ≤ ‖windowFirstExp h p.1 L - windowFirstExp h p.2 L‖)
    (hmass :
      2 * ((pivotFiber X L s m).card : ℝ) ^ 2 / 5 ≤
        (P.card : ℝ) * δ ^ 2) :
    ∃ N ∈ pivotFiber X L s m, certifiedKill h N L := by
  apply exists_certifiedKill_of_pivotFiberWindowPairwiseEnergy hne hroom
  exact hmass.trans
    (card_mul_sq_le_sum_pairwise_norm_sq_of_separatedPairs
      (pivotFiber X L s m) (windowFirstExp h · L) P δ hP hδ hsep)

/-- General uncentred producer: cofinally, one nonempty actual supplier fibre
stays a fixed squared distance from locked reconstruction. -/
def DTWPivotAntiReconstruction : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X L s m : ℕ,
      max X₀ 1 ≤ X ∧
      0 < s ∧
      h ≤ L - s ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      (pivotFiber X L s m).Nonempty ∧
      ((pivotFiber X L s m).card : ℝ) / 5 ≤
        pivotFiberReconstructionDefect h X L s m

/-- Stronger variance-only form of the cofinal producer.  Compared with
`DTWPivotAntiReconstruction`, this discards the nonnegative mean-error bias
and asks a prime-toggle argument only for centred fibre energy. -/
def DTWPivotReconstructionVariance : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X L s m : ℕ,
      max X₀ 1 ≤ X ∧
      0 < s ∧
      h ≤ L - s ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      (pivotFiber X L s m).Nonempty ∧
      ((pivotFiber X L s m).card : ℝ) / 5 ≤
        pivotFiberReconstructionVariance h X L s m

/-- Cofinal first-harmonic escape on the canonical natural prime fibre.
This is the weakest fibre-average input consumed by the uncentred anchor
defect: no residual-weighted or centred-variance estimate is present. -/
def DTWNaturalPivotWindowGap : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X L : ℕ,
      max X₀ 4 ≤ X ∧
      h < L ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      (pivotFiber X L (L - h) 1).Nonempty ∧
      (pivotFiberWindowMode h X L (L - h) 1).re ≤
        (9 / 10 : ℝ) * (pivotFiber X L (L - h) 1).card

/-- Strictly weaker pointwise socket: cofinally, one member of the canonical
natural prime fibre escapes the locked first-harmonic arc.  The singleton
subset consumer turns this directly into a certificate, so neither a fibre
average nor centred variance is logically required. -/
def DTWNaturalPivotPointEscape : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X L N : ℕ,
      max X₀ 4 ≤ X ∧
      h < L ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      N ∈ pivotFiber X L (L - h) 1 ∧
      windowFirstCos h N L ≤ (9 / 10 : ℝ)

/-- Prime-indexed gap in the exact infinite tail orbit.  This removes all
finite-window, dyadic-room, and supplier bookkeeping from the remaining
arithmetic theorem: primality selects the lacunary exponent, while the
phase is exactly `scaledTotientSeriesFirstExp`. -/
def DTWNaturalPrimeTailOrbitGap : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ p : ℕ,
      max (N₀ + h + 1) (h + 5) ≤ p ∧
      p.Prime ∧
      (tailOrbitFirstExp h (p - h - 1)).re ≤ (4 / 5 : ℝ)

/-- The prime-indexed infinite-orbit gap supplies the finite-window
singleton escape.  Exponential depth pays the room and truncation budgets;
the natural-fibre membership is the exact shifted-prime equivalence. -/
theorem naturalPivotPointEscape_of_naturalPrimeTailOrbitGap
    (hgap : DTWNaturalPrimeTailOrbitGap) :
    DTWNaturalPivotPointEscape := by
  intro h hh N₀
  obtain ⟨p, hpN, hp, htail⟩ := hgap h hh N₀
  let N := p - h - 1
  have hN₀ : N₀ ≤ N := by dsimp [N]; omega
  have hN4 : 4 ≤ N := by dsimp [N]; omega
  obtain ⟨L, hL, hroom, herror⟩ :=
    exists_natural_window_depth_with_error h N (h + 1) (1 / 10 : ℝ) (by norm_num)
  have hhL : h < L := by omega
  refine ⟨N, L, N, max_le hN₀ hN4, hhL, hroom, ?_, ?_⟩
  · apply (mem_pivotFiber_one_overlap_iff hN4 (Nat.le_of_lt hhL)).2
    refine ⟨le_rfl, by omega, ?_⟩
    have heq : N + h + 1 = p := by dsimp [N]; omega
    rwa [heq]
  · apply windowFirstCos_le_nine_tenths_of_tailOrbitGap
    · simpa [N] using htail
    · exact herror

/-- Stronger optional spectral producer on the canonical natural prime
fibre.  Its first conjunct implies `DTWNaturalPivotWindowGap`; the residual
and conjugate-pivot conjuncts are needed only for the centred-variance route. -/
def DTWNaturalPivotTwoModeCancellation : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X L : ℕ,
      max X₀ 4 ≤ X ∧
      h < L ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      (pivotFiber X L (L - h) 1).Nonempty ∧
      (pivotFiberWindowMode h X L (L - h) 1).re ≤
        (4 / 5 : ℝ) * (pivotFiber X L (L - h) 1).card ∧
      ‖pivotFiberResidualMode h X L (L - h) 1‖ ≤
        ((pivotFiber X L (L - h) 1).card : ℝ) / 3 ∧
      ‖pivotFiberConjugatePhaseMode h X L (L - h) 1‖ ≤
        ((pivotFiber X L (L - h) 1).card : ℝ) / 15

/-- Mean-free, cofinal pairwise-energy producer.  This is equivalent to a
sufficient reconstruction-variance supply through the exact finite-fibre
identity, while exposing only pair differences to arithmetic arguments. -/
def DTWPivotPairwiseReconstructionEnergy : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X L s m : ℕ,
      max X₀ 1 ≤ X ∧
      0 < s ∧
      h ≤ L - s ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      (pivotFiber X L s m).Nonempty ∧
      2 * ((pivotFiber X L s m).card : ℝ) ^ 2 / 5 ≤
        ∑ N ∈ pivotFiber X L s m,
          ∑ N' ∈ pivotFiber X L s m,
            ‖pivotReconstructionError h N L s -
              pivotReconstructionError h N' L s‖ ^ 2

/-- Cofinal counted-separated-pairs producer.  This is a finite lattice and
combinatorics socket beneath the pairwise-energy formulation: a proof may
select only the arithmetically controlled ordered pairs and certify their
common separation. -/
def DTWPivotSeparatedPairs : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X L s m : ℕ, ∃ P : Finset (ℕ × ℕ), ∃ δ : ℝ,
      max X₀ 1 ≤ X ∧
      0 < s ∧
      h ≤ L - s ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      (pivotFiber X L s m).Nonempty ∧
      P ⊆ (pivotFiber X L s m).product (pivotFiber X L s m) ∧
      0 ≤ δ ∧
      (∀ p ∈ P,
        δ ≤ ‖pivotReconstructionError h p.1 L s -
          pivotReconstructionError h p.2 L s‖) ∧
      2 * ((pivotFiber X L s m).card : ℝ) ^ 2 / 5 ≤
        (P.card : ℝ) * δ ^ 2

/-- Cofinal pairwise energy of the raw finite-window phases.  This is more
direct and arithmetic-facing than reconstruction-error energy because it
contains neither the pivot phase nor the residual quotient. -/
def DTWPivotWindowPairwiseEnergy : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X L s m : ℕ,
      max X₀ 1 ≤ X ∧
      0 < s ∧
      h ≤ L - s ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      (pivotFiber X L s m).Nonempty ∧
      2 * ((pivotFiber X L s m).card : ℝ) ^ 2 / 5 ≤
        ∑ N ∈ pivotFiber X L s m,
          ∑ N' ∈ pivotFiber X L s m,
            ‖windowFirstExp h N L - windowFirstExp h N' L‖ ^ 2

/-- Counted-separated-pairs form of raw window-phase anti-concentration.
The remaining producer may select any controlled subset of the ordered fibre
square and prove one common chord separation. -/
def DTWPivotWindowSeparatedPairs : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ X₀ : ℕ, ∃ X L s m : ℕ, ∃ P : Finset (ℕ × ℕ), ∃ δ : ℝ,
      max X₀ 1 ≤ X ∧
      0 < s ∧
      h ≤ L - s ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      (pivotFiber X L s m).Nonempty ∧
      P ⊆ (pivotFiber X L s m).product (pivotFiber X L s m) ∧
      0 ≤ δ ∧
      (∀ p ∈ P,
        δ ≤ ‖windowFirstExp h p.1 L - windowFirstExp h p.2 L‖) ∧
      2 * ((pivotFiber X L s m).card : ℝ) ^ 2 / 5 ≤
        (P.card : ℝ) * δ ^ 2

/-- Fixed-shift fibre-free counted window-phase anti-concentration.  The
sample `T` may be any nonempty subset of a cofinal dyadic block. -/
def DTWWindowSeparatedPairsAt (h : ℕ) : Prop :=
  ∀ X₀ : ℕ, ∃ X L : ℕ, ∃ T : Finset ℕ,
      ∃ P : Finset (ℕ × ℕ), ∃ δ : ℝ,
      max X₀ 1 ≤ X ∧
      T.Nonempty ∧
      T ⊆ Finset.Ico X (2 * X) ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      P ⊆ T.product T ∧
      0 ≤ δ ∧
      (∀ p ∈ P,
        δ ≤ ‖windowFirstExp h p.1 L - windowFirstExp h p.2 L‖) ∧
      2 * (T.card : ℝ) ^ 2 / 5 ≤ (P.card : ℝ) * δ ^ 2

/-- Fibre-free counted window-phase anti-concentration at every positive
shift; neither primality nor a pivot factorization is part of the statement. -/
def DTWWindowSeparatedPairs : Prop :=
  ∀ h : ℕ, 0 < h → DTWWindowSeparatedPairsAt h

/-- The fibre-free predicate is genuinely weaker than its pivot-fibre
specialization: forget the factorization data and retain the same sample and
separated pairs inside the ambient dyadic block. -/
theorem windowSeparatedPairs_of_pivotWindowSeparatedPairs
    (hsep : DTWPivotWindowSeparatedPairs) :
    DTWWindowSeparatedPairs := by
  intro h hh X₀
  obtain ⟨X, L, s, m, P, δ, hX, _hs, _hoverlap, hroom, hne,
    hP, hδ, hpairs, hmass⟩ := hsep h hh X₀
  refine ⟨X, L, pivotFiber X L s m, P, δ,
    hX, hne, ?_, hroom, hP, hδ, hpairs, hmass⟩
  intro N hN
  have hNsupplier : N ∈ pivotSupplierBases X L s :=
    (Finset.mem_filter.mp hN).1
  exact (Finset.mem_filter.mp hNsupplier).1

/-- Counted raw-window pairs supply the complete window pairwise energy. -/
theorem pivotWindowPairwiseEnergy_of_windowSeparatedPairs
    (hsep : DTWPivotWindowSeparatedPairs) :
    DTWPivotWindowPairwiseEnergy := by
  intro h hh X₀
  obtain ⟨X, L, s, m, P, δ, hX, hs, hoverlap, hroom, hne,
    hP, hδ, hpairs, hmass⟩ := hsep h hh X₀
  refine ⟨X, L, s, m, hX, hs, hoverlap, hroom, hne, ?_⟩
  exact hmass.trans
    (card_mul_sq_le_sum_pairwise_norm_sq_of_separatedPairs
      (pivotFiber X L s m) (windowFirstExp h · L) P δ hP hδ hpairs)

/-- Raw-window pairwise anti-concentration feeds the existing uncentred
anchor defect without passing through reconstruction variance. -/
theorem pivotAntiReconstruction_of_windowPairwiseEnergy
    (hpair : DTWPivotWindowPairwiseEnergy) :
    DTWPivotAntiReconstruction := by
  intro h hh X₀
  obtain ⟨X, L, s, m, hX, hs, hoverlap, hroom, hne, henergy⟩ :=
    hpair h hh X₀
  exact ⟨X, L, s, m, hX, hs, hoverlap, hroom, hne,
    pivotFiberReconstructionDefect_ge_one_fifth_of_windowPairwise hne henergy⟩

/-- Counted separated pairs supply the complete pairwise energy demanded by
the existing #249 variance route. -/
theorem pivotPairwiseReconstructionEnergy_of_separatedPairs
    (hsep : DTWPivotSeparatedPairs) :
    DTWPivotPairwiseReconstructionEnergy := by
  intro h hh X₀
  obtain ⟨X, L, s, m, P, δ, hX, hs, hoverlap, hroom, hne,
    hP, hδ, hpairs, hmass⟩ := hsep h hh X₀
  refine ⟨X, L, s, m, hX, hs, hoverlap, hroom, hne, ?_⟩
  exact hmass.trans
    (card_mul_sq_le_sum_pairwise_norm_sq_of_separatedPairs
      (pivotFiber X L s m) (pivotReconstructionError h · L s)
      P δ hP hδ hpairs)

/-- Pairwise-energy supply feeds the established centred-variance producer. -/
theorem pivotReconstructionVariance_of_pairwiseEnergy
    (hpair : DTWPivotPairwiseReconstructionEnergy) :
    DTWPivotReconstructionVariance := by
  intro h hh X₀
  obtain ⟨X, L, s, m, hX, hs, hoverlap, hroom, hne, henergy⟩ :=
    hpair h hh X₀
  exact ⟨X, L, s, m, hX, hs, hoverlap, hroom, hne,
    pivotFiberReconstructionVariance_ge_one_fifth_of_pairwise hne henergy⟩

/-- The old two-mode socket implies the canonical window-gap socket using
only its unweighted first-mode conjunct. -/
theorem naturalPivotWindowGap_of_naturalPivotTwoModeCancellation
    (htwo : DTWNaturalPivotTwoModeCancellation) :
    DTWNaturalPivotWindowGap := by
  intro h hh X₀
  obtain ⟨X, L, hX, hL, hroom, hne, hwindow, _hresidual, _hphase⟩ :=
    htwo h hh X₀
  refine ⟨X, L, hX, hL, hroom, hne, ?_⟩
  have hcard : (0 : ℝ) ≤ (pivotFiber X L (L - h) 1).card :=
    Nat.cast_nonneg _
  nlinarith

/-- Natural-prime window escape directly supplies uncentred pivot
anti-reconstruction.  The proof uses exactly `D_F = 2|F| - 2 Re W₀`; the
residual-weighted modes never enter. -/
theorem pivotAntiReconstruction_of_naturalPivotWindowGap
    (hgap : DTWNaturalPivotWindowGap) :
    DTWPivotAntiReconstruction := by
  intro h hh X₀
  obtain ⟨X, L, hX, hL, hroom, hne, hwindow⟩ := hgap h hh X₀
  refine ⟨X, L, L - h, 1, ?_, ?_, ?_, hroom, hne, ?_⟩
  · omega
  · omega
  · omega
  · rw [pivotFiberReconstructionDefect_eq_twoModeAnchor]
    have hcard : (0 : ℝ) ≤ (pivotFiber X L (L - h) 1).card :=
      Nat.cast_nonneg _
    nlinarith

/-- The concrete natural-prime two-mode cancellation theorem supplies the
existing cofinal reconstruction-variance socket, with `6/25` arithmetic
slack before the `1/5` consumer threshold. -/
theorem pivotReconstructionVariance_of_naturalPivotTwoModeCancellation
    (htwo : DTWNaturalPivotTwoModeCancellation) :
    DTWPivotReconstructionVariance := by
  intro h hh X₀
  obtain ⟨X, L, hX, hL, hroom, hne, hwindow, hresidual, hphase⟩ :=
    htwo h hh X₀
  refine ⟨X, L, L - h, 1, ?_, ?_, ?_, hroom, hne, ?_⟩
  · omega
  · omega
  · omega
  · have h6 :=
      pivotFiberReconstructionVariance_ge_six_div_twentyfive_of_modeBounds
        hne hwindow hresidual hphase
    have hcard : (0 : ℝ) ≤ (pivotFiber X L (L - h) 1).card :=
      Nat.cast_nonneg _
    nlinarith

/-- Cofinal reconstruction variance is a sufficient arithmetic producer for
the established anti-reconstruction predicate. -/
theorem pivotAntiReconstruction_of_reconstructionVariance
    (hvariance : DTWPivotReconstructionVariance) :
    DTWPivotAntiReconstruction := by
  intro h hh X₀
  obtain ⟨X, L, s, m, hX, hs, hoverlap, hroom, hne, hvar⟩ :=
    hvariance h hh X₀
  refine ⟨X, L, s, m, hX, hs, hoverlap, hroom, hne, ?_⟩
  rw [pivotFiberReconstructionDefect_eq_variance_add_bias h X L s m hne]
  exact hvar.trans (le_add_of_nonneg_right <| mul_nonneg
    (Nat.cast_nonneg _) (sq_nonneg _))

/-- Cofinal pivot anti-reconstruction composes through the established
certificate-supply theorem to the #249 irrationality target. -/
theorem irrational_totient_series_of_pivotAntiReconstruction
    (hmix : DTWPivotAntiReconstruction) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_certificate_supply
  intro h hh N₀
  obtain ⟨X, L, s, m, hX, hs, hoverlap, hroom, hne, hdefect⟩ :=
    hmix h hh N₀
  obtain ⟨N, hNF, hkill⟩ :=
    exists_certifiedKill_of_pivotFiberReconstructionDefect hne hroom hdefect
  have hNIco : N ∈ Finset.Ico X (2 * X) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hNF).1).1
  exact ⟨N,
    le_trans (le_trans (Nat.le_max_left _ _) hX)
      (Finset.mem_Ico.mp hNIco).1,
    L, hkill⟩

/-- Exact natural-prime first-mode endpoint.  A cofinal `9/10` window gap on
the genuine cofactor-one fibre is sufficient for #249. -/
theorem irrational_totient_series_of_naturalPivotWindowGap
    (hgap : DTWNaturalPivotWindowGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_pivotAntiReconstruction
    (pivotAntiReconstruction_of_naturalPivotWindowGap hgap)

/-- Exact singleton endpoint.  A cofinal point escape inside the canonical
natural fibre feeds the arbitrary-subset consumer with the singleton `{N}`. -/
theorem irrational_totient_series_of_naturalPivotPointEscape
    (hpoint : DTWNaturalPivotPointEscape) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_certificate_supply
  intro h hh N₀
  obtain ⟨X, L, N, hX, _hL, hroom, hNF, hgap⟩ := hpoint h hh N₀
  have hNIco : N ∈ Finset.Ico X (2 * X) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hNF).1).1
  have hsingletonGap :
      (∑ M ∈ ({N} : Finset ℕ), windowFirstCos h M L) ≤
        (9 / 10 : ℝ) * ({N} : Finset ℕ).card := by
    simpa using hgap
  obtain ⟨M, hM, hkill⟩ :=
    exists_certifiedKill_of_first_harmonic_gap_subset
      ({N} : Finset ℕ) (by simpa using (Finset.mem_Ico.mp hNIco).2)
        (by simp) hroom hsingletonGap
  have hMN : M = N := by simpa using hM
  subst M
  exact ⟨N, le_trans (le_trans (Nat.le_max_left _ _) hX)
    (Finset.mem_Ico.mp hNIco).1, L, hkill⟩

/-- Exact prime-orbit endpoint.  The only assumed producer is a cofinal
real-part gap for the prime-indexed infinite tail orbit; all finite
certificate infrastructure is checked by the preceding bridge. -/
theorem irrational_totient_series_of_naturalPrimeTailOrbitGap
    (hgap : DTWNaturalPrimeTailOrbitGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_naturalPivotPointEscape
    (naturalPivotPointEscape_of_naturalPrimeTailOrbitGap hgap)

/-- Exact #249 variance endpoint: proving the cofinal centred-error producer
alone implies irrationality through the checked anti-reconstruction bridge. -/
theorem irrational_totient_series_of_pivotReconstructionVariance
    (hvariance : DTWPivotReconstructionVariance) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_pivotAntiReconstruction
    (pivotAntiReconstruction_of_reconstructionVariance hvariance)

/-- Exact #249 pairwise-energy endpoint. -/
theorem irrational_totient_series_of_pivotPairwiseReconstructionEnergy
    (hpair : DTWPivotPairwiseReconstructionEnergy) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_pivotReconstructionVariance
    (pivotReconstructionVariance_of_pairwiseEnergy hpair)

/-- Exact #249 counted-separated-pairs endpoint. -/
theorem irrational_totient_series_of_pivotSeparatedPairs
    (hsep : DTWPivotSeparatedPairs) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_pivotPairwiseReconstructionEnergy
    (pivotPairwiseReconstructionEnergy_of_separatedPairs hsep)

/-- Exact #249 raw-window pairwise-energy endpoint. -/
theorem irrational_totient_series_of_pivotWindowPairwiseEnergy
    (hpair : DTWPivotWindowPairwiseEnergy) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_pivotAntiReconstruction
    (pivotAntiReconstruction_of_windowPairwiseEnergy hpair)

/-- Exact #249 raw-window counted-separated-pairs endpoint.  This is the
pivot-fibre two-point socket: the arithmetic producer controls only dyadic
window phases and their counted chord separation. -/
theorem irrational_totient_series_of_pivotWindowSeparatedPairs
    (hsep : DTWPivotWindowSeparatedPairs) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_pivotWindowPairwiseEnergy
    (pivotWindowPairwiseEnergy_of_windowSeparatedPairs hsep)

/-- Exact fibre-free #249 counted-separated-pairs endpoint.  Enough
two-point anti-concentration on any cofinal finite block forces an actual
finite certificate; all mean, anchor, and certificate extraction steps are
discharged here. -/
theorem irrational_totient_series_of_windowSeparatedPairs
    (hsep : DTWWindowSeparatedPairs) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_certificate_supply
  intro h hh N₀
  obtain ⟨X, L, T, P, δ, hX, hTne, hT, hroom,
    hP, hδ, hpairs, hmass⟩ := hsep h hh N₀
  have henergy :
      2 * (T.card : ℝ) ^ 2 / 5 ≤
        ∑ N ∈ T, ∑ N' ∈ T,
          ‖windowFirstExp h N L - windowFirstExp h N' L‖ ^ 2 :=
    hmass.trans
      (card_mul_sq_le_sum_pairwise_norm_sq_of_separatedPairs
        T (windowFirstExp h · L) P δ hP hδ hpairs)
  have hdefect :
      (T.card : ℝ) / 5 ≤ firstHarmonicAnchorDefect h L T := by
    rw [firstHarmonicAnchorDefect_eq_sum_norm_sq]
    exact card_div_five_le_sum_anchor_norm_sq_of_pairwise
      T (windowFirstExp h · L) 1 hTne henergy
  have hTlt : ∀ N ∈ T, N < 2 * X := by
    intro N hN
    exact (Finset.mem_Ico.mp (hT hN)).2
  obtain ⟨N, hNT, hkill⟩ :=
    exists_certifiedKill_of_firstHarmonicAnchorDefect
      T hTlt hTne hroom hdefect
  have hXN : X ≤ N := (Finset.mem_Ico.mp (hT hNT)).1
  exact ⟨N, (Nat.le_max_left N₀ 1).trans (hX.trans hXN), L, hkill⟩

/-- Any cofinal adjacent-chord escape for the exact scaled orbit supplies the
fixed-shift fibre-free endpoint.  Depth is chosen so both finite phases are
within `1/20`; the sample `{N, N + 1}` with both ordered pairs has separation
`9/10` and the required counted energy. -/
theorem windowSeparatedPairsAt_of_cofinally_scaled_adjacent_chord
    (h : ℕ)
    (hcofinal : ∀ N₀, ∃ N ≥ N₀,
      1 ≤ ‖scaledTotientSeriesFirstExp h (N + 1) -
        scaledTotientSeriesFirstExp h N‖) :
    DTWWindowSeparatedPairsAt h := by
  intro X₀
  obtain ⟨N, hN, horbitScaled⟩ := hcofinal (max X₀ 2)
  obtain ⟨L, _hL, hroom', herror⟩ :=
    exists_natural_window_depth_with_error
      h (N + 1) 0 (1 / 20 : ℝ) (by norm_num)
  have hN2 : 2 ≤ N := by omega
  have hroom : 16 * (2 * N + h + L + 2) ≤ 2 ^ L := by
    omega
  have herrorN :
      2 * Real.pi * ((N : ℝ) + L + h + 2) / 2 ^ L ≤
        (1 / 20 : ℝ) := by
    calc
      2 * Real.pi * ((N : ℝ) + L + h + 2) / 2 ^ L =
          (2 * Real.pi / (2 : ℝ) ^ L) *
            ((N : ℝ) + L + h + 2) := by ring
      _ ≤ (2 * Real.pi / (2 : ℝ) ^ L) *
            (((N + 1 : ℕ) : ℝ) + L + h + 2) := by
          gcongr
          norm_num
      _ = 2 * Real.pi * (((N + 1 : ℕ) : ℝ) + L + h + 2) /
            2 ^ L := by ring
      _ ≤ (1 / 20 : ℝ) := herror
  have herrN :
      ‖windowFirstExp h N L - tailOrbitFirstExp h N‖ <
        (1 / 20 : ℝ) :=
    (norm_windowFirstExp_sub_tailOrbitFirstExp_lt h N L).trans_le herrorN
  have herrSucc :
      ‖windowFirstExp h (N + 1) L - tailOrbitFirstExp h (N + 1)‖ <
        (1 / 20 : ℝ) :=
    (norm_windowFirstExp_sub_tailOrbitFirstExp_lt h (N + 1) L).trans_le herror
  have horbit :
      1 ≤ ‖tailOrbitFirstExp h (N + 1) - tailOrbitFirstExp h N‖ := by
    simpa only [tailOrbitFirstExp_eq_scaledTotientSeriesFirstExp] using
      horbitScaled
  have htriangle :
      ‖tailOrbitFirstExp h (N + 1) - tailOrbitFirstExp h N‖ ≤
        ‖tailOrbitFirstExp h (N + 1) - windowFirstExp h (N + 1) L‖ +
          ‖windowFirstExp h (N + 1) L - windowFirstExp h N L‖ +
          ‖windowFirstExp h N L - tailOrbitFirstExp h N‖ := by
    calc
      ‖tailOrbitFirstExp h (N + 1) - tailOrbitFirstExp h N‖ =
          ‖(tailOrbitFirstExp h (N + 1) - windowFirstExp h (N + 1) L) +
            (windowFirstExp h (N + 1) L - windowFirstExp h N L) +
            (windowFirstExp h N L - tailOrbitFirstExp h N)‖ := by
              congr 1
              ring
      _ ≤ ‖(tailOrbitFirstExp h (N + 1) - windowFirstExp h (N + 1) L) +
            (windowFirstExp h (N + 1) L - windowFirstExp h N L)‖ +
            ‖windowFirstExp h N L - tailOrbitFirstExp h N‖ := norm_add_le _ _
      _ ≤ (‖tailOrbitFirstExp h (N + 1) - windowFirstExp h (N + 1) L‖ +
            ‖windowFirstExp h (N + 1) L - windowFirstExp h N L‖) +
            ‖windowFirstExp h N L - tailOrbitFirstExp h N‖ := by
              gcongr
              exact norm_add_le _ _
  have herrSuccRev :
      ‖tailOrbitFirstExp h (N + 1) - windowFirstExp h (N + 1) L‖ <
        (1 / 20 : ℝ) := by
    simpa [norm_sub_rev] using herrSucc
  have hfiniteSep :
      (9 / 10 : ℝ) ≤
        ‖windowFirstExp h (N + 1) L - windowFirstExp h N L‖ := by
    nlinarith
  refine ⟨N, L, ({N, N + 1} : Finset ℕ),
    ({(N, N + 1), (N + 1, N)} : Finset (ℕ × ℕ)),
    (9 / 10 : ℝ), ?_, ?_, ?_, hroom, ?_, ?_, ?_, ?_⟩
  · omega
  · simp
  · intro M hM
    simp only [Finset.mem_insert, Finset.mem_singleton] at hM
    rcases hM with rfl | rfl <;> simp only [Finset.mem_Ico] <;> omega
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp
  · norm_num
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · simpa [norm_sub_rev] using hfiniteSep
    · exact hfiniteSep
  · have hne : N + 1 ≠ N := by omega
    norm_num [hne]

/-- A non-dyadic fixed scaled series supplies the fixed-shift window-pair
endpoint by doubling expansivity. -/
theorem windowSeparatedPairsAt_of_not_dyadic_scaled_totient_series
    (h : ℕ)
    (hnd : ¬ IsDyadicReal
      (((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))) :
    DTWWindowSeparatedPairsAt h :=
  windowSeparatedPairsAt_of_cofinally_scaled_adjacent_chord h
    (cofinally_scaledTotientSeriesFirstExp_adjacent_chord_ge_one_of_not_dyadic
      h hnd)

/-- Irrationality itself supplies the fibre-free endpoint at every positive
shift. -/
theorem windowSeparatedPairs_of_irrational_totient_series
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    DTWWindowSeparatedPairs := by
  intro h hh
  exact windowSeparatedPairsAt_of_cofinally_scaled_adjacent_chord h
    (cofinally_scaledTotientSeriesFirstExp_adjacent_chord_ge_one hS h hh)

/-- The fibre-free window-pair endpoint is exactly equivalent to the
irrationality of the #249 totient series.  It is a useful geometric interface,
but not a logically weaker unresolved arithmetic obligation. -/
theorem dtwWindowSeparatedPairs_iff_irrational_totient_series :
    DTWWindowSeparatedPairs ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨irrational_totient_series_of_windowSeparatedPairs,
    windowSeparatedPairs_of_irrational_totient_series⟩

/-- Compatibility endpoint for the stronger two-mode socket.  Its proof now
flows through the weaker window-gap route, making explicit that the `W₁` and
`C₁` conjuncts are not on the certificate consumer's critical path. -/
theorem irrational_totient_series_of_naturalPivotTwoModeCancellation
    (htwo : DTWNaturalPivotTwoModeCancellation) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_naturalPivotWindowGap
    (naturalPivotWindowGap_of_naturalPivotTwoModeCancellation htwo)

#print axioms exists_certifiedKill_of_firstHarmonicAnchorDefect
#print axioms tail_diff_eq_scaled_totient_series_sub_prefix
#print axioms tailOrbitFirstExp_eq_scaledTotientSeriesFirstExp
#print axioms windowFirstExp_eq_unreduced
#print axioms windowFirstExp_eq_of_discrepancy_emod_eq
#print axioms windowFirstCos_eq_of_discrepancy_emod_eq
#print axioms tailOrbitFirstExp_eq_window_mul_remainder
#print axioms norm_windowFirstExp_sub_tailOrbitFirstExp_lt
#print axioms windowFirstCos_le_nine_tenths_of_tailOrbitGap
#print axioms firstHarmonicAnchorDefect_ge_iff_first_harmonic_gap
#print axioms exists_large_real_pair_energy_with_zero_first_harmonic_chord
#print axioms sum_pairwise_norm_sq_eq_two_card_mul_centered
#print axioms card_mul_sq_le_sum_pairwise_norm_sq_of_separatedPairs
#print axioms card_div_five_le_sum_anchor_norm_sq_of_pairwise
#print axioms pivotReconstructionError_eq_conj_phase_mul_window_sub_one
#print axioms pivotFiberReconstructionErrorSum_eq_twoMode
#print axioms pivotFiberReconstructionVariance_eq_pairwise
#print axioms pivotFiberReconstructionVariance_ge_one_fifth_of_pairwise
#print axioms pivotFiberReconstructionDefect_eq_sum_residual_norm_sq
#print axioms pivotFiberReconstructionDefect_eq_variance_add_bias
#print axioms pivotFiberReconstructionVariance_eq_twoMode_div_card
#print axioms pivotFiberReconstructionVariance_ge_six_div_twentyfive_of_modeBounds
#print axioms exists_certifiedKill_of_pivotFiberReconstructionVariance
#print axioms exists_certifiedKill_of_pivotFiberPairwiseEnergy
#print axioms exists_certifiedKill_of_pivotFiberSeparatedPairs
#print axioms exists_certifiedKill_of_pivotFiberWindowPairwiseEnergy
#print axioms exists_certifiedKill_of_pivotFiberWindowSeparatedPairs
#print axioms exists_certifiedKill_of_pivotFiberReconstructionDefect
#print axioms naturalPivotWindowGap_of_naturalPivotTwoModeCancellation
#print axioms pivotAntiReconstruction_of_naturalPivotWindowGap
#print axioms naturalPivotPointEscape_of_naturalPrimeTailOrbitGap
#print axioms pivotAntiReconstruction_of_reconstructionVariance
#print axioms pivotReconstructionVariance_of_naturalPivotTwoModeCancellation
#print axioms irrational_totient_series_of_pivotAntiReconstruction
#print axioms irrational_totient_series_of_naturalPivotWindowGap
#print axioms irrational_totient_series_of_naturalPivotPointEscape
#print axioms irrational_totient_series_of_naturalPrimeTailOrbitGap
#print axioms irrational_totient_series_of_pivotReconstructionVariance
#print axioms irrational_totient_series_of_pivotPairwiseReconstructionEnergy
#print axioms irrational_totient_series_of_pivotSeparatedPairs
#print axioms irrational_totient_series_of_pivotWindowPairwiseEnergy
#print axioms irrational_totient_series_of_pivotWindowSeparatedPairs
#print axioms irrational_totient_series_of_windowSeparatedPairs
#print axioms cofinally_adjacent_chord_ge_one_of_unit_squaring
#print axioms cofinally_scaledTotientSeriesFirstExp_adjacent_chord_ge_one
#print axioms windowSeparatedPairs_of_irrational_totient_series
#print axioms dtwWindowSeparatedPairs_iff_irrational_totient_series
#print axioms irrational_totient_series_of_naturalPivotTwoModeCancellation

end
end TotientTailPeriodKiller
end Erdos257PeriodNoncollapse
