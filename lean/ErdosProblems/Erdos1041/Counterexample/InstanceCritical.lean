import ErdosProblems.Erdos1041.Counterexample.Defs
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Real.Pi.Bounds

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Formalisation of the concrete critical configuration of `ani_degree7_counterexample.tex`
at `s = 10^-6`. -/

/-
Slice S4.  Helper development lives in `Erdos1041.Counterexample.S4Proofs`; the
obligations are re-exported at the interface names
`Erdos1041.Counterexample.s4_f_monic_degree`, `s4_roots_on_circle`,
`s4_roots_nodup` at the end of the file.

The root argument follows a Cayley-transform route.  With
`chi x = (1 + i x)/(1 - i x)` one has the
exact Gaussian-rational identity `(1 - i x)^7 F(chi x) = 2 i H(x)` for an
explicit degree-seven *real* polynomial `H`, and seven exact rational sign
changes of `H` produce seven distinct roots of `F` of modulus exactly one.
-/

noncomputable section
open scoped ComplexConjugate NNReal
namespace Erdos1041.Counterexample

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## §A  Trigonometric anchors for the seventh roots of unity

Public, because slices S5 and S7 need the same enclosures.  Everything is
derived from one Chebyshev relation, `8c³ + 4c² − 4c − 1 = 0` for
`c = cos(2π/7)`, together with `Real.pi_gt_d6` / `Real.pi_lt_d6`.  This is the
only place in slice S4 where `Real.pi` enters; every other estimate is exact
rational arithmetic. -/

theorem two_pi_div_seven_lb : (8975977 / 10 ^ 7 : ℝ) < 2 * Real.pi / 7 := by
  have h := Real.pi_gt_d6
  norm_num at h ⊢
  linarith

theorem two_pi_div_seven_ub : 2 * Real.pi / 7 < (8975980 / 10 ^ 7 : ℝ) := by
  have h := Real.pi_lt_d6
  norm_num at h ⊢
  linarith

theorem two_pi_div_seven_pos : 0 < 2 * Real.pi / 7 := by
  have := two_pi_div_seven_lb; linarith

theorem two_pi_div_seven_lt_pi : 2 * Real.pi / 7 < Real.pi := by
  have := Real.pi_pos; linarith

/-- A crude enclosure of `cos(2π/7)`, wide but enough to isolate the relevant
root of the Chebyshev cubic. -/
theorem cos_two_pi_div_seven_crude :
    (5630 / 10000 : ℝ) < Real.cos (2 * Real.pi / 7) ∧
      Real.cos (2 * Real.pi / 7) < (6312 / 10000 : ℝ) := by
  have hlb := two_pi_div_seven_lb
  have hub := two_pi_div_seven_ub
  have hpos := two_pi_div_seven_pos
  have habs : |2 * Real.pi / 7| ≤ 1 := by
    rw [abs_of_pos hpos]; linarith
  have hb := Real.cos_bound habs
  rw [abs_of_pos hpos] at hb
  rw [abs_le] at hb
  have h2u : (2 * Real.pi / 7) ^ 2 < 8056822 / 10 ^ 7 := by nlinarith
  have h2l : (8056816 / 10 ^ 7 : ℝ) < (2 * Real.pi / 7) ^ 2 := by nlinarith
  have h4u : (2 * Real.pi / 7) ^ 4 < 6492000 / 10 ^ 7 := by nlinarith
  constructor
  · nlinarith [hb.1]
  · nlinarith [hb.2]

/-- The Chebyshev relation: `cos(4θ) = cos(3θ)` at `θ = 2π/7` because
`4θ = 2π − 3θ`. -/
theorem cos_two_pi_div_seven_cubic :
    8 * Real.cos (2 * Real.pi / 7) ^ 3 + 4 * Real.cos (2 * Real.pi / 7) ^ 2
      - 4 * Real.cos (2 * Real.pi / 7) - 1 = 0 := by
  have hsym : Real.cos (4 * (2 * Real.pi / 7)) = Real.cos (3 * (2 * Real.pi / 7)) := by
    have he : (4 : ℝ) * (2 * Real.pi / 7) = 2 * Real.pi - 3 * (2 * Real.pi / 7) := by ring
    rw [he, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
    ring
  have h3 := Real.cos_three_mul (2 * Real.pi / 7)
  have h4 : Real.cos (4 * (2 * Real.pi / 7))
      = 8 * Real.cos (2 * Real.pi / 7) ^ 4 - 8 * Real.cos (2 * Real.pi / 7) ^ 2 + 1 := by
    have e : (4 : ℝ) * (2 * Real.pi / 7) = 2 * (2 * (2 * Real.pi / 7)) := by ring
    rw [e, Real.cos_two_mul, Real.cos_two_mul]
    ring
  rw [h4, h3] at hsym
  have hkey : (Real.cos (2 * Real.pi / 7) - 1) *
      (8 * Real.cos (2 * Real.pi / 7) ^ 3 + 4 * Real.cos (2 * Real.pi / 7) ^ 2
        - 4 * Real.cos (2 * Real.pi / 7) - 1) = 0 := by
    linear_combination hsym
  have hne : Real.cos (2 * Real.pi / 7) - 1 ≠ 0 := by
    have h := cos_two_pi_div_seven_crude.2
    intro hz
    rw [sub_eq_zero] at hz
    rw [hz] at h
    norm_num at h
  exact (mul_eq_zero.mp hkey).resolve_left hne

/-- `cos(2π/7) ∈ (0.6234, 0.6236)`. -/
theorem cos_two_pi_div_seven_bounds :
    (6234 / 10000 : ℝ) < Real.cos (2 * Real.pi / 7) ∧
      Real.cos (2 * Real.pi / 7) < (6236 / 10000 : ℝ) := by
  obtain ⟨h1, h2⟩ := cos_two_pi_div_seven_crude
  have hg := cos_two_pi_div_seven_cubic
  have hq : ∀ a : ℝ, 56 / 100 ≤ a → a ≤ 64 / 100 →
      0 < 8 * (Real.cos (2 * Real.pi / 7) ^ 2 + Real.cos (2 * Real.pi / 7) * a + a ^ 2)
        + 4 * (Real.cos (2 * Real.pi / 7) + a) - 4 := by
    intro a ha1 ha2
    nlinarith [h1, h2, ha1, ha2,
      mul_pos (show (0:ℝ) < Real.cos (2 * Real.pi / 7) by linarith)
        (show (0:ℝ) < a by linarith)]
  constructor
  · by_contra hcon
    push_neg at hcon
    have hq' := hq (6234 / 10000) (by norm_num) (by norm_num)
    have hid : (0 : ℝ) - (8 * (6234 / 10000 : ℝ) ^ 3 + 4 * (6234 / 10000 : ℝ) ^ 2
          - 4 * (6234 / 10000 : ℝ) - 1)
        = (Real.cos (2 * Real.pi / 7) - 6234 / 10000) *
          (8 * (Real.cos (2 * Real.pi / 7) ^ 2
              + Real.cos (2 * Real.pi / 7) * (6234 / 10000) + (6234 / 10000 : ℝ) ^ 2)
            + 4 * (Real.cos (2 * Real.pi / 7) + 6234 / 10000) - 4) := by
      linear_combination (-1 : ℝ) * hg
    nlinarith [hid, hq', hcon]
  · by_contra hcon
    push_neg at hcon
    have hq' := hq (6236 / 10000) (by norm_num) (by norm_num)
    have hid : (0 : ℝ) - (8 * (6236 / 10000 : ℝ) ^ 3 + 4 * (6236 / 10000 : ℝ) ^ 2
          - 4 * (6236 / 10000 : ℝ) - 1)
        = (Real.cos (2 * Real.pi / 7) - 6236 / 10000) *
          (8 * (Real.cos (2 * Real.pi / 7) ^ 2
              + Real.cos (2 * Real.pi / 7) * (6236 / 10000) + (6236 / 10000 : ℝ) ^ 2)
            + 4 * (Real.cos (2 * Real.pi / 7) + 6236 / 10000) - 4) := by
      linear_combination (-1 : ℝ) * hg
    nlinarith [hid, hq', hcon]

/-- `sin(2π/7) ∈ (0.7817, 0.7820)`. -/
theorem sin_two_pi_div_seven_bounds :
    (7817 / 10000 : ℝ) < Real.sin (2 * Real.pi / 7) ∧
      Real.sin (2 * Real.pi / 7) < (7820 / 10000 : ℝ) := by
  obtain ⟨hc1, hc2⟩ := cos_two_pi_div_seven_bounds
  have hsq : Real.sin (2 * Real.pi / 7) ^ 2 = 1 - Real.cos (2 * Real.pi / 7) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (2 * Real.pi / 7)
    linarith
  have hpos : 0 < Real.sin (2 * Real.pi / 7) :=
    Real.sin_pos_of_pos_of_lt_pi two_pi_div_seven_pos two_pi_div_seven_lt_pi
  constructor <;> nlinarith [hsq, hpos, hc1, hc2]

/-! ### The seventh roots of unity as powers of `u 1` -/

theorem u_succ (j : ℕ) : u (j + 1) = u 1 * u j := by
  unfold u
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem u_zero : u 0 = 1 := by
  unfold u
  norm_num

theorem u_seven : u 7 = 1 := by
  unfold u
  have h : (2 * (Real.pi : ℂ) * ((7 : ℕ) : ℂ) * Complex.I / 7)
      = 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_two_pi_mul_I]

theorem u_one_eq : u 1
    = ((Real.cos (2 * Real.pi / 7) : ℝ) : ℂ)
      + ((Real.sin (2 * Real.pi / 7) : ℝ) : ℂ) * Complex.I := by
  unfold u
  have h : (2 * (Real.pi : ℂ) * ((1 : ℕ) : ℂ) * Complex.I / 7)
      = (((2 * Real.pi / 7 : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem u_one_re : (u 1).re = Real.cos (2 * Real.pi / 7) := by
  rw [u_one_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem u_one_im : (u 1).im = Real.sin (2 * Real.pi / 7) := by
  rw [u_one_eq]
  simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem u_step_re (j : ℕ) :
    (u (j + 1)).re = (u 1).re * (u j).re - (u 1).im * (u j).im := by
  rw [u_succ]; exact Complex.mul_re _ _

theorem u_step_im (j : ℕ) :
    (u (j + 1)).im = (u 1).re * (u j).im + (u 1).im * (u j).re := by
  rw [u_succ]; exact Complex.mul_im _ _

/-! ### Rational enclosures of `Re u j`, `Im u j` for `j = 0,…,6`

Obtained by six steps of interval multiplication from `u 1`; the widest box is
`j = 6`, at `6·10⁻³`.  Every row is verified against
`INSTANCE_CERTIFICATES.md` §1. -/

theorem u_bounds_0 :
    ((1 : ℝ) ≤ (u 0).re ∧ (u 0).re ≤ 1) ∧ ((0 : ℝ) ≤ (u 0).im ∧ (u 0).im ≤ 0) := by
  rw [u_zero]; norm_num

theorem u_bounds_1 :
    ((6234 / 10000 : ℝ) ≤ (u 1).re ∧ (u 1).re ≤ 6236 / 10000) ∧
      ((7817 / 10000 : ℝ) ≤ (u 1).im ∧ (u 1).im ≤ 7820 / 10000) := by
  rw [u_one_re, u_one_im]
  obtain ⟨c1, c2⟩ := cos_two_pi_div_seven_bounds
  obtain ⟨s1, s2⟩ := sin_two_pi_div_seven_bounds
  exact ⟨⟨c1.le, c2.le⟩, ⟨s1.le, s2.le⟩⟩

theorem u_bounds_2 :
    ((-2229 / 10000 : ℝ) ≤ (u 2).re ∧ (u 2).re ≤ -2221 / 10000) ∧
      ((9746 / 10000 : ℝ) ≤ (u 2).im ∧ (u 2).im ≤ 9754 / 10000) := by
  have hre : (u 2).re = (u 1).re * (u 1).re - (u 1).im * (u 1).im := u_step_re 1
  have him : (u 2).im = (u 1).re * (u 1).im + (u 1).im * (u 1).re := u_step_im 1
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_1
  rw [hre, him]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [a1, a2, b1, b2]

theorem u_bounds_3 :
    ((-9018 / 10000 : ℝ) ≤ (u 3).re ∧ (u 3).re ≤ -9003 / 10000) ∧
      ((4332 / 10000 : ℝ) ≤ (u 3).im ∧ (u 3).im ≤ 4347 / 10000) := by
  have hre : (u 3).re = (u 1).re * (u 2).re - (u 1).im * (u 2).im := u_step_re 2
  have him : (u 3).im = (u 1).re * (u 2).im + (u 1).im * (u 2).re := u_step_im 2
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_1
  obtain ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ := u_bounds_2
  rw [hre, him]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [a1, a2, b1, b2, c1, c2, d1, d2]

theorem u_bounds_4 :
    ((-9023 / 10000 : ℝ) ≤ (u 4).re ∧ (u 4).re ≤ -8998 / 10000) ∧
      ((-4352 / 10000 : ℝ) ≤ (u 4).im ∧ (u 4).im ≤ -4326 / 10000) := by
  have hre : (u 4).re = (u 1).re * (u 3).re - (u 1).im * (u 3).im := u_step_re 3
  have him : (u 4).im = (u 1).re * (u 3).im + (u 1).im * (u 3).re := u_step_im 3
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_1
  obtain ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ := u_bounds_3
  rw [hre, him]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [a1, a2, b1, b2, c1, c2, d1, d2]

theorem u_bounds_5 :
    ((-2246 / 10000 : ℝ) ≤ (u 5).re ∧ (u 5).re ≤ -2206 / 10000) ∧
      ((-9770 / 10000 : ℝ) ≤ (u 5).im ∧ (u 5).im ≤ -9730 / 10000) := by
  have hre : (u 5).re = (u 1).re * (u 4).re - (u 1).im * (u 4).im := u_step_re 4
  have him : (u 5).im = (u 1).re * (u 4).im + (u 1).im * (u 4).re := u_step_im 4
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_1
  obtain ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ := u_bounds_4
  rw [hre, him]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [a1, a2, b1, b2, c1, c2, d1, d2]

theorem u_bounds_6 :
    ((6205 / 10000 : ℝ) ≤ (u 6).re ∧ (u 6).re ≤ 6265 / 10000) ∧
      ((-7849 / 10000 : ℝ) ≤ (u 6).im ∧ (u 6).im ≤ -7790 / 10000) := by
  have hre : (u 6).re = (u 1).re * (u 5).re - (u 1).im * (u 5).im := u_step_re 5
  have him : (u 6).im = (u 1).re * (u 5).im + (u 1).im * (u 5).re := u_step_im 5
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_1
  obtain ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ := u_bounds_5
  rw [hre, him]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [a1, a2, b1, b2, c1, c2, d1, d2]

/-! ### The two anchors named in the interface statement -/

theorem exp_six_pi_div_seven : Complex.exp (6 * Real.pi * Complex.I / 7) = u 3 := by
  unfold u
  congr 1
  push_cast
  ring

theorem exp_neg_two_pi_div_seven : Complex.exp (-2 * Real.pi * Complex.I / 7) = u 6 := by
  unfold u
  have e : (2 * (Real.pi : ℂ) * ((6 : ℕ) : ℂ) * Complex.I / 7)
      = -2 * (Real.pi : ℂ) * Complex.I / 7 + 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-! ### Separation of the seven anchors

`‖u i - u j‖ ≥ 2 sin(π/7) > 0.867` for `i ≠ j`; only the crude bound `1/5` is
needed, and only against `u 3` and `u 6`. -/

theorem norm_sub_ge_of_box {z w : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (h : d ^ 2 ≤ (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) : d ≤ ‖z - w‖ := by
  have hn : ‖z - w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  nlinarith [hn, h, norm_nonneg (z - w), hd]

theorem u_sep_three (k : ℕ) (hk : k < 7) (hne : k ≠ 3) : (1 / 5 : ℝ) ≤ ‖u k - u 3‖ := by
  obtain ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ := u_bounds_3
  interval_cases k
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_0; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_1; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_2; nlinarith)
  · exact absurd rfl hne
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_4; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_5; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_6; nlinarith)

theorem u_sep_six (k : ℕ) (hk : k < 7) (hne : k ≠ 6) : (1 / 5 : ℝ) ≤ ‖u k - u 6‖ := by
  obtain ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ := u_bounds_6
  interval_cases k
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_0; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_1; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_2; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_3; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_4; nlinarith)
  · exact norm_sub_ge_of_box (by norm_num)
      (by obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := u_bounds_5; nlinarith)
  · exact absurd rfl hne

namespace S4Proofs

/-! ## Basic facts about the constants -/

theorem rho_pos : 0 < (ρ : ℝ) := by
  norm_num [ρ, s]

theorem rho_lt_one : (ρ : ℝ) < 1 := by
  norm_num [ρ, s]

theorem rho_ne_zero : (ρ : ℂ) ≠ 0 := by
  norm_num [ρ, s]

theorem eps_pos : 0 < (ε : ℝ) := by
  norm_num [ε, s]

theorem eps_ne_zero : (ε : ℂ) ≠ 0 := by
  norm_num [ε, s]

/-! ## The first obligation: `f` is monic of degree seven -/

theorem s4_f_monic_degree' : f.Monic ∧ f.natDegree = 7 := by
  constructor
  · unfold f
    monicity!
  · unfold f
    compute_degree!

/-! ## Exact scaling identities -/

/-- Exact rescaling, without introducing a reciprocal polynomial. -/
theorem f_eval_scale (z : ℂ) :
    f.eval ((ρ : ℂ) * z) = (ρ : ℂ) ^ 7 * F.eval z := by
  simp only [f, F, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- `F` written out in the paper's form (paper (1.3)). -/
theorem F_eval (z : ℂ) :
    F.eval z = z ^ 7 - 1
      + (ε : ℂ) ^ 4 * (a * z ^ 3 - conj a * z ^ 4)
      + (ε : ℂ) ^ 5 * (b * z ^ 2 - conj b * z ^ 5)
      + (ε : ℂ) ^ 6 * (c * z - conj c * z ^ 6) := by
  simp only [F, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem conj_a : conj a = (A : ℂ) + (s : ℂ) * Complex.I := by
  simp only [a, map_sub, map_mul, map_ratCast, Complex.conj_I]
  ring

theorem conj_b : conj b = -(Complex.I * (B : ℂ)) + ((9 / 5 : ℚ) : ℂ) * (s : ℂ) := by
  simp only [b, map_add, map_mul, map_ratCast, Complex.conj_I]
  ring

theorem conj_c : conj c = -(Cconst : ℂ) + ((162 / 25 : ℚ) : ℂ) * (s : ℂ) * Complex.I := by
  simp only [c, map_sub, map_neg, map_mul, map_ratCast, Complex.conj_I]
  ring

/-- Explicit evaluation of the scaled model; no numerical approximation. -/
theorem Q_eval_expanded (w : ℂ) :
    Q.eval w = w ^ 7 + a * w ^ 3 + b * w ^ 2 + c * w
      - (s : ℂ) ^ 2 * conj a * w ^ 4
      - (s : ℂ) ^ 6 * conj b * w ^ 5
      - (s : ℂ) ^ 10 * conj c * w ^ 6 := by
  simp only [Q, P, G, E, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, a, b, c]
  push_cast
  ring

/-- The first exact scaling identity, paper (4.4). -/
theorem F_eval_eps (w : ℂ) :
    F.eval ((ε : ℂ) * w) = -1 + (ε : ℂ) ^ 7 * Q.eval w := by
  rw [Q_eval_expanded, F_eval]
  simp only [ε]
  push_cast
  ring

/-- Physical evaluation expressed entirely through the scaled model. -/
theorem f_eval_rho_eps (w : ℂ) :
    f.eval ((ρ : ℂ) * (ε : ℂ) * w) =
      (ρ : ℂ) ^ 7 * (-1 + (ε : ℂ) ^ 7 * Q.eval w) := by
  rw [mul_assoc, f_eval_scale, F_eval_eps]

/-! ## A Cayley-transform replacement for the nested root disks

Write `chi x = (1 + i x)/(1 - i x)`.  The real polynomial `H` below satisfies
`(1 - i x)^7 F(chi x) = 2 i H(x)`.  Seven rational sign changes give seven
distinct unit-modulus roots directly.  This avoids a root-counting contour
theorem and avoids approximate-to-exact reflection arguments.
-/

def cayley (x : ℝ) : ℂ :=
  (1 + (x : ℂ) * Complex.I) / (1 - (x : ℂ) * Complex.I)

def cayleyH (x : ℝ) : ℝ :=
    7 * x - 35 * x ^ 3 + 21 * x ^ 5 - x ^ 7
      - (ε : ℝ) ^ 4 * (1 + x ^ 2) ^ 3 * ((s : ℝ) + (A : ℝ) * x)
      + (ε : ℝ) ^ 5 * (1 + x ^ 2) ^ 2 *
          ((B : ℝ) * (1 - 3 * x ^ 2) + (9 / 5 : ℝ) * (s : ℝ) * (x ^ 3 - 3 * x))
      + (ε : ℝ) ^ 6 * (1 + x ^ 2) *
          ((Cconst : ℝ) * (5 * x - 10 * x ^ 3 + x ^ 5)
            - (162 / 25 : ℝ) * (s : ℝ) * (1 - 10 * x ^ 2 + 5 * x ^ 4))

def bracketLo : Fin 7 → ℝ :=
  ![-1 / 10000, 4815 / 10000, 12539 / 10000, 43812 / 10000,
    -43813 / 10000, -12540 / 10000, -4816 / 10000]

def bracketHi : Fin 7 → ℝ :=
  ![1 / 10000, 4816 / 10000, 12540 / 10000, 43813 / 10000,
    -43812 / 10000, -12539 / 10000, -4815 / 10000]

theorem cayley_den_ne_zero (x : ℝ) : (1 - (x : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

theorem cayley_norm (x : ℝ) : ‖cayley x‖ = 1 := by
  have heq : ‖1 + (x : ℂ) * Complex.I‖ = ‖1 - (x : ℂ) * Complex.I‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
  unfold cayley
  rw [norm_div, heq, div_self (norm_ne_zero_iff.mpr (cayley_den_ne_zero x))]

theorem cayley_injective : Function.Injective cayley := by
  intro x y h
  have hc := (div_eq_div_iff (cayley_den_ne_zero x) (cayley_den_ne_zero y)).mp h
  have hi := congrArg Complex.im hc
  norm_num at hi
  linarith

/-- The exact Gaussian-rational identity behind the whole root argument.
Proved by clearing the nonvanishing Cayley denominator; no approximation. -/
theorem cayley_identity (x : ℝ) :
    (1 - (x : ℂ) * Complex.I) ^ 7 * F.eval (cayley x) =
      2 * Complex.I * (cayleyH x : ℂ) := by
  have hden := cayley_den_ne_zero x
  rw [F_eval, conj_a, conj_b, conj_c]
  unfold cayley cayleyH a b c
  push_cast
  field_simp
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, pow_succ] <;> ring

theorem cayleyH_continuous : Continuous cayleyH := by
  unfold cayleyH
  fun_prop

/-- Seven exact sign changes, not floating-point approximations. -/
theorem cayley_signs (j : Fin 7) :
    bracketLo j < bracketHi j ∧
      ((cayleyH (bracketLo j) < 0 ∧ 0 < cayleyH (bracketHi j)) ∨
       (cayleyH (bracketHi j) < 0 ∧ 0 < cayleyH (bracketLo j))) := by
  fin_cases j <;>
    norm_num [bracketLo, bracketHi, cayleyH, ε, s, A, B, Cconst, t]

theorem exists_cayley_root (j : Fin 7) :
    ∃ x : ℝ, x ∈ Set.Ioo (bracketLo j) (bracketHi j) ∧ cayleyH x = 0 := by
  rcases cayley_signs j with ⟨hab, hs⟩
  rcases hs with hs | hs
  · exact intermediate_value_Ioo hab.le cayleyH_continuous.continuousOn hs
  · exact intermediate_value_Ioo' hab.le cayleyH_continuous.continuousOn hs

def realRoot (j : Fin 7) : ℝ := Classical.choose (exists_cayley_root j)

theorem realRoot_mem (j : Fin 7) :
    realRoot j ∈ Set.Ioo (bracketLo j) (bracketHi j) :=
  (Classical.choose_spec (exists_cayley_root j)).1

theorem realRoot_zero (j : Fin 7) : cayleyH (realRoot j) = 0 :=
  (Classical.choose_spec (exists_cayley_root j)).2

theorem realRoot_injective : Function.Injective realRoot := by
  intro i j hij
  by_contra hne
  have hi := realRoot_mem i
  have hj := realRoot_mem j
  fin_cases i <;> fin_cases j <;>
    norm_num [Set.mem_Ioo, bracketLo, bracketHi] at * <;> linarith

/-- The seven physical roots constructed from the seven real brackets. -/
def physicalRoot (j : Fin 7) : ℂ := (ρ : ℂ) * cayley (realRoot j)

theorem cayley_realRoot_isRoot (j : Fin 7) : F.IsRoot (cayley (realRoot j)) := by
  have h := cayley_identity (realRoot j)
  rw [realRoot_zero] at h
  simp only [Complex.ofReal_zero, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (cayley_den_ne_zero _))

theorem physicalRoot_isRoot (j : Fin 7) : f.IsRoot (physicalRoot j) := by
  have h : f.eval ((ρ : ℂ) * cayley (realRoot j)) = 0 := by
    rw [f_eval_scale, cayley_realRoot_isRoot, mul_zero]
  exact h

theorem physicalRoot_norm (j : Fin 7) : ‖physicalRoot j‖ = (ρ : ℝ) := by
  simp [physicalRoot, cayley_norm, Complex.norm_ratCast, abs_of_pos rho_pos]

theorem physicalRoot_injective : Function.Injective physicalRoot := by
  intro i j h
  apply realRoot_injective
  apply cayley_injective
  exact mul_left_cancel₀ rho_ne_zero h

/-- The seven roots as a multiset (no `DecidableEq ℂ` needed). -/
def rootMul : Multiset ℂ := Multiset.map physicalRoot Finset.univ.val

theorem rootMul_nodup : rootMul.Nodup :=
  Multiset.Nodup.map physicalRoot_injective Finset.univ.nodup

theorem rootMul_card : Multiset.card rootMul = 7 := by
  simp [rootMul]

theorem f_ne_zero : f ≠ 0 := s4_f_monic_degree'.1.ne_zero

/-- All multiplicities are exhausted by the seven distinct constructed roots. -/
theorem f_roots_eq : f.roots = rootMul := by
  have hsub : rootMul ⊆ f.roots := by
    intro z hz
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hz
    exact (Polynomial.mem_roots f_ne_zero).mpr (physicalRoot_isRoot j)
  have hle : rootMul ≤ f.roots := (Multiset.le_iff_subset rootMul_nodup).mpr hsub
  obtain ⟨m, hm⟩ := Multiset.le_iff_exists_add.mp hle
  have hdeg := Polynomial.card_roots' f
  rw [s4_f_monic_degree'.2, hm, Multiset.card_add, rootMul_card] at hdeg
  have hm0 : Multiset.card m = 0 := by omega
  have hmz : m = 0 := Multiset.card_eq_zero.mp hm0
  rw [hm, hmz, add_zero]

/-- The second obligation. -/
theorem s4_roots_on_circle' : ∀ z, f.IsRoot z → ‖z‖ = (ρ : ℝ) := by
  intro z hz
  have hm : z ∈ rootMul := by
    rw [← f_roots_eq]
    exact (Polynomial.mem_roots f_ne_zero).mpr hz
  obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hm
  exact physicalRoot_norm j

/-- The third obligation. -/
theorem s4_roots_nodup' : f.roots.Nodup := by
  rw [f_roots_eq]
  exact rootMul_nodup

/-- A directly usable adjacent consequence: the roots are strictly inside the
unit disk. -/
theorem roots_strictly_inside : ∀ z, f.IsRoot z → ‖z‖ < 1 := by
  intro z hz
  rw [s4_roots_on_circle' z hz]
  exact rho_lt_one

/-- Every root of `f` is one of the seven constructed ones. -/
theorem exists_index_of_isRoot {z : ℂ} (hz : f.IsRoot z) : ∃ j : Fin 7, z = physicalRoot j := by
  have hm : z ∈ rootMul := by
    rw [← f_roots_eq]
    exact (Polynomial.mem_roots f_ne_zero).mpr hz
  obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
  exact ⟨j, hj.symm⟩

/-! ## The constructed roots sit next to the seventh roots of unity

`cayley x - w = ((1 + ix) - w(1 - ix)) / (1 - ix)`, so the whole estimate is a
rational computation in `x`, `Re w`, `Im w` with no division and no
trigonometry beyond the anchor enclosures of §A.  The uniform deviation budget
`1/100` covers every one of the seven cases (worst case `8·10⁻³`, at `j = 4`). -/

theorem norm_cayley_sub_lt {x : ℝ} {w : ℂ}
    (hA : |1 - w.re - w.im * x| ≤ 1 / 100)
    (hB : |x + w.re * x - w.im| ≤ 1 / 100) :
    ‖cayley x - w‖ < 1 / 10 := by
  have hden := cayley_den_ne_zero x
  have hrw : cayley x - w
      = ((1 + (x : ℂ) * Complex.I) - w * (1 - (x : ℂ) * Complex.I))
        / (1 - (x : ℂ) * Complex.I) := by
    rw [cayley]; field_simp
  have hd2 : ‖(1 : ℂ) - (x : ℂ) * Complex.I‖ ^ 2 = 1 + x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hn2 : ‖(1 + (x : ℂ) * Complex.I) - w * (1 - (x : ℂ) * Complex.I)‖ ^ 2
      = (1 - w.re - w.im * x) ^ 2 + (x + w.re * x - w.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hdpos : 0 < ‖(1 : ℂ) - (x : ℂ) * Complex.I‖ := norm_pos_iff.mpr hden
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  have hAsq : (1 - w.re - w.im * x) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    nlinarith [hA'.1, hA'.2]
  have hBsq : (x + w.re * x - w.im) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    nlinarith [hB'.1, hB'.2]
  rw [hrw, norm_div, div_lt_iff₀ hdpos]
  nlinarith [hn2, hd2, hAsq, hBsq, hdpos, sq_nonneg x,
    norm_nonneg ((1 + (x : ℂ) * Complex.I) - w * (1 - (x : ℂ) * Complex.I))]

theorem cayley_near_u_0 : ‖cayley (realRoot 0) - u 0‖ < 1 / 10 := by
  have hx1 : (-1 / 10000 : ℝ) < realRoot 0 := (realRoot_mem 0).1
  have hx2 : realRoot 0 < (1 / 10000 : ℝ) := (realRoot_mem 0).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_0
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)

theorem cayley_near_u_1 : ‖cayley (realRoot 1) - u 1‖ < 1 / 10 := by
  have hx1 : (4815 / 10000 : ℝ) < realRoot 1 := (realRoot_mem 1).1
  have hx2 : realRoot 1 < (4816 / 10000 : ℝ) := (realRoot_mem 1).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_1
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)

theorem cayley_near_u_2 : ‖cayley (realRoot 2) - u 2‖ < 1 / 10 := by
  have hx1 : (12539 / 10000 : ℝ) < realRoot 2 := (realRoot_mem 2).1
  have hx2 : realRoot 2 < (12540 / 10000 : ℝ) := (realRoot_mem 2).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_2
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)

theorem cayley_near_u_3 : ‖cayley (realRoot 3) - u 3‖ < 1 / 10 := by
  have hx1 : (43812 / 10000 : ℝ) < realRoot 3 := (realRoot_mem 3).1
  have hx2 : realRoot 3 < (43813 / 10000 : ℝ) := (realRoot_mem 3).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_3
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)

theorem cayley_near_u_4 : ‖cayley (realRoot 4) - u 4‖ < 1 / 10 := by
  have hx1 : (-43813 / 10000 : ℝ) < realRoot 4 := (realRoot_mem 4).1
  have hx2 : realRoot 4 < (-43812 / 10000 : ℝ) := (realRoot_mem 4).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_4
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)

theorem cayley_near_u_5 : ‖cayley (realRoot 5) - u 5‖ < 1 / 10 := by
  have hx1 : (-12540 / 10000 : ℝ) < realRoot 5 := (realRoot_mem 5).1
  have hx2 : realRoot 5 < (-12539 / 10000 : ℝ) := (realRoot_mem 5).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_5
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)

theorem cayley_near_u_6 : ‖cayley (realRoot 6) - u 6‖ < 1 / 10 := by
  have hx1 : (-4816 / 10000 : ℝ) < realRoot 6 := (realRoot_mem 6).1
  have hx2 : realRoot 6 < (-4815 / 10000 : ℝ) := (realRoot_mem 6).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_6
  exact norm_cayley_sub_lt (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)

theorem cayley_near_u (j : Fin 7) : ‖cayley (realRoot j) - u (j : ℕ)‖ < 1 / 10 := by
  fin_cases j
  · exact cayley_near_u_0
  · exact cayley_near_u_1
  · exact cayley_near_u_2
  · exact cayley_near_u_3
  · exact cayley_near_u_4
  · exact cayley_near_u_5
  · exact cayley_near_u_6

/-- Each constructed root of `f` lies within `ρ/10` of `ρ u_j`. -/
theorem physicalRoot_near (j : Fin 7) :
    ‖physicalRoot j - (ρ : ℂ) * u (j : ℕ)‖ < (ρ : ℝ) / 10 := by
  have h : physicalRoot j - (ρ : ℂ) * u (j : ℕ)
      = (ρ : ℂ) * (cayley (realRoot j) - u (j : ℕ)) := by
    unfold physicalRoot; ring
  rw [h, norm_mul, Complex.norm_ratCast, abs_of_pos rho_pos]
  nlinarith [rho_pos, cayley_near_u j, norm_nonneg (cayley (realRoot j) - u (j : ℕ))]

/-! ## The `shiftQuad` bridge

`shiftQuad p cc` is defined by division by the monic `X ^ 2`.  At a critical
point the constant and linear coefficients of `p.comp (X + C cc) - C (p.eval cc)`
both vanish, so the division is exact and the defining identity holds. -/

theorem shiftQuad_spec (p : Polynomial ℂ) (cc : ℂ)
    (hcc : (Polynomial.derivative p).eval cc = 0) (z : ℂ) :
    (shiftQuad p cc).eval z * z ^ 2 = p.eval (cc + z) - p.eval cc := by
  set g : Polynomial ℂ := p.comp (Polynomial.X + Polynomial.C cc) - Polynomial.C (p.eval cc)
    with hg
  have hgeval : ∀ y : ℂ, g.eval y = p.eval (cc + y) - p.eval cc := by
    intro y
    simp [hg, Polynomial.eval_comp, add_comm]
  have hc0 : g.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hgeval]
    simp
  have hderiv : Polynomial.derivative g
      = (Polynomial.derivative p).comp (Polynomial.X + Polynomial.C cc) := by
    simp [hg, Polynomial.derivative_comp]
  have hc1 : g.coeff 1 = 0 := by
    have h0 : (Polynomial.derivative g).coeff 0 = g.coeff 1 := by
      simp [Polynomial.coeff_derivative]
    have h1 : (Polynomial.derivative g).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, hderiv]
      simp [Polynomial.eval_comp, hcc]
    rw [← h0, h1]
  have hdvd : (Polynomial.X ^ 2 : Polynomial ℂ) ∣ g := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · exact hc0
    · exact hc1
  have hmonic : (Polynomial.X ^ 2 : Polynomial ℂ).Monic := Polynomial.monic_X_pow 2
  have hmod : g %ₘ (Polynomial.X ^ 2) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
  have hmul : (Polynomial.X ^ 2 : Polynomial ℂ) * (g /ₘ (Polynomial.X ^ 2)) = g := by
    have h := Polynomial.modByMonic_add_div g (Polynomial.X ^ 2 : Polynomial ℂ)
    rw [hmod, zero_add] at h
    exact h
  have : (shiftQuad p cc) = g /ₘ (Polynomial.X ^ 2) := rfl
  rw [this]
  have := congrArg (fun q : Polynomial ℂ => q.eval z) hmul
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at this
  rw [hgeval] at this
  linear_combination this

/-! ## Transport of the critical points from `Q` to `f`

`f'(ρεw) = ρ⁶ε⁶ Q'(w)` (paper (4.4)), so `w ↦ ρεw` is a bijection carrying the
zeros of `Q'` onto the zeros of `f'`, degree for degree. -/

theorem derivative_Q_eval (w : ℂ) :
    (Polynomial.derivative Q).eval w
      = 7 * w ^ 6 + 3 * a * w ^ 2 + 2 * b * w + c
        - 4 * (s : ℂ) ^ 2 * conj a * w ^ 3
        - 5 * (s : ℂ) ^ 6 * conj b * w ^ 4
        - 6 * (s : ℂ) ^ 10 * conj c * w ^ 5 := by
  simp only [Q, P, G, E, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X_pow, Polynomial.derivative_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero, a, b, c]
  push_cast
  ring

/-- Paper (4.4), differentiated form. -/
theorem derivative_f_eval_rho_eps (w : ℂ) :
    (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * w)
      = (ρ : ℂ) ^ 6 * (ε : ℂ) ^ 6 * (Polynomial.derivative Q).eval w := by
  rw [derivative_Q_eval]
  simp only [f, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X_pow, Polynomial.derivative_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero, a, b, c, ε]
  push_cast
  ring

theorem derivative_f_natDegree : (Polynomial.derivative f).natDegree = 6 := by
  have hd : (Polynomial.derivative f).degree = ((f.natDegree - 1 : ℕ) : WithBot ℕ) :=
    Polynomial.degree_derivative_eq f (by rw [s4_f_monic_degree'.2]; norm_num)
  rw [s4_f_monic_degree'.2] at hd
  have : (Polynomial.derivative f).degree = (6 : ℕ) := by simpa using hd
  exact Polynomial.natDegree_eq_of_degree_eq_some this

/-- Once a polynomial's zeros are known to be simple, every multiplicity is one.
This is the shape in which `rootMultiplicity zs (derivative f) = 1` will be
discharged, once the six critical points are localised. -/
theorem rootMultiplicity_eq_one_of_nodup {p : Polynomial ℂ} (hp : p ≠ 0)
    (hnd : p.roots.Nodup) {z : ℂ} (hz : p.IsRoot z) :
    Polynomial.rootMultiplicity z p = 1 := by
  have hmem : z ∈ p.roots := (Polynomial.mem_roots hp).mpr hz
  rw [← Polynomial.count_roots]
  exact Multiset.count_eq_one_of_mem hnd hmem

/-! ## A Newton contraction bridge for the critical-point localisation -/

/-- A Newton map on a nonempty complete set gives a unique zero.

For the S4 critical disks, use `p z = (Polynomial.derivative Q).eval z` and
`d = (Polynomial.derivative (Polynomial.derivative Q)).eval centre`.  Finite
Taylor inequalities provide `hmap` and `hlip`. -/
theorem exists_unique_zero_of_newton_contraction
    (p : ℂ → ℂ) (S : Set ℂ) (hcomplete : IsComplete S)
    (x₀ : ℂ) (hx₀ : x₀ ∈ S) (d : ℂ) (hd : d ≠ 0)
    (hmap : ∀ z ∈ S, z - p z / d ∈ S)
    (hlip : ∀ x ∈ S, ∀ y ∈ S,
      ‖(x - p x / d) - (y - p y / d)‖ ≤ (1 / 2 : ℝ) * ‖x - y‖) :
    ∃! z : ℂ, z ∈ S ∧ p z = 0 := by
  let step : ℂ → ℂ := fun z => z - p z / d
  have hmaps : Set.MapsTo step S S := hmap
  have hc : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict step S S) := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      have := hlip x.val x.property y.val y.property
      simpa [step, Set.MapsTo.restrict, Subtype.dist_eq, dist_eq_norm] using this
  obtain ⟨z, hz, hfixed, _, _⟩ :=
    hc.exists_fixedPoint' hcomplete hmaps hx₀ (edist_ne_top _ _)
  have hzroot : p z = 0 := by
    have hf : z - p z / d = z := hfixed
    have hdiv : p z / d = 0 := by linear_combination -hf
    exact (div_eq_zero_iff.mp hdiv).resolve_right hd
  refine ⟨z, ⟨hz, hzroot⟩, ?_⟩
  intro w hw
  have hdist := hlip w hw.1 z hz
  simp only [hw.2, hzroot, zero_div, sub_zero] at hdist
  have hn : ‖w - z‖ = 0 := by nlinarith [norm_nonneg (w - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-! ## Exact arithmetic budgets for the critical package

These are the rational margin checks of `INSTANCE_CERTIFICATES.md`, restated as
exact rational inequalities. -/

def scaledRadius : ℝ := 1 / 10

def physicalRadius : ℝ := (ρ : ℝ) * (ε : ℝ) * scaledRadius

theorem physicalRadius_pos : 0 < physicalRadius := by
  unfold physicalRadius scaledRadius
  exact mul_pos (mul_pos rho_pos eps_pos) (by norm_num)

/-- The entire degree-five tail budget is less than a quarter of 180. -/
theorem quadratic_tail_budget :
    190 * scaledRadius + 20 * scaledRadius ^ 2 + 15 * scaledRadius ^ 3
      + 6 * scaledRadius ^ 4 + scaledRadius ^ 5 < 180 / 4 := by
  norm_num [scaledRadius]

/-- The required slit bound fits within the smaller admissible physical disk. -/
theorem slit_budget : (36 / 5 / 10 ^ 6 : ℝ) < 180 * scaledRadius ^ 2 / 4 := by
  norm_num [scaledRadius]

/-- Coarse localisation already gives more than the requested projection gain. -/
theorem projection_budget :
    (2 / 1000 : ℝ) - (4 / 5) * (346 / 1000) ≤ -(143 / 1000) := by
  norm_num

/-! ## The lemniscate defect `H_s` in the scaled coordinate -/

/-- `K₀ = (ρ⁻¹⁴ - 1)/(2ε⁷)` (paper (4.5)), written without a reciprocal. -/
def K0 : ℝ := (1 - (ρ : ℝ) ^ 14) / (2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7)

/-- `H_s(w) = K₀ + Re Q_s(w) - (ε⁷/2)|Q_s(w)|²` (paper (4.6)). -/
def Hs (w : ℂ) : ℝ :=
  K0 + (Q.eval w).re - ((ε : ℝ) ^ 7 / 2) * Complex.normSq (Q.eval w)

theorem normSq_rho_pow : Complex.normSq ((ρ : ℂ) ^ 7) = (ρ : ℝ) ^ 14 := by
  rw [map_pow]
  simp only [Complex.normSq_apply, Complex.ratCast_re, Complex.ratCast_im]
  ring

/-- Paper (4.6): `1 - |f(ρεw)|² = 2 ρ¹⁴ ε⁷ H_s(w)`.  Exact identity; this is the
bridge that turns the rational sign certificates for `H_s` into membership of
`Ω(f)`. -/
theorem one_sub_normSq_f_rho_eps (w : ℂ) :
    1 - Complex.normSq (f.eval ((ρ : ℂ) * (ε : ℂ) * w))
      = 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs w := by
  have he : ((ε : ℂ)) ^ 7 = ((((ε : ℝ)) ^ 7 : ℝ) : ℂ) := by push_cast; ring
  have h2 : Complex.normSq (-1 + ((((ε : ℝ)) ^ 7 : ℝ) : ℂ) * Q.eval w)
      = 1 - 2 * (ε : ℝ) ^ 7 * (Q.eval w).re
        + ((ε : ℝ) ^ 7) ^ 2 * Complex.normSq (Q.eval w) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im]
    ring
  rw [f_eval_rho_eps, Complex.normSq_mul, normSq_rho_pow, he, h2]
  have hr : ((ρ : ℝ)) ≠ 0 := ne_of_gt rho_pos
  have hepsr : ((ε : ℝ)) ≠ 0 := ne_of_gt eps_pos
  unfold Hs K0
  field_simp
  ring

/-- The physical form of the defect identity, at `z = ρεw`. -/
theorem one_sub_sq_norm_f_rho_eps (w : ℂ) :
    1 - ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ ^ 2
      = 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs w := by
  rw [← Complex.normSq_eq_norm_sq]
  exact one_sub_normSq_f_rho_eps w


end S4Proofs

/-! ## Root-localisation conjuncts of `s4_instance_critical`

Public: S7 consumes these directly.  The witnesses are
`b₃ = S4Proofs.physicalRoot 3` and `b₆ = S4Proofs.physicalRoot 6`. -/

/-- Conjunct: every zero of `f` lies within `ρ/10` of some `ρ u_j`. -/
theorem s4_roots_near_seventh_roots :
    ∀ w, f.IsRoot w → ∃ j : Fin 7, ‖w - (ρ : ℂ) * u (j : ℕ)‖ < (ρ : ℝ) / 10 := by
  intro w hw
  obtain ⟨j, rfl⟩ := S4Proofs.exists_index_of_isRoot hw
  exact ⟨j, S4Proofs.physicalRoot_near j⟩

private theorem unique_near_aux (j : Fin 7) (k : ℕ)
    (hsep : (1 / 5 : ℝ) ≤ ‖u (j : ℕ) - u k‖)
    (hnear : ‖S4Proofs.physicalRoot j - (ρ : ℂ) * u k‖ < (ρ : ℝ) / 10) : False := by
  have h1 := S4Proofs.physicalRoot_near j
  have e : (ρ : ℂ) * (u (j : ℕ) - u k)
      = (S4Proofs.physicalRoot j - (ρ : ℂ) * u k)
        - (S4Proofs.physicalRoot j - (ρ : ℂ) * u (j : ℕ)) := by ring
  have hlt : ‖(ρ : ℂ) * (u (j : ℕ) - u k)‖ < (ρ : ℝ) / 5 := by
    rw [e]
    have htri := norm_sub_le (S4Proofs.physicalRoot j - (ρ : ℂ) * u k)
      (S4Proofs.physicalRoot j - (ρ : ℂ) * u (j : ℕ))
    linarith
  rw [norm_mul, Complex.norm_ratCast, abs_of_pos S4Proofs.rho_pos] at hlt
  nlinarith [S4Proofs.rho_pos, hsep, hlt]

/-- Conjunct: the disk of radius `ρ/10` about `ρ e^{6πi/7}` holds exactly one
zero of `f`, namely `b₃`. -/
theorem s4_root_unique_near_u3 :
    ∀ w, f.IsRoot w →
      ‖w - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 →
      w = S4Proofs.physicalRoot 3 := by
  intro w hw hnear
  rw [exp_six_pi_div_seven] at hnear
  obtain ⟨j, rfl⟩ := S4Proofs.exists_index_of_isRoot hw
  have hj : (j : ℕ) = 3 := by
    by_contra hne
    exact unique_near_aux j 3 (u_sep_three (j : ℕ) j.isLt hne) hnear
  have hje : j = 3 := by
    apply Fin.ext
    simpa using hj
  rw [hje]

/-- Conjunct: the disk of radius `ρ/10` about `ρ e^{-2πi/7}` holds exactly one
zero of `f`, namely `b₆`. -/
theorem s4_root_unique_near_u6 :
    ∀ w, f.IsRoot w →
      ‖w - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 →
      w = S4Proofs.physicalRoot 6 := by
  intro w hw hnear
  rw [exp_neg_two_pi_div_seven] at hnear
  obtain ⟨j, rfl⟩ := S4Proofs.exists_index_of_isRoot hw
  have hj : (j : ℕ) = 6 := by
    by_contra hne
    exact unique_near_aux j 6 (u_sep_six (j : ℕ) j.isLt hne) hnear
  have hje : j = 6 := by
    apply Fin.ext
    simpa using hj
  rw [hje]

/-- Conjunct: `b₃` is a zero of `f`, localised at `ρ e^{6πi/7}`. -/
theorem s4_b3_isRoot : f.IsRoot (S4Proofs.physicalRoot 3) :=
  S4Proofs.physicalRoot_isRoot 3

/-- Conjunct: `b₆` is a zero of `f`, localised at `ρ e^{-2πi/7}`. -/
theorem s4_b6_isRoot : f.IsRoot (S4Proofs.physicalRoot 6) :=
  S4Proofs.physicalRoot_isRoot 6

theorem s4_b3_ne_b6 : S4Proofs.physicalRoot 3 ≠ S4Proofs.physicalRoot 6 := by
  intro h
  have := S4Proofs.physicalRoot_injective h
  exact absurd this (by decide)

theorem s4_b3_near :
    ‖S4Proofs.physicalRoot 3 - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖
      < (ρ : ℝ) / 10 := by
  rw [exp_six_pi_div_seven]
  exact S4Proofs.physicalRoot_near 3

theorem s4_b6_near :
    ‖S4Proofs.physicalRoot 6 - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖
      < (ρ : ℝ) / 10 := by
  rw [exp_neg_two_pi_div_seven]
  exact S4Proofs.physicalRoot_near 6

/-! ## The S4 obligations at their interface names -/

/-- `f` is monic of degree seven.  Owner: slice S4. -/
theorem s4_f_monic_degree : f.Monic ∧ f.natDegree = 7 :=
  S4Proofs.s4_f_monic_degree'

/-- Every zero of `f` has modulus exactly `ρ`.  Owner: slice S4. -/
theorem s4_roots_on_circle : ∀ z, f.IsRoot z → ‖z‖ = (ρ : ℝ) :=
  S4Proofs.s4_roots_on_circle'

/-- The seven zeros of `f` are simple.  Owner: slice S4. -/
theorem s4_roots_nodup : f.roots.Nodup :=
  S4Proofs.s4_roots_nodup'

end Erdos1041.Counterexample

-- BEGIN GENERATED: coarse instance certificates
-- Regenerate with
--   ./repo-python formal_math/erdos1041_external_counterexample/emit_instance_certificates.py
-- Numbers verified exactly by instance_certificates_coarse.py (26/26 checks).

namespace Erdos1041.Counterexample.S4Proofs

/-! ### The constants as rational-cast Gaussian rationals

Every constant is kept in the shape `((x : ℚ) : ℂ) + ((y : ℚ) : ℂ) * I`, so that
`re` and `im` are read off by `Complex.ratCast_re` / `Complex.ratCast_im`.  No
complex division ever appears, hence no `starRingEnd` residue for `ring` to
choke on. -/

theorem s_rat : (s : ℚ) = 1 / 1000000 := by norm_num [s]

theorem a_Q : a = ((-329507 / 1600 : ℚ) : ℂ) + ((-1 / 1000000 : ℚ) : ℂ) * Complex.I := by
  unfold a; rw [A_value, s_rat] <;> push_cast <;> ring

theorem b_Q : b = ((9 / 5000000 : ℚ) : ℂ) + ((551827 / 800 : ℚ) : ℂ) * Complex.I := by
  unfold b; rw [B_value, s_rat] <;> push_cast <;> ring

theorem c_Q : c = ((23013813 / 32000 : ℚ) : ℂ) + ((-81 / 12500000 : ℚ) : ℂ) * Complex.I := by
  unfold c; rw [Cconst_value, s_rat] <;> push_cast <;> ring

theorem conj_a_Q :
    conj a = ((-329507 / 1600 : ℚ) : ℂ) + ((1 / 1000000 : ℚ) : ℂ) * Complex.I := by
  rw [conj_a, A_value, s_rat] <;> push_cast <;> ring

theorem conj_b_Q :
    conj b = ((9 / 5000000 : ℚ) : ℂ) + ((-551827 / 800 : ℚ) : ℂ) * Complex.I := by
  rw [conj_b, B_value, s_rat] <;> push_cast <;> ring

theorem conj_c_Q :
    conj c = ((23013813 / 32000 : ℚ) : ℂ) + ((81 / 12500000 : ℚ) : ℂ) * Complex.I := by
  rw [conj_c, Cconst_value, s_rat] <;> push_cast <;> ring

/-! ### Taylor coefficients of `Q'` at an arbitrary point

`Q'(w) = qp₀ + qp₁w + … + qp₆w⁶`; `qpTj v` is the `j`-th Taylor coefficient of
`Q'` at `v`.  The expansion lemma is the binomial theorem, so `ring` proves it
with `a`, `b`, `c`, their conjugates, `v` and `t` all atoms: no numeral and no
`I² = -1` is involved. -/

def qp0 : ℂ := c
def qp1 : ℂ := 2 * b
def qp2 : ℂ := 3 * a
def qp3 : ℂ := -4 * (s : ℂ) ^ 2 * conj a
def qp4 : ℂ := -5 * (s : ℂ) ^ 6 * conj b
def qp5 : ℂ := -6 * (s : ℂ) ^ 10 * conj c
def qp6 : ℂ := 7

theorem derivative_Q_eval' (w : ℂ) :
    (Polynomial.derivative Q).eval w
      = qp0 + qp1 * w + qp2 * w ^ 2 + qp3 * w ^ 3 + qp4 * w ^ 4 + qp5 * w ^ 5
        + qp6 * w ^ 6 := by
  rw [derivative_Q_eval]
  unfold qp0 qp1 qp2 qp3 qp4 qp5 qp6
  ring

def qpT0 (v : ℂ) : ℂ :=
  qp0 + qp1 * v + qp2 * v ^ 2 + qp3 * v ^ 3 + qp4 * v ^ 4 + qp5 * v ^ 5 + qp6 * v ^ 6
def qpT1 (v : ℂ) : ℂ :=
  qp1 + 2 * qp2 * v + 3 * qp3 * v ^ 2 + 4 * qp4 * v ^ 3 + 5 * qp5 * v ^ 4 + 6 * qp6 * v ^ 5
def qpT2 (v : ℂ) : ℂ :=
  qp2 + 3 * qp3 * v + 6 * qp4 * v ^ 2 + 10 * qp5 * v ^ 3 + 15 * qp6 * v ^ 4
def qpT3 (v : ℂ) : ℂ := qp3 + 4 * qp4 * v + 10 * qp5 * v ^ 2 + 20 * qp6 * v ^ 3
def qpT4 (v : ℂ) : ℂ := qp4 + 5 * qp5 * v + 15 * qp6 * v ^ 2
def qpT5 (v : ℂ) : ℂ := qp5 + 6 * qp6 * v
def qpT6 : ℂ := qp6

theorem Qp_taylor (v t : ℂ) :
    (Polynomial.derivative Q).eval (v + t)
      = qpT0 v + qpT1 v * t + qpT2 v * t ^ 2 + qpT3 v * t ^ 3 + qpT4 v * t ^ 4
        + qpT5 v * t ^ 5 + qpT6 * t ^ 6 := by
  rw [derivative_Q_eval']
  unfold qpT0 qpT1 qpT2 qpT3 qpT4 qpT5 qpT6
  ring

/-! ### Norm bounds through `normSq`; `Real.sqrt` never appears -/

theorem norm_le_of_normSq_le {z : ℂ} {n : ℝ} (hn : 0 ≤ n)
    (h : Complex.normSq z ≤ n ^ 2) : ‖z‖ ≤ n := by
  have h2 : ‖z‖ ^ 2 ≤ n ^ 2 := by rwa [← Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg z, hn, h2]

theorem le_norm_of_le_normSq {z : ℂ} {m : ℝ} (hm : 0 ≤ m)
    (h : m ^ 2 ≤ Complex.normSq z) : m ≤ ‖z‖ := by
  have h2 : m ^ 2 ≤ ‖z‖ ^ 2 := by rwa [← Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg z, hm, h2]

/-! ### The abstract disk localisation

A degree-six Taylor datum on a closed disk, with a residual bound and a
contraction bound, pins exactly one zero inside the disk.  This is the only
analytic step; every instance of it below supplies nothing but exact rational
inequalities. -/

theorem norm_pow_sub_pow_le (n : ℕ) {x y : ℂ} {rr : ℝ} (hx : ‖x‖ ≤ rr) (hy : ‖y‖ ≤ rr) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ (n + 1) * rr ^ n * ‖x - y‖ := by
  have hr0 : (0 : ℝ) ≤ rr := le_trans (norm_nonneg x) hx
  induction n with
  | zero => simp
  | succ m ih =>
    have hfac : x ^ (m + 2) - y ^ (m + 2)
        = x * (x ^ (m + 1) - y ^ (m + 1)) + y ^ (m + 1) * (x - y) := by ring
    have hy' : ‖y ^ (m + 1)‖ ≤ rr ^ (m + 1) := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg y) hy _
    calc ‖x ^ (m + 2) - y ^ (m + 2)‖
        ≤ ‖x * (x ^ (m + 1) - y ^ (m + 1))‖ + ‖y ^ (m + 1) * (x - y)‖ := by
          rw [hfac]; exact norm_add_le _ _
      _ = ‖x‖ * ‖x ^ (m + 1) - y ^ (m + 1)‖ + ‖y ^ (m + 1)‖ * ‖x - y‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ rr * ((m + 1) * rr ^ m * ‖x - y‖) + rr ^ (m + 1) * ‖x - y‖ := by
          have h1 : ‖x‖ * ‖x ^ (m + 1) - y ^ (m + 1)‖ ≤ rr * ((m + 1) * rr ^ m * ‖x - y‖) := by
            apply mul_le_mul hx ih (norm_nonneg _) hr0
          have h2 : ‖y ^ (m + 1)‖ * ‖x - y‖ ≤ rr ^ (m + 1) * ‖x - y‖ :=
            mul_le_mul_of_nonneg_right hy' (norm_nonneg _)
          linarith
      _ = (↑(m + 1) + 1) * rr ^ (m + 1) * ‖x - y‖ := by push_cast; ring

theorem newton_disk
    (p : ℂ → ℂ) {v d0 d1 d2 d3 d4 d5 d6 : ℂ} {rr n0 n2 n3 n4 n5 n6 m1 : ℝ}
    (hr : 0 < rr)
    (hexp : ∀ t : ℂ, p (v + t)
      = d0 + d1 * t + d2 * t ^ 2 + d3 * t ^ 3 + d4 * t ^ 4 + d5 * t ^ 5 + d6 * t ^ 6)
    (hn0 : ‖d0‖ ≤ n0) (hn2 : ‖d2‖ ≤ n2) (hn3 : ‖d3‖ ≤ n3) (hn4 : ‖d4‖ ≤ n4)
    (hn5 : ‖d5‖ ≤ n5) (hn6 : ‖d6‖ ≤ n6)
    (hm1 : m1 ≤ ‖d1‖) (hm1pos : 0 < m1)
    (hmapb : n0 + n2 * rr ^ 2 + n3 * rr ^ 3 + n4 * rr ^ 4 + n5 * rr ^ 5 + n6 * rr ^ 6
      ≤ m1 * rr)
    (hlipb : 2 * n2 * rr + 3 * n3 * rr ^ 2 + 4 * n4 * rr ^ 3 + 5 * n5 * rr ^ 4
      + 6 * n6 * rr ^ 5 ≤ m1 / 2) :
    ∃! z : ℂ, z ∈ Metric.closedBall v rr ∧ p z = 0 := by
  have hd1 : d1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hm1
    linarith
  have hd1n : 0 < ‖d1‖ := lt_of_lt_of_le hm1pos hm1
  refine exists_unique_zero_of_newton_contraction p (Metric.closedBall v rr)
    (Metric.isClosed_closedBall.isComplete) v (Metric.mem_closedBall_self hr.le) d1 hd1
    ?_ ?_
  · intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    have hzv : z = v + (z - v) := by ring
    have hpz := hexp (z - v)
    rw [← hzv] at hpz
    have hrew : z - p z / d1 - v
        = -((d0 + d2 * (z - v) ^ 2 + d3 * (z - v) ^ 3 + d4 * (z - v) ^ 4
            + d5 * (z - v) ^ 5 + d6 * (z - v) ^ 6) / d1) := by
      rw [hpz]; field_simp; ring
    rw [hrew, norm_neg, norm_div, div_le_iff₀ hd1n]
    have hb : ∀ (dd : ℂ) (nn : ℝ) (k : ℕ), ‖dd‖ ≤ nn → ‖dd * (z - v) ^ k‖ ≤ nn * rr ^ k := by
      intro dd nn k hdd
      rw [norm_mul, norm_pow]
      exact mul_le_mul hdd (pow_le_pow_left₀ (norm_nonneg _) hz k) (by positivity)
        (le_trans (norm_nonneg _) hdd)
    have t2 := hb d2 n2 2 hn2
    have t3 := hb d3 n3 3 hn3
    have t4 := hb d4 n4 4 hn4
    have t5 := hb d5 n5 5 hn5
    have t6 := hb d6 n6 6 hn6
    have htri : ‖d0 + d2 * (z - v) ^ 2 + d3 * (z - v) ^ 3 + d4 * (z - v) ^ 4
        + d5 * (z - v) ^ 5 + d6 * (z - v) ^ 6‖
        ≤ ‖d0‖ + ‖d2 * (z - v) ^ 2‖ + ‖d3 * (z - v) ^ 3‖ + ‖d4 * (z - v) ^ 4‖
          + ‖d5 * (z - v) ^ 5‖ + ‖d6 * (z - v) ^ 6‖ := by
      refine le_trans (norm_add_le _ _) ?_
      gcongr
      refine le_trans (norm_add_le _ _) ?_
      gcongr
      refine le_trans (norm_add_le _ _) ?_
      gcongr
      refine le_trans (norm_add_le _ _) ?_
      gcongr
      exact norm_add_le _ _
    nlinarith [htri, hn0, t2, t3, t4, t5, t6, hmapb, hm1, hr]
  · intro x hx y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hx hy
    have hpx := hexp (x - v)
    have hpy := hexp (y - v)
    rw [show v + (x - v) = x by ring] at hpx
    rw [show v + (y - v) = y by ring] at hpy
    have hrew : x - p x / d1 - (y - p y / d1)
        = -((d2 * ((x - v) ^ 2 - (y - v) ^ 2) + d3 * ((x - v) ^ 3 - (y - v) ^ 3)
            + d4 * ((x - v) ^ 4 - (y - v) ^ 4) + d5 * ((x - v) ^ 5 - (y - v) ^ 5)
            + d6 * ((x - v) ^ 6 - (y - v) ^ 6)) / d1) := by
      rw [hpx, hpy]; field_simp; ring
    have hxy : (x - v) - (y - v) = x - y := by ring
    have hb : ∀ (dd : ℂ) (nn : ℝ) (k : ℕ), ‖dd‖ ≤ nn →
        ‖dd * ((x - v) ^ (k + 1) - (y - v) ^ (k + 1))‖
          ≤ nn * ((k + 1) * rr ^ k) * ‖x - y‖ := by
      intro dd nn k hdd
      rw [norm_mul]
      have h1 := norm_pow_sub_pow_le k hx hy
      rw [hxy] at h1
      have hnn : 0 ≤ nn := le_trans (norm_nonneg _) hdd
      calc ‖dd‖ * ‖(x - v) ^ (k + 1) - (y - v) ^ (k + 1)‖
          ≤ nn * ((k + 1) * rr ^ k * ‖x - y‖) :=
            mul_le_mul hdd h1 (norm_nonneg _) hnn
        _ = nn * ((k + 1) * rr ^ k) * ‖x - y‖ := by ring
    have t2 := hb d2 n2 1 hn2
    have t3 := hb d3 n3 2 hn3
    have t4 := hb d4 n4 3 hn4
    have t5 := hb d5 n5 4 hn5
    have t6 := hb d6 n6 5 hn6
    norm_num at t2 t3 t4 t5 t6
    rw [hrew, norm_neg, norm_div, div_le_iff₀ hd1n]
    have htri : ‖d2 * ((x - v) ^ 2 - (y - v) ^ 2) + d3 * ((x - v) ^ 3 - (y - v) ^ 3)
        + d4 * ((x - v) ^ 4 - (y - v) ^ 4) + d5 * ((x - v) ^ 5 - (y - v) ^ 5)
        + d6 * ((x - v) ^ 6 - (y - v) ^ 6)‖
        ≤ ‖d2 * ((x - v) ^ 2 - (y - v) ^ 2)‖ + ‖d3 * ((x - v) ^ 3 - (y - v) ^ 3)‖
          + ‖d4 * ((x - v) ^ 4 - (y - v) ^ 4)‖ + ‖d5 * ((x - v) ^ 5 - (y - v) ^ 5)‖
          + ‖d6 * ((x - v) ^ 6 - (y - v) ^ 6)‖ := by
      exact le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
        (add_le_add (le_trans (norm_add_le _ _)
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    simp only [norm_mul] at htri
    have hstep := le_trans htri
      (add_le_add (add_le_add (add_le_add (add_le_add t2 t3) t4) t5) t6)
    have p1 := mul_le_mul_of_nonneg_right hlipb (norm_nonneg (x - y))
    have p2 := mul_le_mul_of_nonneg_right hm1 (norm_nonneg (x - y))
    nlinarith [hstep, p1, p2, norm_nonneg (x - y)]

/-! ### `qp₀ … qp₆` as explicit Gaussian-rational numerals -/

theorem qp0_Q : qp0 = (((23013813 / 32000 : ℚ) : ℂ) + (((-81 / 12500000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp0
  rw [c_Q] <;> push_cast <;> ring

theorem qp1_Q : qp1 = (((9 / 2500000 : ℚ) : ℂ) + (((551827 / 400 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp1
  rw [b_Q] <;> push_cast <;> ring

theorem qp2_Q : qp2 = (((-988521 / 1600 : ℚ) : ℂ) + (((-3 / 1000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp2
  rw [a_Q] <;> push_cast <;> ring

theorem qp3_Q : qp3 = (((329507 / 400000000000000 : ℚ) : ℂ) + (((-1 / 250000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp3
  rw [conj_a_Q, s_rat] <;> push_cast <;> ring

theorem qp4_Q : qp4 = (((-9 / 1000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((551827 / 160000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp4
  rw [conj_b_Q, s_rat] <;> push_cast <;> ring

theorem qp5_Q : qp5 = (((-69041439 / 16000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-243 / 6250000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp5
  rw [conj_c_Q, s_rat] <;> push_cast <;> ring

theorem qp6_Q : qp6 = (((7 : ℚ) : ℂ) + (((0 : ℚ) : ℂ)) * Complex.I) := by
  unfold qp6
  push_cast <;> ring

/-! ### Taylor coefficients of `Q` itself, for the `H_s` sign certificates -/

def qq0 : ℂ := 0
def qq1 : ℂ := c
def qq2 : ℂ := b
def qq3 : ℂ := a
def qq4 : ℂ := -(s : ℂ) ^ 2 * conj a
def qq5 : ℂ := -(s : ℂ) ^ 6 * conj b
def qq6 : ℂ := -(s : ℂ) ^ 10 * conj c
def qq7 : ℂ := 1

theorem Q_eval'' (w : ℂ) :
    Q.eval w = qq0 + qq1 * w + qq2 * w ^ 2 + qq3 * w ^ 3 + qq4 * w ^ 4 + qq5 * w ^ 5
      + qq6 * w ^ 6 + qq7 * w ^ 7 := by
  rw [Q_eval_expanded]
  unfold qq0 qq1 qq2 qq3 qq4 qq5 qq6 qq7
  ring

def qT0 (v : ℂ) : ℂ :=
  qq0 + qq1 * v + qq2 * v ^ 2 + qq3 * v ^ 3 + qq4 * v ^ 4 + qq5 * v ^ 5 + qq6 * v ^ 6
    + qq7 * v ^ 7
def qT1 (v : ℂ) : ℂ :=
  qq1 + 2 * qq2 * v + 3 * qq3 * v ^ 2 + 4 * qq4 * v ^ 3 + 5 * qq5 * v ^ 4 + 6 * qq6 * v ^ 5
    + 7 * qq7 * v ^ 6
def qT2 (v : ℂ) : ℂ :=
  qq2 + 3 * qq3 * v + 6 * qq4 * v ^ 2 + 10 * qq5 * v ^ 3 + 15 * qq6 * v ^ 4 + 21 * qq7 * v ^ 5
def qT3 (v : ℂ) : ℂ :=
  qq3 + 4 * qq4 * v + 10 * qq5 * v ^ 2 + 20 * qq6 * v ^ 3 + 35 * qq7 * v ^ 4
def qT4 (v : ℂ) : ℂ := qq4 + 5 * qq5 * v + 15 * qq6 * v ^ 2 + 35 * qq7 * v ^ 3
def qT5 (v : ℂ) : ℂ := qq5 + 6 * qq6 * v + 21 * qq7 * v ^ 2
def qT6 (v : ℂ) : ℂ := qq6 + 7 * qq7 * v
def qT7 : ℂ := qq7

theorem Q_taylor (v t : ℂ) :
    Q.eval (v + t) = qT0 v + qT1 v * t + qT2 v * t ^ 2 + qT3 v * t ^ 3 + qT4 v * t ^ 4
      + qT5 v * t ^ 5 + qT6 v * t ^ 6 + qT7 * t ^ 7 := by
  rw [Q_eval'']
  unfold qT0 qT1 qT2 qT3 qT4 qT5 qT6 qT7
  ring

theorem qT7_bound : ‖qT7‖ ≤ (1 : ℝ) := by
  unfold qT7 qq7
  simp

/-- The excursion of `Q` over a closed disk, from its Taylor data. -/
theorem Q_var_on_disk {v : ℂ} {rr g1 g2 g3 g4 g5 g6 g7 : ℝ} (hr : 0 ≤ rr)
    (h1 : ‖qT1 v‖ ≤ g1) (h2 : ‖qT2 v‖ ≤ g2) (h3 : ‖qT3 v‖ ≤ g3) (h4 : ‖qT4 v‖ ≤ g4)
    (h5 : ‖qT5 v‖ ≤ g5) (h6 : ‖qT6 v‖ ≤ g6) (h7 : ‖qT7‖ ≤ g7) :
    ∀ w : ℂ, ‖w - v‖ ≤ rr →
      ‖Q.eval w - qT0 v‖
        ≤ g1 * rr + g2 * rr ^ 2 + g3 * rr ^ 3 + g4 * rr ^ 4 + g5 * rr ^ 5 + g6 * rr ^ 6
          + g7 * rr ^ 7 := by
  intro w hw
  have hq := Q_taylor v (w - v)
  rw [show v + (w - v) = w by ring] at hq
  have hrew : Q.eval w - qT0 v
      = qT1 v * (w - v) + qT2 v * (w - v) ^ 2 + qT3 v * (w - v) ^ 3 + qT4 v * (w - v) ^ 4
        + qT5 v * (w - v) ^ 5 + qT6 v * (w - v) ^ 6 + qT7 * (w - v) ^ 7 := by
    rw [hq]; ring
  have hb : ∀ (dd : ℂ) (nn : ℝ) (k : ℕ), ‖dd‖ ≤ nn → ‖dd * (w - v) ^ k‖ ≤ nn * rr ^ k := by
    intro dd nn k hdd
    rw [norm_mul, norm_pow]
    exact mul_le_mul hdd (pow_le_pow_left₀ (norm_nonneg _) hw k) (by positivity)
      (le_trans (norm_nonneg _) hdd)
  have t1 := hb (qT1 v) g1 1 h1
  have t2 := hb (qT2 v) g2 2 h2
  have t3 := hb (qT3 v) g3 3 h3
  have t4 := hb (qT4 v) g4 4 h4
  have t5 := hb (qT5 v) g5 5 h5
  have t6 := hb (qT6 v) g6 6 h6
  have t7 := hb qT7 g7 7 h7
  rw [hrew]
  set X1 := qT1 v * (w - v)
  set X2 := qT2 v * (w - v) ^ 2
  set X3 := qT3 v * (w - v) ^ 3
  set X4 := qT4 v * (w - v) ^ 4
  set X5 := qT5 v * (w - v) ^ 5
  set X6 := qT6 v * (w - v) ^ 6
  set X7 := qT7 * (w - v) ^ 7
  have H2 : ‖X1 + X2‖ ≤ ‖X1‖ + ‖X2‖ := norm_add_le _ _
  have H3 : ‖X1 + X2 + X3‖ ≤ ‖X1‖ + ‖X2‖ + ‖X3‖ :=
    le_trans (norm_add_le _ _) (add_le_add H2 le_rfl)
  have H4 : ‖X1 + X2 + X3 + X4‖ ≤ ‖X1‖ + ‖X2‖ + ‖X3‖ + ‖X4‖ :=
    le_trans (norm_add_le _ _) (add_le_add H3 le_rfl)
  have H5 : ‖X1 + X2 + X3 + X4 + X5‖ ≤ ‖X1‖ + ‖X2‖ + ‖X3‖ + ‖X4‖ + ‖X5‖ :=
    le_trans (norm_add_le _ _) (add_le_add H4 le_rfl)
  have H6 : ‖X1 + X2 + X3 + X4 + X5 + X6‖ ≤ ‖X1‖ + ‖X2‖ + ‖X3‖ + ‖X4‖ + ‖X5‖ + ‖X6‖ :=
    le_trans (norm_add_le _ _) (add_le_add H5 le_rfl)
  have H7 : ‖X1 + X2 + X3 + X4 + X5 + X6 + X7‖
      ≤ ‖X1‖ + ‖X2‖ + ‖X3‖ + ‖X4‖ + ‖X5‖ + ‖X6‖ + ‖X7‖ :=
    le_trans (norm_add_le _ _) (add_le_add H6 le_rfl)
  simp only [pow_one] at t1
  linarith [H7, t1, t2, t3, t4, t5, t6, t7]

/-! ### `K₀` is between `0` and `10⁻¹¹` -/

theorem rho_pow14_le_one : (ρ : ℝ) ^ 14 ≤ 1 :=
  pow_le_one₀ rho_pos.le rho_lt_one.le

theorem rho_pow14_ge : (9 : ℝ) / 10 ≤ (ρ : ℝ) ^ 14 := by
  have hb : (1 : ℝ) + 14 * (-(1 / 10 ^ 96)) ≤ (1 + -(1 / 10 ^ 96)) ^ 14 := by
    apply one_add_mul_le_pow
    norm_num
  have he : (1 : ℝ) + -(1 / 10 ^ 96) = (ρ : ℝ) := by
    unfold ρ s; push_cast; ring
  rw [he] at hb
  nlinarith [hb]

theorem eps_pow7_pos : (0 : ℝ) < (ε : ℝ) ^ 7 := pow_pos eps_pos 7

theorem K0_denom_pos : (0 : ℝ) < 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 := by
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 14 := pow_pos rho_pos 14
  nlinarith [h1, eps_pow7_pos]

theorem K0_nonneg : 0 ≤ K0 := by
  unfold K0
  exact div_nonneg (by linarith [rho_pow14_le_one]) K0_denom_pos.le

theorem K0_le : K0 ≤ 1 / 10 ^ 11 := by
  unfold K0
  have h1 : (1 : ℝ) - (ρ : ℝ) ^ 14 ≤ 14 / 10 ^ 96 := by
    have hb : (1 : ℝ) + 14 * (-(1 / 10 ^ 96)) ≤ (1 + -(1 / 10 ^ 96)) ^ 14 := by
      apply one_add_mul_le_pow; norm_num
    have he : (1 : ℝ) + -(1 / 10 ^ 96) = (ρ : ℝ) := by unfold ρ s; push_cast; ring
    rw [he] at hb
    linarith
  have h2 : (9 : ℝ) / 10 ≤ (ρ : ℝ) ^ 14 := rho_pow14_ge
  have he7 : ((ε : ℝ)) ^ 7 = 1 / 10 ^ 84 := by unfold ε s; push_cast; norm_num
  rw [div_le_iff₀ K0_denom_pos, he7]
  nlinarith [h1, h2]

/-- The negative-sign certificate on a whole critical disk. -/
theorem Hs_neg_on_disk {v : ℂ} {rr var reHi : ℝ}
    (hvar : ∀ w : ℂ, ‖w - v‖ ≤ rr → ‖Q.eval w - qT0 v‖ ≤ var)
    (hre : (qT0 v).re ≤ reHi)
    (hneg : reHi + var + 1 / 10 ^ 11 < 0) :
    ∀ w : ℂ, ‖w - v‖ ≤ rr → Hs w < 0 := by
  intro w hw
  have hv := hvar w hw
  have hrele : (Q.eval w).re - (qT0 v).re ≤ var := by
    have := Complex.abs_re_le_norm (Q.eval w - qT0 v)
    simp only [Complex.sub_re] at this
    calc (Q.eval w).re - (qT0 v).re ≤ |(Q.eval w).re - (qT0 v).re| := le_abs_self _
      _ ≤ ‖Q.eval w - qT0 v‖ := this
      _ ≤ var := hv
  have hquad : 0 ≤ ((ε : ℝ) ^ 7 / 2) * Complex.normSq (Q.eval w) :=
    mul_nonneg (by linarith [eps_pow7_pos]) (Complex.normSq_nonneg _)
  unfold Hs
  linarith [K0_le, hrele, hre, hneg, hquad]

/-- The positive-sign certificate on the interior critical disk. -/
theorem Hs_pos_on_disk {v : ℂ} {rr var reLo absHi : ℝ} (habs : 0 ≤ absHi)
    (hvar : ∀ w : ℂ, ‖w - v‖ ≤ rr → ‖Q.eval w - qT0 v‖ ≤ var)
    (hre : reLo ≤ (qT0 v).re)
    (hnorm : ∀ w : ℂ, ‖w - v‖ ≤ rr → ‖Q.eval w‖ ≤ absHi)
    (hpos : 0 < reLo - var - absHi ^ 2 / 10 ^ 80) :
    ∀ w : ℂ, ‖w - v‖ ≤ rr → 0 < Hs w := by
  intro w hw
  have hv := hvar w hw
  have hn := hnorm w hw
  have hrege : (qT0 v).re - (Q.eval w).re ≤ var := by
    have := Complex.abs_re_le_norm (qT0 v - Q.eval w)
    simp only [Complex.sub_re] at this
    calc (qT0 v).re - (Q.eval w).re ≤ |(qT0 v).re - (Q.eval w).re| := le_abs_self _
      _ ≤ ‖qT0 v - Q.eval w‖ := this
      _ = ‖Q.eval w - qT0 v‖ := by rw [← norm_neg]; ring_nf
      _ ≤ var := hv
  have hns : Complex.normSq (Q.eval w) ≤ absHi ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have he7 : ((ε : ℝ)) ^ 7 = 1 / 10 ^ 84 := by unfold ε s; push_cast; norm_num
  have hquad : ((ε : ℝ) ^ 7 / 2) * Complex.normSq (Q.eval w) ≤ absHi ^ 2 / 10 ^ 80 := by
    rw [he7]
    nlinarith [hns, Complex.normSq_nonneg (Q.eval w)]
  unfold Hs
  linarith [K0_nonneg, hrege, hre, hpos, hquad]

/-! ### `qq₀ … qq₇` as explicit Gaussian-rational numerals -/

theorem qq0_Q : qq0 = (((0 : ℚ) : ℂ) + (((0 : ℚ) : ℂ)) * Complex.I) := by
  unfold qq0
  push_cast <;> ring

theorem qq1_Q : qq1 = (((23013813 / 32000 : ℚ) : ℂ) + (((-81 / 12500000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qq1
  rw [c_Q] <;> push_cast <;> ring

theorem qq2_Q : qq2 = (((9 / 5000000 : ℚ) : ℂ) + (((551827 / 800 : ℚ) : ℂ)) * Complex.I) := by
  unfold qq2
  rw [b_Q] <;> push_cast <;> ring

theorem qq3_Q : qq3 = (((-329507 / 1600 : ℚ) : ℂ) + (((-1 / 1000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qq3
  rw [a_Q] <;> push_cast <;> ring

theorem qq4_Q : qq4 = (((329507 / 1600000000000000 : ℚ) : ℂ) + (((-1 / 1000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qq4
  rw [conj_a_Q, s_rat] <;> push_cast <;> ring

theorem qq5_Q : qq5 = (((-9 / 5000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((551827 / 800000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qq5
  rw [conj_b_Q, s_rat] <;> push_cast <;> ring

theorem qq6_Q : qq6 = (((-23013813 / 32000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-81 / 12500000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  unfold qq6
  rw [conj_c_Q, s_rat] <;> push_cast <;> ring

theorem qq7_Q : qq7 = (((1 : ℚ) : ℂ) + (((0 : ℚ) : ℂ)) * Complex.I) := by
  unfold qq7
  push_cast <;> ring

theorem qpT6_bound : ‖qpT6‖ ≤ (7 : ℝ) := by
  unfold qpT6
  rw [qp6_Q]
  apply norm_le_of_normSq_le (by norm_num)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im]
  push_cast
  norm_num

/-! ### Centre 0: the critical point near `+3.18983-0.50000 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 9.525e-11 against the radius,
contraction ≤ 2.057e-06 against `1/2`. -/

def vc0 : ℂ := (((15949137893 / 5000000000 : ℚ) : ℂ) + (((-4999999979 / 10000000000 : ℚ) : ℂ)) * Complex.I)

theorem vc0_p2 : vc0 ^ 2 = (((198499999665942783471 / 20000000000000000000 : ℚ) : ℂ) + (((-79745689130068104247 / 25000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc0 ^ 2 = vc0 ^ 1 * vc0 := by ring
  rw [hs]
  unfold vc0
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc0_p3 : vc0 ^ 3 = (((15032062444211514848128961211389 / 500000000000000000000000000000 : ℚ) : ℂ) + (((-15137499909268208878783023188113 / 1000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc0 ^ 3 = vc0 ^ 2 * vc0 := by ring
  rw [hs, vc0_p2]
  unfold vc0
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc0_p4 : vc0 ^ 4 = (((883306247727210733585620292143044419203881 / 10000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-15829519265678895752052017655043376501337 / 250000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc0 ^ 4 = vc0 ^ 3 * vc0 := by ring
  rw [hs, vc0_p3]
  unfold vc0
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc0_p5 : vc0 ^ 5 = (((12505021226830210354606678811685869687691313480324273 / 50000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-24613906063943647314412641438549781458306649145753779 / 100000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc0 ^ 5 = vc0 ^ 4 * vc0 := by ring
  rw [hs, vc0_p4]
  unfold vc0
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc0_p6 : vc0 ^ 6 = (((134941540360720403149205355799054764942496515791919405357747303 / 200000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-227547843885365856204262660608742721908300340732250729305018957 / 250000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc0 ^ 6 = vc0 ^ 5 * vc0 := by ring
  rw [hs, vc0_p5]
  unfold vc0
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc0_p7 : vc0 ^ 7 = (((8485527744238124234368877719557862752117086643012980473670714717790059089 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-32407074009909443743700849551828982709266736460616262767276652229812833993 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc0 ^ 7 = vc0 ^ 6 * vc0 := by ring
  rw [hs, vc0_p6]
  unfold vc0
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem qpT0_vc0_bound : ‖qpT0 vc0‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc0_p6, vc0_p5, vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc0_bound : ‖qpT2 vc0‖ ≤ (2728815463 / 250000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc0_bound : ‖qpT3 vc0‖ ≤ (4712399811 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc0_p3, vc0_p2]
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc0_bound : ‖qpT4 vc0‖ ≤ (547312499 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc0_p2]
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc0_bound : ‖qpT5 vc0‖ ≤ (33902157 / 250000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc0_lower : (5306414501 / 500000 : ℝ) ≤ ‖qpT1 vc0‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc0_p5, vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc0`. -/
theorem crit_loc_0 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc0 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc0 t)
    qpT0_vc0_bound qpT2_vc0_bound qpT3_vc0_bound qpT4_vc0_bound qpT5_vc0_bound
    qpT6_bound qpT1_vc0_lower (by norm_num) (by norm_num) (by norm_num)

theorem qT1_vc0_bound : ‖qT1 vc0‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT1
  rw [vc0_p6, vc0_p5, vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT2_vc0_bound : ‖qT2 vc0‖ ≤ (2653207251 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT2
  rw [vc0_p5, vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT3_vc0_bound : ‖qT3 vc0‖ ≤ (1819210309 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT3
  rw [vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT4_vc0_bound : ‖qT4 vc0‖ ≤ (1178099953 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT4
  rw [vc0_p3, vc0_p2]
  unfold vc0
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT5_vc0_bound : ‖qT5 vc0‖ ≤ (8757 / 40 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT5
  rw [vc0_p2]
  unfold vc0
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT6_vc0_bound : ‖qT6 vc0‖ ≤ (11300719 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT6
  unfold vc0
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc0_abs : ‖qT0 vc0‖ ≤ (3181625269 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT0
  rw [vc0_p7, vc0_p6, vc0_p5, vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc0_re_hi : (qT0 vc0).re ≤ (-24715449 / 50000000000000 : ℝ) := by
  unfold qT0
  rw [vc0_p7, vc0_p6, vc0_p5, vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc0_re_lo : (-49430899 / 100000000000000 : ℝ) ≤ (qT0 vc0).re := by
  unfold qT0
  rw [vc0_p7, vc0_p6, vc0_p5, vc0_p4, vc0_p3, vc0_p2]
  unfold vc0
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem Q_var_vc0 : ∀ w : ℂ, ‖w - vc0‖ ≤ (1 / 1000000 : ℝ) →
    ‖Q.eval w - qT0 vc0‖ ≤ (5307418140421796100171925022601439 / 1000000000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  refine le_trans (Q_var_on_disk (v := vc0) (by norm_num)
    qT1_vc0_bound qT2_vc0_bound qT3_vc0_bound qT4_vc0_bound qT5_vc0_bound
    qT6_vc0_bound qT7_bound w hw) (by norm_num)

/-- `H_s < 0` on the whole disk about `vc0`: this critical value lies outside
the lemniscate.  Margin `4.8899e-07`. -/
theorem Hs_neg_vc0 : ∀ w : ℂ, ‖w - vc0‖ ≤ (1 / 1000000 : ℝ) → Hs w < 0 :=
  Hs_neg_on_disk Q_var_vc0 qT0_vc0_re_hi (by norm_num)

/-! ### Centre 1: the critical point near `-3.18983-0.50000 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 9.525e-11 against the radius,
contraction ≤ 2.057e-06 against `1/2`. -/

def vc1 : ℂ := (((-6379655169 / 2000000000 : ℚ) : ℂ) + (((-5000000021 / 10000000000 : ℚ) : ℂ)) * Complex.I)

theorem vc1_p2 : vc1 ^ 2 = (((31015625052303451987 / 3125000000000000000 : ℚ) : ℂ) + (((31898275978972758549 / 10000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 2 = vc1 ^ 1 * vc1 := by ring
  rw [hs]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc1_p3 : vc1 ^ 3 = (((-3006412502390370216903098003319 / 100000000000000000000000000000 : ℚ) : ℂ) + (((-7568750045391578536216879612157 / 500000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 3 = vc1 ^ 2 * vc1 := by ring
  rw [hs, vc1_p2]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc1_p4 : vc1 ^ 4 = (((220826563069811055808964980701675732896239 / 2500000000000000000000000000000000000000 : ℚ) : ℂ) + (((989344967578716910505605223348565286863 / 15625000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 4 = vc1 ^ 3 * vc1 := by ring
  rw [hs, vc1_p3]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc1_p5 : vc1 ^ 5 = (((-250100425812678017230243263215578736069007720847491 / 1000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-6153476609056572105506692888783902476071989986698619 / 25000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 5 = vc1 ^ 4 * vc1 := by ring
  rw [hs, vc1_p4]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc1_p6 : vc1 ^ 6 = (((5271153941050411655522736984469585705197486842021741957287543 / 7812500000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((22754784763932923793702130020795388297412765021595585818749083 / 25000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 6 = vc1 ^ 5 * vc1 := by ring
  rw [hs, vc1_p5]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc1_p7 : vc1 ^ 7 = (((-424276387488356581112633572628260170755459534206569885263845697514425529 / 250000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-4050884323022818707879129360850140894271366136723211827906450849522615123 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc1 ^ 7 = vc1 ^ 6 * vc1 := by ring
  rw [hs, vc1_p6]
  unfold vc1
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem qpT0_vc1_bound : ‖qpT0 vc1‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc1_p6, vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc1_bound : ‖qpT2 vc1‖ ≤ (10915261941 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc1_bound : ‖qpT3 vc1‖ ≤ (4712399839 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc1_p3, vc1_p2]
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc1_bound : ‖qpT4 vc1‖ ≤ (1094625003 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc1_p2]
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc1_bound : ‖qpT5 vc1‖ ≤ (135608629 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc1_lower : (5306414559 / 500000 : ℝ) ≤ ‖qpT1 vc1‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc1`. -/
theorem crit_loc_1 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc1 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc1 t)
    qpT0_vc1_bound qpT2_vc1_bound qpT3_vc1_bound qpT4_vc1_bound qpT5_vc1_bound
    qpT6_bound qpT1_vc1_lower (by norm_num) (by norm_num) (by norm_num)

theorem qT1_vc1_bound : ‖qT1 vc1‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT1
  rw [vc1_p6, vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT2_vc1_bound : ‖qT2 vc1‖ ≤ (33165091 / 6250 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT2
  rw [vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT3_vc1_bound : ‖qT3 vc1‖ ≤ (3638420647 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT3
  rw [vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT4_vc1_bound : ‖qT4 vc1‖ ≤ (29452499 / 25000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT4
  rw [vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT5_vc1_bound : ‖qT5 vc1‖ ≤ (218925001 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT5
  rw [vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT6_vc1_bound : ‖qT6 vc1‖ ≤ (22601439 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT6
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc1_abs : ‖qT0 vc1‖ ≤ (6363250651 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT0
  rw [vc1_p7, vc1_p6, vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc1_re_hi : (qT0 vc1).re ≤ (-24715453 / 50000000000000 : ℝ) := by
  unfold qT0
  rw [vc1_p7, vc1_p6, vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc1_re_lo : (-49430907 / 100000000000000 : ℝ) ≤ (qT0 vc1).re := by
  unfold qT0
  rw [vc1_p7, vc1_p6, vc1_p5, vc1_p4, vc1_p3, vc1_p2]
  unfold vc1
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem Q_var_vc1 : ∀ w : ℂ, ‖w - vc1‖ ≤ (1 / 1000000 : ℝ) →
    ‖Q.eval w - qT0 vc1‖ ≤ (33171363740136406876118281397509 / 6250000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  refine le_trans (Q_var_on_disk (v := vc1) (by norm_num)
    qT1_vc1_bound qT2_vc1_bound qT3_vc1_bound qT4_vc1_bound qT5_vc1_bound
    qT6_vc1_bound qT7_bound w hw) (by norm_num)

/-- `H_s < 0` on the whole disk about `vc1`: this critical value lies outside
the lemniscate.  Margin `4.8899e-07`. -/
theorem Hs_neg_vc1 : ∀ w : ℂ, ‖w - vc1‖ ≤ (1 / 1000000 : ℝ) → Hs w < 0 :=
  Hs_neg_on_disk Q_var_vc1 qT0_vc1_re_hi (by norm_num)

/-! ### Centre 2: the critical point near `+0.00000+0.82325 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 2.646e-09 against the radius,
contraction ≤ 3.012e-06 against `1/2`. -/

def vc2 : ℂ := (((39 / 10000000000 : ℚ) : ℂ) + (((4116237331 / 5000000000 : ℚ) : ℂ)) * Complex.I)

theorem vc2_p2 : vc2 ^ 2 = (((-67773639060472012723 / 100000000000000000000 : ℚ) : ℂ) + (((160533255909 / 25000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc2 ^ 2 = vc2 ^ 1 * vc2 := by ring
  rw [hs]
  unfold vc2
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc2_p3 : vc2 ^ 3 = (((-7929515770075225607229 / 1000000000000000000000000000000 : ℚ) : ℂ) + (((-278972383158434652729525601411 / 500000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc2 ^ 3 = vc2 ^ 2 * vc2 := by ring
  rw [hs, vc2_p2]
  unfold vc2
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc2_p4 : vc2 ^ 4 = (((4593266151499137311106062272858939214233 / 10000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-10879922943178951944793662930207 / 1250000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc2 ^ 4 = vc2 ^ 3 * vc2 := by ring
  rw [hs, vc2_p3]
  unfold vc2
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc2_p5 : vc2 ^ 5 = (((895686899542331856070972051770281044675359 / 100000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((18906973604019448917001755292036170302874264019831 / 50000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc2 ^ 5 = vc2 ^ 4 * vc2 := by ring
  rw [hs, vc2_p4]
  unfold vc2
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc2_p6 : vc2 ^ 6 = (((-311302362260385834197051500751481978043948469589353203705243 / 1000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((2212115911670275854256461300671953057133243894200119 / 250000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc2 ^ 6 = vc2 ^ 5 * vc2 := by ring
  rw [hs, vc2_p5]
  unfold vc2
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc2_p7 : vc2 ^ 7 = (((-84985544897085351808551898559569465611325465181459528644043589 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-1281394404764685540640438687241308039594241596751675440842945009417151 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc2 ^ 7 = vc2 ^ 6 * vc2 := by ring
  rw [hs, vc2_p6]
  unfold vc2
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem qpT0_vc2_bound : ‖qpT0 vc2‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc2_p6, vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc2_bound : ‖qpT2 vc2‖ ≤ (569596331 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc2_bound : ‖qpT3 vc2‖ ≤ (19528067 / 250000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc2_p3, vc2_p2]
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc2_bound : ‖qpT4 vc2‖ ≤ (35581161 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc2_p2]
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc2_bound : ‖qpT5 vc2‖ ≤ (17288197 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc2_lower : (378202597 / 1000000 : ℝ) ≤ ‖qpT1 vc2‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc2`. -/
theorem crit_loc_2 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc2 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc2 t)
    qpT0_vc2_bound qpT2_vc2_bound qpT3_vc2_bound qpT4_vc2_bound qpT5_vc2_bound
    qpT6_bound qpT1_vc2_lower (by norm_num) (by norm_num) (by norm_num)

theorem qT1_vc2_bound : ‖qT1 vc2‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT1
  rw [vc2_p6, vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT2_vc2_bound : ‖qT2 vc2‖ ≤ (189101299 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT2
  rw [vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT3_vc2_bound : ‖qT3 vc2‖ ≤ (47466361 / 250000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT3
  rw [vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT4_vc2_bound : ‖qT4 vc2‖ ≤ (19528067 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT4
  rw [vc2_p3, vc2_p2]
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT5_vc2_bound : ‖qT5 vc2‖ ≤ (2846493 / 200000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT5
  rw [vc2_p2]
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT6_vc2_bound : ‖qT6 vc2‖ ≤ (5762733 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT6
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc2_abs : ‖qT0 vc2‖ ≤ (5980521 / 25000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT0
  rw [vc2_p7, vc2_p6, vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc2_re_hi : (qT0 vc2).re ≤ (355686791 / 100000000000000 : ℝ) := by
  unfold qT0
  rw [vc2_p7, vc2_p6, vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc2_re_lo : (35568679 / 10000000000000 : ℝ) ≤ (qT0 vc2).re := by
  unfold qT0
  rw [vc2_p7, vc2_p6, vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem Q_var_vc2 : ∀ w : ℂ, ‖w - vc2‖ ≤ (1 / 1000000 : ℝ) →
    ‖Q.eval w - qT0 vc2‖ ≤ (95050744432731764040616235381367 / 500000000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  refine le_trans (Q_var_on_disk (v := vc2) (by norm_num)
    qT1_vc2_bound qT2_vc2_bound qT3_vc2_bound qT4_vc2_bound qT5_vc2_bound
    qT6_vc2_bound qT7_bound w hw) (by norm_num)

theorem Q_abs_vc2 : ∀ w : ℂ, ‖w - vc2‖ ≤ (1 / 1000000 : ℝ) → ‖Q.eval w‖ ≤ (119610420000095050744432731764040616235381367 / 500000000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  have h1 := Q_var_vc2 w hw
  have h2 : ‖Q.eval w‖ ≤ ‖Q.eval w - qT0 vc2‖ + ‖qT0 vc2‖ := by
    calc ‖Q.eval w‖ = ‖(Q.eval w - qT0 vc2) + qT0 vc2‖ := by ring_nf
      _ ≤ ‖Q.eval w - qT0 vc2‖ + ‖qT0 vc2‖ := norm_add_le _ _
  linarith [qT0_vc2_abs]

/-- `H_s > 0` on the whole disk about `vc2`: this is the interior critical
point `q_s`.  Margin `3.5567e-06`. -/
theorem Hs_pos_vc2 : ∀ w : ℂ, ‖w - vc2‖ ≤ (1 / 1000000 : ℝ) → 0 < Hs w :=
  Hs_pos_on_disk (by norm_num) Q_var_vc2 qT0_vc2_re_lo Q_abs_vc2 (by norm_num)

/-! ### Centre 3: the critical point near `+0.00000+1.80786 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 2.315e-08 against the radius,
contraction ≤ 2.331e-05 against `1/2`. -/

def vc3 : ℂ := (((1137 / 5000000000 : ℚ) : ℂ) + (((9039295429 / 5000000000 : ℚ) : ℂ)) * Complex.I)

theorem vc3_p2 : vc3 ^ 2 = (((-10213607731592375159 / 3125000000000000000 : ℚ) : ℂ) + (((10277678902773 / 12500000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 2 = vc3 ^ 1 * vc3 := by ring
  rw [hs]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc3_p3 : vc3 ^ 3 = (((-139354463889847836547749 / 62500000000000000000000000000 : ℚ) : ℂ) + (((-369295270727116376943094939943 / 62500000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 3 = vc3 ^ 2 * vc3 := by ring
  rw [hs, vc3_p2]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc3_p4 : vc3 ^ 4 = (((1669084526317391063213658163374817314967 / 156250000000000000000000000000000000000 : ℚ) : ℂ) + (((-104972180704186151812244101415907 / 19531250000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 4 = vc3 ^ 3 * vc3 := by ring
  rw [hs, vc3_p3]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc3_p5 : vc3 ^ 5 = (((9488745532114968704806074709045331871030303 / 781250000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((15087348129354468413956985009325637196544777295771 / 781250000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 5 = vc3 ^ 4 * vc3 := by ring
  rw [hs, vc3_p4]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc3_p6 : vc3 ^ 6 = (((-17047374622674344793917029959750173772036924432643552484531 / 488281250000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((51462944469233519951250346702254611414031823606838307 / 1953125000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 6 = vc3 ^ 5 * vc3 := by ring
  rw [hs, vc3_p5]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc3_p7 : vc3 ^ 7 = (((-542720218487546308151652214037299123264253021909490678306845691 / 9765625000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-616385022012704705237035105169518627393915772679675375255529670880137 / 9765625000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc3 ^ 7 = vc3 ^ 6 * vc3 := by ring
  rw [hs, vc3_p6]
  unfold vc3
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem qpT0_vc3_bound : ‖qpT0 vc3‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc3_p6, vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc3_bound : ‖qpT2 vc3‖ ≤ (503799177 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc3_bound : ‖qpT3 vc3‖ ≤ (827221407 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc3_p3, vc3_p2]
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc3_bound : ‖qpT4 vc3‖ ≤ (17158861 / 50000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc3_p2]
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc3_bound : ‖qpT5 vc3‖ ≤ (37965041 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc3_lower : (43220003 / 1000000 : ℝ) ≤ ‖qpT1 vc3‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc3`. -/
theorem crit_loc_3 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc3 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc3 t)
    qpT0_vc3_bound qpT2_vc3_bound qpT3_vc3_bound qpT4_vc3_bound qpT5_vc3_bound
    qpT6_bound qpT1_vc3_lower (by norm_num) (by norm_num) (by norm_num)

theorem qT1_vc3_bound : ‖qT1 vc3‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT1
  rw [vc3_p6, vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT2_vc3_bound : ‖qT2 vc3‖ ≤ (10805001 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT2
  rw [vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT3_vc3_bound : ‖qT3 vc3‖ ≤ (167933059 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT3
  rw [vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT4_vc3_bound : ‖qT4 vc3‖ ≤ (25850669 / 125000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT4
  rw [vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT5_vc3_bound : ‖qT5 vc3‖ ≤ (17158861 / 250000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT5
  rw [vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT6_vc3_bound : ‖qT6 vc3‖ ≤ (6327507 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT6
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc3_abs : ‖qT0 vc3‖ ≤ (49864307 / 250000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT0
  rw [vc3_p7, vc3_p6, vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc3_re_hi : (qT0 vc3).re ≤ (-186589 / 2500000000000 : ℝ) := by
  unfold qT0
  rw [vc3_p7, vc3_p6, vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc3_re_lo : (-7463561 / 100000000000000 : ℝ) ≤ (qT0 vc3).re := by
  unfold qT0
  rw [vc3_p7, vc3_p6, vc3_p5, vc3_p4, vc3_p3, vc3_p2]
  unfold vc3
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem Q_var_vc3 : ∀ w : ℂ, ‖w - vc3‖ ≤ (1 / 1000000 : ℝ) →
    ‖Q.eval w - qT0 vc3‖ ≤ (4522033986653161084127091331003 / 200000000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  refine le_trans (Q_var_on_disk (v := vc3) (by norm_num)
    qT1_vc3_bound qT2_vc3_bound qT3_vc3_bound qT4_vc3_bound qT5_vc3_bound
    qT6_vc3_bound qT7_bound w hw) (by norm_num)

/-- `H_s < 0` on the whole disk about `vc3`: this critical value lies outside
the lemniscate.  Margin `7.4603e-08`. -/
theorem Hs_neg_vc3 : ∀ w : ℂ, ‖w - vc3‖ ≤ (1 / 1000000 : ℝ) → Hs w < 0 :=
  Hs_neg_on_disk Q_var_vc3 qT0_vc3_re_hi (by norm_num)

/-! ### Centre 4: the critical point near `-0.00000+1.88386 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 2.072e-08 against the radius,
contraction ≤ 2.917e-05 against `1/2`. -/

def vc4 : ℂ := (((-453 / 2000000000 : ℚ) : ℂ) + (((3767718291 / 2000000000 : ℚ) : ℂ)) * Complex.I)

theorem vc4_p2 : vc4 ^ 2 = (((-887231320020984717 / 250000000000000000 : ℚ) : ℂ) + (((-1706776385823 / 2000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 2 = vc4 ^ 1 * vc4 := by ring
  rw [hs]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc4_p3 : vc4 ^ 3 = (((9645978911268238802901 / 4000000000000000000000000000 : ℚ) : ℂ) + (((-26742701382328335806876091357 / 4000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 3 = vc4 ^ 2 * vc4 := by ring
  rw [hs, vc4_p2]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc4_p4 : vc4 ^ 4 = (((50379482574472542679355244232089098367 / 4000000000000000000000000000000000000 : ℚ) : ℂ) + (((1514305465774385795798778467091 / 250000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 4 = vc4 ^ 3 * vc4 := by ring
  rw [hs, vc4_p3]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc4_p5 : vc4 ^ 5 = (((-114109528031186907307694303011787597743947 / 8000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((189815697986944993044268969031766395512714655229 / 8000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 5 = vc4 ^ 4 * vc4 := by ring
  rw [hs, vc4_p4]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc4_p6 : vc4 ^ 6 = (((-44698254826518302367972614979730526430820686861767755353 / 1000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-257959533564283105475987616732699348897039592626657 / 8000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 6 = vc4 ^ 5 * vc4 := by ring
  rw [hs, vc4_p5]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc4_p7 : vc4 ^ 7 = (((1133905328439280208585693561539832422428460918077690658482459 / 16000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-1347283458285099461755927652123069767085316471437075724564630218163 / 16000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc4 ^ 7 = vc4 ^ 6 * vc4 := by ring
  rw [hs, vc4_p6]
  unfold vc4
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem qpT0_vc4_bound : ‖qpT0 vc4‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc4_p6, vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc4_bound : ‖qpT2 vc4‖ ≤ (704635793 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc4_bound : ‖qpT3 vc4‖ ≤ (935994549 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc4_p3, vc4_p2]
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc4_bound : ‖qpT4 vc4‖ ≤ (74527431 / 200000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc4_p2]
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc4_bound : ‖qpT5 vc4‖ ≤ (15824417 / 200000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc4_lower : (24153503 / 500000 : ℝ) ≤ ‖qpT1 vc4‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc4`. -/
theorem crit_loc_4 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc4 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc4 t)
    qpT0_vc4_bound qpT2_vc4_bound qpT3_vc4_bound qpT4_vc4_bound qpT5_vc4_bound
    qpT6_bound qpT1_vc4_lower (by norm_num) (by norm_num) (by norm_num)

theorem qT1_vc4_bound : ‖qT1 vc4‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT1
  rw [vc4_p6, vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT2_vc4_bound : ‖qT2 vc4‖ ≤ (754797 / 31250 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT2
  rw [vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT3_vc4_bound : ‖qT3 vc4‖ ≤ (117439299 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT3
  rw [vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT4_vc4_bound : ‖qT4 vc4‖ ≤ (116999319 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT4
  rw [vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT5_vc4_bound : ‖qT5 vc4‖ ≤ (74527431 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT5
  rw [vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT6_vc4_bound : ‖qT6 vc4‖ ≤ (2637403 / 200000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT6
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc4_abs : ‖qT0 vc4‖ ≤ (199501253 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT0
  rw [vc4_p7, vc4_p6, vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc4_re_hi : (qT0 vc4).re ≤ (-86373977 / 100000000000000 : ℝ) := by
  unfold qT0
  rw [vc4_p7, vc4_p6, vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc4_re_lo : (-43186989 / 50000000000000 : ℝ) ≤ (qT0 vc4).re := by
  unfold qT0
  rw [vc4_p7, vc4_p6, vc4_p5, vc4_p4, vc4_p3, vc4_p2]
  unfold vc4
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem Q_var_vc4 : ∀ w : ℂ, ‖w - vc4‖ ≤ (1 / 1000000 : ℝ) →
    ‖Q.eval w - qT0 vc4‖ ≤ (3144217359853999839065930523377 / 125000000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  refine le_trans (Q_var_on_disk (v := vc4) (by norm_num)
    qT1_vc4_bound qT2_vc4_bound qT3_vc4_bound qT4_vc4_bound qT5_vc4_bound
    qT6_vc4_bound qT7_bound w hw) (by norm_num)

/-- `H_s < 0` on the whole disk about `vc4`: this critical value lies outside
the lemniscate.  Margin `8.6370e-07`. -/
theorem Hs_neg_vc4 : ∀ w : ℂ, ‖w - vc4‖ ≤ (1 / 1000000 : ℝ) → Hs w < 0 :=
  Hs_neg_on_disk Q_var_vc4 qT0_vc4_re_hi (by norm_num)

/-! ### Centre 5: the critical point near `+0.00000-3.51497 i`

Rounded to denominator `10^10`; disk radius `10^-6` in the scaled coordinate.
Exact margins: residual/`|Q''|` ≤ 6.040e-11 against the radius,
contraction ≤ 1.833e-06 against `1/2`. -/

def vc5 : ℂ := (((11 / 10000000000 : ℚ) : ℂ) + (((-2196853561 / 625000000 : ℚ) : ℂ)) * Complex.I)

theorem vc5_p2 : vc5 ^ 2 = (((-247099677106093092891 / 20000000000000000000 : ℚ) : ℂ) + (((-24165389171 / 3125000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 2 = vc5 ^ 1 * vc5 := by ring
  rw [hs]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc5_p3 : vc5 ^ 3 = (((-40771446722505360329677 / 1000000000000000000000000000000 : ℚ) : ℂ) + (((2714209027862353929043847112493 / 62500000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 3 = vc5 ^ 2 * vc5 := by ring
  rw [hs, vc5_p2]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc5_p4 : vc5 ^ 4 = (((1526456260648386673948267200732713583592241 / 10000000000000000000000000000000000000000 : ℚ) : ℂ) + (((5971259861297178645066068483361 / 31250000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 4 = vc5 ^ 3 * vc5 := by ring
  rw [hs, vc5_p3]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc5_p5 : vc5 ^ 5 = (((83955094335661267100043663063120237763942171 / 100000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-3353400871916152432254519560223784343393150746480781 / 6250000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 5 = vc5 ^ 4 * vc5 := by ring
  rw [hs, vc5_p4]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc5_p6 : vc5 ^ 6 = (((-377186849122790623263217003237700071473883591330440409164377643 / 200000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((-110662228773233030336651389809080744940103846985354761 / 31250000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 6 = vc5 ^ 5 * vc5 := by ring
  rw [hs, vc5_p5]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem vc5_p7 : vc5 ^ 7 = (((-145216936912274390098558476051124713996061929918476991938231577917 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ) + (((4143121363288861532431469536381322989930447854768957314173015663188878873 / 625000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℂ)) * Complex.I) := by
  have hs : vc5 ^ 7 = vc5 ^ 6 * vc5 := by ring
  rw [hs, vc5_p6]
  unfold vc5
  rw [Complex.ext_iff]
  constructor <;>
    (simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]; push_cast; norm_num)

theorem qpT0_vc5_bound : ‖qpT0 vc5‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT0
  rw [vc5_p6, vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT2_vc5_bound : ‖qpT2 vc5‖ ≤ (1926245639 / 125000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT2
  rw [vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT3_vc5_bound : ‖qpT3 vc5‖ ≤ (6079828223 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT3
  rw [vc5_p3, vc5_p2]
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT4_vc5_bound : ‖qpT4 vc5‖ ≤ (259454661 / 200000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT4
  rw [vc5_p2]
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT5_vc5_bound : ‖qpT5 vc5‖ ≤ (1845357 / 12500 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qpT5
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qpT1_vc5_lower : (16812014601 / 1000000 : ℝ) ≤ ‖qpT1 vc5‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qpT1
  rw [vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qp0_Q, qp1_Q, qp2_Q, qp3_Q, qp4_Q, qp5_Q, qp6_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

/-- Exactly one critical point of `Q_s` in the disk of radius `10⁻⁶` about `vc5`. -/
theorem crit_loc_5 :
    ∃! z : ℂ, z ∈ Metric.closedBall vc5 ((1 / 1000000 : ℝ)) ∧ (Polynomial.derivative Q).eval z = 0 :=
  newton_disk (fun z => (Polynomial.derivative Q).eval z) (by norm_num)
    (fun t => Qp_taylor vc5 t)
    qpT0_vc5_bound qpT2_vc5_bound qpT3_vc5_bound qpT4_vc5_bound qpT5_vc5_bound
    qpT6_bound qpT1_vc5_lower (by norm_num) (by norm_num) (by norm_num)

theorem qT1_vc5_bound : ‖qT1 vc5‖ ≤ (1 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT1
  rw [vc5_p6, vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT2_vc5_bound : ‖qT2 vc5‖ ≤ (8406007301 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT2
  rw [vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT3_vc5_bound : ‖qT3 vc5‖ ≤ (2568327519 / 500000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT3
  rw [vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT4_vc5_bound : ‖qT4 vc5‖ ≤ (23749329 / 15625 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT4
  rw [vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT5_vc5_bound : ‖qT5 vc5‖ ≤ (259454661 / 1000000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT5
  rw [vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT6_vc5_bound : ‖qT6 vc5‖ ≤ (615119 / 25000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT6
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc5_abs : ‖qT0 vc5‖ ≤ (3341170127 / 250000 : ℝ) := by
  apply norm_le_of_normSq_le (by norm_num)
  unfold qT0
  rw [vc5_p7, vc5_p6, vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc5_re_hi : (qT0 vc5).re ≤ (-19464601 / 12500000000000 : ℝ) := by
  unfold qT0
  rw [vc5_p7, vc5_p6, vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem qT0_vc5_re_lo : (-155716809 / 100000000000000 : ℝ) ≤ (qT0 vc5).re := by
  unfold qT0
  rw [vc5_p7, vc5_p6, vc5_p5, vc5_p4, vc5_p3, vc5_p2]
  unfold vc5
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem Q_var_vc5 : ∀ w : ℂ, ‖w - vc5‖ ≤ (1 / 1000000 : ℝ) →
    ‖Q.eval w - qT0 vc5‖ ≤ (8407012437656557957315454685604761 / 1000000000000000000000000000000000000000000 : ℝ) := by
  intro w hw
  refine le_trans (Q_var_on_disk (v := vc5) (by norm_num)
    qT1_vc5_bound qT2_vc5_bound qT3_vc5_bound qT4_vc5_bound qT5_vc5_bound
    qT6_vc5_bound qT7_bound w hw) (by norm_num)

/-- `H_s < 0` on the whole disk about `vc5`: this critical value lies outside
the lemniscate.  Margin `1.5488e-06`. -/
theorem Hs_neg_vc5 : ∀ w : ℂ, ‖w - vc5‖ ≤ (1 / 1000000 : ℝ) → Hs w < 0 :=
  Hs_neg_on_disk Q_var_vc5 qT0_vc5_re_hi (by norm_num)

end Erdos1041.Counterexample.S4Proofs
-- END GENERATED

/-! ## Assembly of `s4_instance_critical`

Hand-authored; regenerate with
`./repo-python formal_math/erdos1041_external_counterexample/emit_s4_assembly.py`. -/

noncomputable section
open scoped ComplexConjugate NNReal
namespace Erdos1041.Counterexample.S4Proofs

set_option maxHeartbeats 4000000

/-! ### The six disks are pairwise disjoint

The centres are more than `2·10⁻⁶` apart (in fact more than `0.07`), so the six
closed disks of radius `10⁻⁶` are disjoint and the six localised zeros are
distinct. -/

theorem lt_norm_of_lt_normSq {z : ℂ} {m : ℝ} (hm : 0 ≤ m)
    (h : m ^ 2 < Complex.normSq z) : m < ‖z‖ := by
  have h2 : m ^ 2 < ‖z‖ ^ 2 := by rwa [← Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg z, hm, h2]

theorem sep_01 : (2 / 10 ^ 6 : ℝ) < ‖vc0 - vc1‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc0 vc1
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_02 : (2 / 10 ^ 6 : ℝ) < ‖vc0 - vc2‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc0 vc2
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_03 : (2 / 10 ^ 6 : ℝ) < ‖vc0 - vc3‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc0 vc3
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_04 : (2 / 10 ^ 6 : ℝ) < ‖vc0 - vc4‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc0 vc4
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_05 : (2 / 10 ^ 6 : ℝ) < ‖vc0 - vc5‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc0 vc5
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_12 : (2 / 10 ^ 6 : ℝ) < ‖vc1 - vc2‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc1 vc2
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_13 : (2 / 10 ^ 6 : ℝ) < ‖vc1 - vc3‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc1 vc3
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_14 : (2 / 10 ^ 6 : ℝ) < ‖vc1 - vc4‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc1 vc4
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_15 : (2 / 10 ^ 6 : ℝ) < ‖vc1 - vc5‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc1 vc5
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_23 : (2 / 10 ^ 6 : ℝ) < ‖vc2 - vc3‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc2 vc3
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_24 : (2 / 10 ^ 6 : ℝ) < ‖vc2 - vc4‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc2 vc4
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_25 : (2 / 10 ^ 6 : ℝ) < ‖vc2 - vc5‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc2 vc5
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_34 : (2 / 10 ^ 6 : ℝ) < ‖vc3 - vc4‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc3 vc4
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_35 : (2 / 10 ^ 6 : ℝ) < ‖vc3 - vc5‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc3 vc5
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

theorem sep_45 : (2 / 10 ^ 6 : ℝ) < ‖vc4 - vc5‖ := by
  apply lt_norm_of_lt_normSq (by norm_num)
  unfold vc4 vc5
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.I_re, Complex.I_im]
  push_cast
  norm_num

/-! ### The six critical points, extracted from the localisation certificates -/

noncomputable def zc0 : ℂ := crit_loc_0.choose

theorem zc0_mem : ‖zc0 - vc0‖ ≤ 1 / 1000000 := by
  have h := crit_loc_0.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h

theorem zc0_root : (Polynomial.derivative Q).eval zc0 = 0 :=
  crit_loc_0.choose_spec.1.2

theorem zc0_uniq : ∀ y : ℂ, ‖y - vc0‖ ≤ 1 / 1000000 →
    (Polynomial.derivative Q).eval y = 0 → y = zc0 := by
  intro y h1 h2
  refine crit_loc_0.choose_spec.2 y ⟨?_, h2⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact h1

noncomputable def zc1 : ℂ := crit_loc_1.choose

theorem zc1_mem : ‖zc1 - vc1‖ ≤ 1 / 1000000 := by
  have h := crit_loc_1.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h

theorem zc1_root : (Polynomial.derivative Q).eval zc1 = 0 :=
  crit_loc_1.choose_spec.1.2

theorem zc1_uniq : ∀ y : ℂ, ‖y - vc1‖ ≤ 1 / 1000000 →
    (Polynomial.derivative Q).eval y = 0 → y = zc1 := by
  intro y h1 h2
  refine crit_loc_1.choose_spec.2 y ⟨?_, h2⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact h1

noncomputable def zc2 : ℂ := crit_loc_2.choose

theorem zc2_mem : ‖zc2 - vc2‖ ≤ 1 / 1000000 := by
  have h := crit_loc_2.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h

theorem zc2_root : (Polynomial.derivative Q).eval zc2 = 0 :=
  crit_loc_2.choose_spec.1.2

theorem zc2_uniq : ∀ y : ℂ, ‖y - vc2‖ ≤ 1 / 1000000 →
    (Polynomial.derivative Q).eval y = 0 → y = zc2 := by
  intro y h1 h2
  refine crit_loc_2.choose_spec.2 y ⟨?_, h2⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact h1

noncomputable def zc3 : ℂ := crit_loc_3.choose

theorem zc3_mem : ‖zc3 - vc3‖ ≤ 1 / 1000000 := by
  have h := crit_loc_3.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h

theorem zc3_root : (Polynomial.derivative Q).eval zc3 = 0 :=
  crit_loc_3.choose_spec.1.2

theorem zc3_uniq : ∀ y : ℂ, ‖y - vc3‖ ≤ 1 / 1000000 →
    (Polynomial.derivative Q).eval y = 0 → y = zc3 := by
  intro y h1 h2
  refine crit_loc_3.choose_spec.2 y ⟨?_, h2⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact h1

noncomputable def zc4 : ℂ := crit_loc_4.choose

theorem zc4_mem : ‖zc4 - vc4‖ ≤ 1 / 1000000 := by
  have h := crit_loc_4.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h

theorem zc4_root : (Polynomial.derivative Q).eval zc4 = 0 :=
  crit_loc_4.choose_spec.1.2

theorem zc4_uniq : ∀ y : ℂ, ‖y - vc4‖ ≤ 1 / 1000000 →
    (Polynomial.derivative Q).eval y = 0 → y = zc4 := by
  intro y h1 h2
  refine crit_loc_4.choose_spec.2 y ⟨?_, h2⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact h1

noncomputable def zc5 : ℂ := crit_loc_5.choose

theorem zc5_mem : ‖zc5 - vc5‖ ≤ 1 / 1000000 := by
  have h := crit_loc_5.choose_spec.1.1
  rw [Metric.mem_closedBall, dist_eq_norm] at h
  exact h

theorem zc5_root : (Polynomial.derivative Q).eval zc5 = 0 :=
  crit_loc_5.choose_spec.1.2

theorem zc5_uniq : ∀ y : ℂ, ‖y - vc5‖ ≤ 1 / 1000000 →
    (Polynomial.derivative Q).eval y = 0 → y = zc5 := by
  intro y h1 h2
  refine crit_loc_5.choose_spec.2 y ⟨?_, h2⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact h1

/-! ### The six critical points of `f`, and their distinctness -/

theorem rho_eps_ne_zero : ((ρ : ℂ) * (ε : ℂ)) ≠ 0 := mul_ne_zero rho_ne_zero eps_ne_zero

theorem ne_of_disks {v1 v2 z1 z2 : ℂ} {rr : ℝ}
    (h1 : ‖z1 - v1‖ ≤ rr) (h2 : ‖z2 - v2‖ ≤ rr) (hsep : 2 * rr < ‖v1 - v2‖) : z1 ≠ z2 := by
  intro h
  subst h
  have hcalc : ‖v1 - v2‖ ≤ 2 * rr := by
    have he : v1 - v2 = (z1 - v2) - (z1 - v1) := by ring
    rw [he]
    calc ‖(z1 - v2) - (z1 - v1)‖ ≤ ‖z1 - v2‖ + ‖z1 - v1‖ := norm_sub_le _ _
      _ ≤ rr + rr := by linarith
      _ = 2 * rr := by ring
  linarith

def cf0 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc0

theorem cf0_root : (Polynomial.derivative f).IsRoot cf0 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc0) = 0 := by
    rw [derivative_f_eval_rho_eps, zc0_root, mul_zero]
  exact h

def cf1 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc1

theorem cf1_root : (Polynomial.derivative f).IsRoot cf1 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc1) = 0 := by
    rw [derivative_f_eval_rho_eps, zc1_root, mul_zero]
  exact h

def cf2 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc2

theorem cf2_root : (Polynomial.derivative f).IsRoot cf2 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc2) = 0 := by
    rw [derivative_f_eval_rho_eps, zc2_root, mul_zero]
  exact h

def cf3 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc3

theorem cf3_root : (Polynomial.derivative f).IsRoot cf3 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc3) = 0 := by
    rw [derivative_f_eval_rho_eps, zc3_root, mul_zero]
  exact h

def cf4 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc4

theorem cf4_root : (Polynomial.derivative f).IsRoot cf4 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc4) = 0 := by
    rw [derivative_f_eval_rho_eps, zc4_root, mul_zero]
  exact h

def cf5 : ℂ := (ρ : ℂ) * (ε : ℂ) * zc5

theorem cf5_root : (Polynomial.derivative f).IsRoot cf5 := by
  have h : (Polynomial.derivative f).eval ((ρ : ℂ) * (ε : ℂ) * zc5) = 0 := by
    rw [derivative_f_eval_rho_eps, zc5_root, mul_zero]
  exact h

theorem cfne01 : cf0 ≠ cf1 := by
  intro h
  exact ne_of_disks zc0_mem zc1_mem (by have hs := sep_01; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne02 : cf0 ≠ cf2 := by
  intro h
  exact ne_of_disks zc0_mem zc2_mem (by have hs := sep_02; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne03 : cf0 ≠ cf3 := by
  intro h
  exact ne_of_disks zc0_mem zc3_mem (by have hs := sep_03; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne04 : cf0 ≠ cf4 := by
  intro h
  exact ne_of_disks zc0_mem zc4_mem (by have hs := sep_04; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne05 : cf0 ≠ cf5 := by
  intro h
  exact ne_of_disks zc0_mem zc5_mem (by have hs := sep_05; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne12 : cf1 ≠ cf2 := by
  intro h
  exact ne_of_disks zc1_mem zc2_mem (by have hs := sep_12; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne13 : cf1 ≠ cf3 := by
  intro h
  exact ne_of_disks zc1_mem zc3_mem (by have hs := sep_13; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne14 : cf1 ≠ cf4 := by
  intro h
  exact ne_of_disks zc1_mem zc4_mem (by have hs := sep_14; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne15 : cf1 ≠ cf5 := by
  intro h
  exact ne_of_disks zc1_mem zc5_mem (by have hs := sep_15; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne23 : cf2 ≠ cf3 := by
  intro h
  exact ne_of_disks zc2_mem zc3_mem (by have hs := sep_23; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne24 : cf2 ≠ cf4 := by
  intro h
  exact ne_of_disks zc2_mem zc4_mem (by have hs := sep_24; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne25 : cf2 ≠ cf5 := by
  intro h
  exact ne_of_disks zc2_mem zc5_mem (by have hs := sep_25; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne34 : cf3 ≠ cf4 := by
  intro h
  exact ne_of_disks zc3_mem zc4_mem (by have hs := sep_34; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne35 : cf3 ≠ cf5 := by
  intro h
  exact ne_of_disks zc3_mem zc5_mem (by have hs := sep_35; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

theorem cfne45 : cf4 ≠ cf5 := by
  intro h
  exact ne_of_disks zc4_mem zc5_mem (by have hs := sep_45; linarith)
    (mul_left_cancel₀ rho_eps_ne_zero h)

/-- The six critical points of `f` as a multiset. -/
def critMul : Multiset ℂ := {cf0, cf1, cf2, cf3, cf4, cf5}

theorem critMul_card : Multiset.card critMul = 6 := by decide +kernel

theorem critMul_nodup : critMul.Nodup := by
  simp only [critMul, Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
    Multiset.mem_singleton, Multiset.nodup_singleton, not_or]
  refine ⟨⟨cfne01, cfne02, cfne03, cfne04, cfne05⟩, ⟨cfne12, cfne13, cfne14, cfne15⟩,
    ⟨cfne23, cfne24, cfne25⟩, ⟨cfne34, cfne35⟩, cfne45, ?_⟩
  trivial

theorem critMul_root : ∀ z ∈ critMul, (Polynomial.derivative f).IsRoot z := by
  intro z hz
  simp only [critMul, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at hz
  rcases hz with h | h | h | h | h | h <;> subst h
  · exact cf0_root
  · exact cf1_root
  · exact cf2_root
  · exact cf3_root
  · exact cf4_root
  · exact cf5_root


/-! ### Exhaustion of `derivative f` -/

theorem derivative_f_ne_zero : Polynomial.derivative f ≠ 0 := by
  intro h
  have hd := derivative_f_natDegree
  rw [h] at hd
  simp at hd

theorem derivative_f_roots_eq : (Polynomial.derivative f).roots = critMul := by
  have hsub : critMul ⊆ (Polynomial.derivative f).roots := by
    intro z hz
    exact (Polynomial.mem_roots derivative_f_ne_zero).mpr (critMul_root z hz)
  have hle : critMul ≤ (Polynomial.derivative f).roots :=
    (Multiset.le_iff_subset critMul_nodup).mpr hsub
  obtain ⟨m, hm⟩ := Multiset.le_iff_exists_add.mp hle
  have hdeg := Polynomial.card_roots' (Polynomial.derivative f)
  rw [derivative_f_natDegree, hm, Multiset.card_add, critMul_card] at hdeg
  have hm0 : Multiset.card m = 0 := by omega
  rw [hm, Multiset.card_eq_zero.mp hm0, add_zero]

theorem derivative_f_roots_nodup : (Polynomial.derivative f).roots.Nodup := by
  rw [derivative_f_roots_eq]; exact critMul_nodup

theorem exists_crit_index {z : ℂ} (hz : (Polynomial.derivative f).IsRoot z) :
    z = cf0 ∨ z = cf1 ∨ z = cf2 ∨ z = cf3 ∨ z = cf4 ∨ z = cf5 := by
  have hm : z ∈ critMul := by
    rw [← derivative_f_roots_eq]
    exact (Polynomial.mem_roots derivative_f_ne_zero).mpr hz
  simpa only [critMul, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] using hm

/-! ### `H_s` decides membership of `Ω(f)` -/

theorem mem_omega_of_Hs_pos {w : ℂ} (h : 0 < Hs w) :
    ((ρ : ℂ) * (ε : ℂ) * w) ∈ Omega f := by
  have hid := one_sub_sq_norm_f_rho_eps w
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 14 := pow_pos rho_pos 14
  have h2 : (0 : ℝ) < (ε : ℝ) ^ 7 := pow_pos eps_pos 7
  have hpos : 0 < 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs w := by positivity
  have hlt : ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ ^ 2 < 1 := by linarith [hid, hpos]
  have hn := norm_nonneg (f.eval ((ρ : ℂ) * (ε : ℂ) * w))
  show ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ < 1
  nlinarith [hlt, hn]

theorem not_mem_omega_of_Hs_neg {w : ℂ} (h : Hs w < 0) :
    ((ρ : ℂ) * (ε : ℂ) * w) ∉ Omega f := by
  have hid := one_sub_sq_norm_f_rho_eps w
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 14 := pow_pos rho_pos 14
  have h2 : (0 : ℝ) < (ε : ℝ) ^ 7 := pow_pos eps_pos 7
  have hpp : (0 : ℝ) < 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 :=
    mul_pos (by linarith : (0 : ℝ) < 2 * (ρ : ℝ) ^ 14) h2
  have hneg : 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs w < 0 := mul_neg_of_pos_of_neg hpp h
  have hgt : 1 < ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ ^ 2 := by linarith [hid, hneg]
  have hn := norm_nonneg (f.eval ((ρ : ℂ) * (ε : ℂ) * w))
  intro hmem
  have hm2 : ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ < 1 := hmem
  nlinarith [hgt, hn, hm2]

/-! ### An upper bound for `H_s` on a disk -/

theorem Hs_le_on_disk {v : ℂ} {rr var reHi : ℝ}
    (hvar : ∀ w : ℂ, ‖w - v‖ ≤ rr → ‖Q.eval w - qT0 v‖ ≤ var)
    (hre : (qT0 v).re ≤ reHi) :
    ∀ w : ℂ, ‖w - v‖ ≤ rr → Hs w ≤ reHi + var + 1 / 10 ^ 11 := by
  intro w hw
  have hv := hvar w hw
  have hrele : (Q.eval w).re - (qT0 v).re ≤ var := by
    have hb := Complex.abs_re_le_norm (Q.eval w - qT0 v)
    simp only [Complex.sub_re] at hb
    calc (Q.eval w).re - (qT0 v).re ≤ |(Q.eval w).re - (qT0 v).re| := le_abs_self _
      _ ≤ ‖Q.eval w - qT0 v‖ := hb
      _ ≤ var := hv
  have hquad : 0 ≤ ((ε : ℝ) ^ 7 / 2) * Complex.normSq (Q.eval w) :=
    mul_nonneg (by linarith [eps_pow7_pos]) (Complex.normSq_nonneg _)
  unfold Hs
  linarith [K0_le, hrele, hre, hquad]


/-! ### The interior critical point and its data -/

def zs : ℂ := (ρ : ℂ) * (ε : ℂ) * zc2

theorem zs_eq_cf2 : zs = cf2 := rfl

theorem zs_crit : (Polynomial.derivative f).IsRoot zs := cf2_root

theorem Hs_zc2_pos : 0 < Hs zc2 := Hs_pos_vc2 zc2 zc2_mem

theorem Hs_zc2_le : Hs zc2 ≤ 3558 / 10 ^ 9 := by
  have h := Hs_le_on_disk Q_var_vc2 qT0_vc2_re_hi zc2 zc2_mem
  norm_num at h ⊢
  linarith

theorem zs_mem_omega : zs ∈ Omega f := mem_omega_of_Hs_pos Hs_zc2_pos

theorem norm_f_zs_lt_one : ‖f.eval ((ρ : ℂ) * (ε : ℂ) * zc2)‖ < 1 := zs_mem_omega

theorem norm_f_zs_pos : 0 < ‖f.eval zs‖ := by
  have hid := one_sub_sq_norm_f_rho_eps zc2
  have hr14 : (ρ : ℝ) ^ 14 ≤ 1 := rho_pow14_le_one
  have hr14p : (0 : ℝ) < (ρ : ℝ) ^ 14 := pow_pos rho_pos 14
  have he7 : ((ε : ℝ)) ^ 7 = 1 / 10 ^ 84 := by unfold ε s; push_cast; norm_num
  have hsmall : 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs zc2 < 1 := by
    rw [he7]
    nlinarith [Hs_zc2_le, Hs_zc2_pos, hr14, hr14p]
  have hn := norm_nonneg (f.eval ((ρ : ℂ) * (ε : ℂ) * zc2))
  have hsq : 0 < ‖f.eval ((ρ : ℂ) * (ε : ℂ) * zc2)‖ ^ 2 := by linarith [hid, hsmall]
  unfold zs
  nlinarith [hsq, hn]

theorem delta_pos : 0 < 1 - ‖f.eval zs‖ := by
  have hlt := norm_f_zs_lt_one
  unfold zs
  linarith

theorem delta_le : 1 - ‖f.eval zs‖ ≤ (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 * (36 / 5 / 10 ^ 6) := by
  have hid := one_sub_sq_norm_f_rho_eps zc2
  have hn := norm_nonneg (f.eval ((ρ : ℂ) * (ε : ℂ) * zc2))
  have hlt := norm_f_zs_lt_one
  have hstep : 1 - ‖f.eval ((ρ : ℂ) * (ε : ℂ) * zc2)‖
      ≤ 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs zc2 := by
    nlinarith [hid, hn, hlt]
  have hr7 : (0 : ℝ) < (ρ : ℝ) ^ 7 := pow_pos rho_pos 7
  have hr7le : (ρ : ℝ) ^ 7 ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  have he7 : (0 : ℝ) < (ε : ℝ) ^ 7 := pow_pos eps_pos 7
  have hp : (ρ : ℝ) ^ 7 * Hs zc2 ≤ 3558 / 10 ^ 9 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (ρ : ℝ) ^ 7) Hs_zc2_pos.le,
      Hs_zc2_le]
  have h14 : (ρ : ℝ) ^ 14 = (ρ : ℝ) ^ 7 * (ρ : ℝ) ^ 7 := by ring
  have hfin : 2 * (ρ : ℝ) ^ 14 * (ε : ℝ) ^ 7 * Hs zc2
      ≤ (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 * (36 / 5 / 10 ^ 6) := by
    rw [h14]
    nlinarith [hp, mul_pos hr7 he7, he7, hr7]
  unfold zs
  linarith [hstep, hfin]

/-! ### `zs` is localised at `ρε·(823247/10⁶)i` -/

theorem zs_loc : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
    < (ρ : ℝ) * (ε : ℝ) / 1000 := by
  have hrw : zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I
      = (ρ : ℂ) * (ε : ℂ) * (zc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I) := by
    unfold zs; ring
  have h2 : ‖vc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖ ≤ 5 / 10 ^ 7 := by
    apply norm_le_of_normSq_le (by norm_num)
    unfold vc2
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re,
      Complex.ratCast_im, Complex.I_re, Complex.I_im]
    push_cast
    norm_num
  have hc : ‖zc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖ < 1 / 1000 := by
    have he : zc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I
        = (zc2 - vc2) + (vc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I) := by ring
    rw [he]
    calc ‖(zc2 - vc2) + (vc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I)‖
        ≤ ‖zc2 - vc2‖ + ‖vc2 - (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖ :=
          norm_add_le _ _
      _ < 1 / 1000 := by linarith [zc2_mem, h2]
  rw [hrw, norm_mul, norm_mul, Complex.norm_ratCast, Complex.norm_ratCast,
    abs_of_pos rho_pos, abs_of_pos eps_pos]
  have hp : (0 : ℝ) < (ρ : ℝ) * (ε : ℝ) := mul_pos rho_pos eps_pos
  have hkey := mul_lt_mul_of_pos_left hc hp
  linarith [hkey]

/-! ### Simplicity and global uniqueness -/

theorem zs_simple : Polynomial.rootMultiplicity zs (Polynomial.derivative f) = 1 :=
  rootMultiplicity_eq_one_of_nodup derivative_f_ne_zero derivative_f_roots_nodup zs_crit

theorem crit_unique : ∀ c' ∈ Omega f, (Polynomial.derivative f).IsRoot c' → c' = zs := by
  intro c' hmem hroot
  rcases exists_crit_index hroot with h | h | h | h | h | h <;> subst h
  · exact absurd hmem (not_mem_omega_of_Hs_neg (Hs_neg_vc0 zc0 zc0_mem))
  · exact absurd hmem (not_mem_omega_of_Hs_neg (Hs_neg_vc1 zc1 zc1_mem))
  · rfl
  · exact absurd hmem (not_mem_omega_of_Hs_neg (Hs_neg_vc3 zc3 zc3_mem))
  · exact absurd hmem (not_mem_omega_of_Hs_neg (Hs_neg_vc4 zc4 zc4_mem))
  · exact absurd hmem (not_mem_omega_of_Hs_neg (Hs_neg_vc5 zc5 zc5_mem))

/-! ### The two remaining certificates

Both are exact-rational estimates verified in `instance_certificates_coarse.py`,
and both are now formalised: `s4_projection` below (Cauchy-Schwarz plus the
tightened Cayley enclosures) and `s4_disk_package` (the explicit identification
of `shiftQuad f zs`). -/

/-! ### Step 4: the disk criterion at `zs`

`shiftQuad f zs` is defined by division, so its coefficients are not writable.
It is identified with an explicit polynomial `Apoly` by `shiftQuad_spec`,
`Polynomial.funext` and cancellation of `X²`.  The Taylor data is transported
from `vc2` to `zc2` by the shift identity
`qTj (v + τ) = Σ_{m ≥ j} C(m,j) · qTm v · τ^{m-j}`, a `ring` identity with
`v` and `τ` atoms. -/

theorem qT1_eq_derivative (v : ℂ) : qT1 v = (Polynomial.derivative Q).eval v := by
  rw [derivative_Q_eval']
  unfold qT1 qq1 qq2 qq3 qq4 qq5 qq6 qq7 qp0 qp1 qp2 qp3 qp4 qp5 qp6
  ring

theorem qT1_zc2 : qT1 zc2 = 0 := by rw [qT1_eq_derivative]; exact zc2_root

theorem qT_shift2 (v τ : ℂ) : qT2 (v + τ)
    = qT2 v + (3 * qT3 v) * τ + (6 * qT4 v) * τ ^ 2 + (10 * qT5 v) * τ ^ 3
      + (15 * qT6 v) * τ ^ 4 + (21 * qT7) * τ ^ 5 := by
  unfold qT2 qT3 qT4 qT5 qT6 qT7; ring

theorem qT_shift3 (v τ : ℂ) : qT3 (v + τ)
    = qT3 v + (4 * qT4 v) * τ + (10 * qT5 v) * τ ^ 2 + (20 * qT6 v) * τ ^ 3
      + (35 * qT7) * τ ^ 4 := by
  unfold qT3 qT4 qT5 qT6 qT7; ring

theorem qT_shift4 (v τ : ℂ) : qT4 (v + τ)
    = qT4 v + (5 * qT5 v) * τ + (15 * qT6 v) * τ ^ 2 + (35 * qT7) * τ ^ 3 := by
  unfold qT4 qT5 qT6 qT7; ring

theorem qT_shift5 (v τ : ℂ) : qT5 (v + τ)
    = qT5 v + (6 * qT6 v) * τ + (21 * qT7) * τ ^ 2 := by
  unfold qT5 qT6 qT7; ring

theorem qT_shift6 (v τ : ℂ) : qT6 (v + τ) = qT6 v + (7 * qT7) * τ := by
  unfold qT6 qT7; ring

/-- A lower bound for `|Q''(vc2)/2|`; the generated block carries only upper bounds. -/
theorem qT2_vc2_lower : (94550649 / 500000 : ℝ) ≤ ‖qT2 vc2‖ := by
  apply le_norm_of_le_normSq (by norm_num)
  unfold qT2
  rw [vc2_p5, vc2_p4, vc2_p3, vc2_p2]
  unfold vc2
  simp only [qq0_Q, qq1_Q, qq2_Q, qq3_Q, qq4_Q, qq5_Q, qq6_Q, qq7_Q,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  norm_num

theorem tau_exists : ∃ τ : ℂ, ‖τ‖ ≤ 1 / 1000000 ∧ zc2 = vc2 + τ :=
  ⟨zc2 - vc2, zc2_mem, by ring⟩

theorem norm_shift_bound {τ : ℂ} (hτ : ‖τ‖ ≤ 1 / 1000000) {d : ℂ} {n : ℝ}
    (hd : ‖d‖ ≤ n) (k : ℕ) : ‖d * τ ^ k‖ ≤ n * (1 / 1000000 : ℝ) ^ k := by
  rw [norm_mul, norm_pow]
  exact mul_le_mul hd (pow_le_pow_left₀ (norm_nonneg _) hτ k) (by positivity)
    (le_trans (norm_nonneg _) hd)

theorem norm_const_mul {c : ℂ} {d : ℂ} {m n : ℝ} (hc : ‖c‖ = m) (hm : 0 ≤ m)
    (hd : ‖d‖ ≤ n) : ‖c * d‖ ≤ m * n := by
  rw [norm_mul, hc]
  exact mul_le_mul_of_nonneg_left hd hm

/-! #### Taylor bounds at `zc2` -/

theorem qT2_zc2_lower : (23637591 / 125000 : ℝ) ≤ ‖qT2 zc2‖ := by
  obtain ⟨τ, hτ, hzc⟩ := tau_exists
  rw [hzc, qT_shift2]
  have b3 : ‖(3 : ℂ) * qT3 vc2‖ ≤ 3 * (47466361 / 250000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT3_vc2_bound
  have b4 : ‖(6 : ℂ) * qT4 vc2‖ ≤ 6 * (19528067 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT4_vc2_bound
  have b5 : ‖(10 : ℂ) * qT5 vc2‖ ≤ 10 * (2846493 / 200000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT5_vc2_bound
  have b6 : ‖(15 : ℂ) * qT6 vc2‖ ≤ 15 * (5762733 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT6_vc2_bound
  have b7 : ‖(21 : ℂ) * qT7‖ ≤ 21 * (1 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT7_bound
  have t3 := norm_shift_bound hτ b3 1
  have t4 := norm_shift_bound hτ b4 2
  have t5 := norm_shift_bound hτ b5 3
  have t6 := norm_shift_bound hτ b6 4
  have t7 := norm_shift_bound hτ b7 5
  have htri : ‖qT2 vc2 + (3 * qT3 vc2) * τ + (6 * qT4 vc2) * τ ^ 2 + (10 * qT5 vc2) * τ ^ 3
      + (15 * qT6 vc2) * τ ^ 4 + (21 * qT7) * τ ^ 5‖
      ≥ ‖qT2 vc2‖ - (‖(3 * qT3 vc2) * τ‖ + ‖(6 * qT4 vc2) * τ ^ 2‖
        + ‖(10 * qT5 vc2) * τ ^ 3‖ + ‖(15 * qT6 vc2) * τ ^ 4‖ + ‖(21 * qT7) * τ ^ 5‖) := by
    have hsplit : qT2 vc2 + (3 * qT3 vc2) * τ + (6 * qT4 vc2) * τ ^ 2 + (10 * qT5 vc2) * τ ^ 3
        + (15 * qT6 vc2) * τ ^ 4 + (21 * qT7) * τ ^ 5
        = qT2 vc2 + ((3 * qT3 vc2) * τ + (6 * qT4 vc2) * τ ^ 2 + (10 * qT5 vc2) * τ ^ 3
          + (15 * qT6 vc2) * τ ^ 4 + (21 * qT7) * τ ^ 5) := by ring
    rw [hsplit]
    have hrest : ‖(3 * qT3 vc2) * τ + (6 * qT4 vc2) * τ ^ 2 + (10 * qT5 vc2) * τ ^ 3
        + (15 * qT6 vc2) * τ ^ 4 + (21 * qT7) * τ ^ 5‖
        ≤ ‖(3 * qT3 vc2) * τ‖ + ‖(6 * qT4 vc2) * τ ^ 2‖ + ‖(10 * qT5 vc2) * τ ^ 3‖
          + ‖(15 * qT6 vc2) * τ ^ 4‖ + ‖(21 * qT7) * τ ^ 5‖ :=
      le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
        (add_le_add (le_trans (norm_add_le _ _)
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    have := norm_sub_norm_le (qT2 vc2)
      (-((3 * qT3 vc2) * τ + (6 * qT4 vc2) * τ ^ 2 + (10 * qT5 vc2) * τ ^ 3
        + (15 * qT6 vc2) * τ ^ 4 + (21 * qT7) * τ ^ 5))
    simp only [sub_neg_eq_add, norm_neg] at this
    linarith [this, hrest]
  norm_num [norm_mul, norm_pow] at htri t3 t4 t5 t6 t7
  linarith [htri, qT2_vc2_lower, t3, t4, t5, t6, t7]

theorem qT3_zc2_bound : ‖qT3 zc2‖ ≤ (189865523 / 1000000 : ℝ) := by
  obtain ⟨τ, hτ, hzc⟩ := tau_exists
  rw [hzc, qT_shift3]
  have b4 : ‖(4 : ℂ) * qT4 vc2‖ ≤ 4 * (19528067 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT4_vc2_bound
  have b5 : ‖(10 : ℂ) * qT5 vc2‖ ≤ 10 * (2846493 / 200000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT5_vc2_bound
  have b6 : ‖(20 : ℂ) * qT6 vc2‖ ≤ 20 * (5762733 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT6_vc2_bound
  have b7 : ‖(35 : ℂ) * qT7‖ ≤ 35 * (1 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT7_bound
  have t4 := norm_shift_bound hτ b4 1
  have t5 := norm_shift_bound hτ b5 2
  have t6 := norm_shift_bound hτ b6 3
  have t7 := norm_shift_bound hτ b7 4
  have htri : ‖qT3 vc2 + (4 * qT4 vc2) * τ + (10 * qT5 vc2) * τ ^ 2 + (20 * qT6 vc2) * τ ^ 3
      + (35 * qT7) * τ ^ 4‖
      ≤ ‖qT3 vc2‖ + ‖(4 * qT4 vc2) * τ‖ + ‖(10 * qT5 vc2) * τ ^ 2‖
        + ‖(20 * qT6 vc2) * τ ^ 3‖ + ‖(35 * qT7) * τ ^ 4‖ :=
    le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
      (add_le_add (le_trans (norm_add_le _ _)
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  norm_num [norm_mul, norm_pow] at htri t4 t5 t6 t7
  linarith [htri, qT3_vc2_bound, t4, t5, t6, t7]

theorem qT4_zc2_bound : ‖qT4 zc2‖ ≤ (19528139 / 1000000 : ℝ) := by
  obtain ⟨τ, hτ, hzc⟩ := tau_exists
  rw [hzc, qT_shift4]
  have b5 : ‖(5 : ℂ) * qT5 vc2‖ ≤ 5 * (2846493 / 200000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT5_vc2_bound
  have b6 : ‖(15 : ℂ) * qT6 vc2‖ ≤ 15 * (5762733 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT6_vc2_bound
  have b7 : ‖(35 : ℂ) * qT7‖ ≤ 35 * (1 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT7_bound
  have t5 := norm_shift_bound hτ b5 1
  have t6 := norm_shift_bound hτ b6 2
  have t7 := norm_shift_bound hτ b7 3
  have htri : ‖qT4 vc2 + (5 * qT5 vc2) * τ + (15 * qT6 vc2) * τ ^ 2 + (35 * qT7) * τ ^ 3‖
      ≤ ‖qT4 vc2‖ + ‖(5 * qT5 vc2) * τ‖ + ‖(15 * qT6 vc2) * τ ^ 2‖ + ‖(35 * qT7) * τ ^ 3‖ :=
    le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
      (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  norm_num [norm_mul, norm_pow] at htri t5 t6 t7
  linarith [htri, qT4_vc2_bound, t5, t6, t7]

theorem qT5_zc2_bound : ‖qT5 zc2‖ ≤ (5693 / 400 : ℝ) := by
  obtain ⟨τ, hτ, hzc⟩ := tau_exists
  rw [hzc, qT_shift5]
  have b6 : ‖(6 : ℂ) * qT6 vc2‖ ≤ 6 * (5762733 / 1000000 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT6_vc2_bound
  have b7 : ‖(21 : ℂ) * qT7‖ ≤ 21 * (1 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT7_bound
  have t6 := norm_shift_bound hτ b6 1
  have t7 := norm_shift_bound hτ b7 2
  have htri : ‖qT5 vc2 + (6 * qT6 vc2) * τ + (21 * qT7) * τ ^ 2‖
      ≤ ‖qT5 vc2‖ + ‖(6 * qT6 vc2) * τ‖ + ‖(21 * qT7) * τ ^ 2‖ :=
    le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
  norm_num [norm_mul, norm_pow] at htri t6 t7
  linarith [htri, qT5_vc2_bound, t6, t7]

theorem qT6_zc2_bound : ‖qT6 zc2‖ ≤ (288137 / 50000 : ℝ) := by
  obtain ⟨τ, hτ, hzc⟩ := tau_exists
  rw [hzc, qT_shift6]
  have b7 : ‖(7 : ℂ) * qT7‖ ≤ 7 * (1 : ℝ) :=
    norm_const_mul (by norm_num) (by norm_num) qT7_bound
  have t7 := norm_shift_bound hτ b7 1
  have htri : ‖qT6 vc2 + (7 * qT7) * τ‖ ≤ ‖qT6 vc2‖ + ‖(7 * qT7) * τ‖ := norm_add_le _ _
  norm_num [norm_mul, norm_pow] at htri t7
  linarith [htri, qT6_vc2_bound, t7]

/-! #### The explicit comparison polynomial -/

def Apoly : Polynomial ℂ :=
  Polynomial.C (qT2 zc2 * (ρ : ℂ) ^ 5 * (ε : ℂ) ^ 5)
    + Polynomial.C (qT3 zc2 * (ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4) * Polynomial.X
    + Polynomial.C (qT4 zc2 * (ρ : ℂ) ^ 3 * (ε : ℂ) ^ 3) * Polynomial.X ^ 2
    + Polynomial.C (qT5 zc2 * (ρ : ℂ) ^ 2 * (ε : ℂ) ^ 2) * Polynomial.X ^ 3
    + Polynomial.C (qT6 zc2 * (ρ : ℂ) * (ε : ℂ)) * Polynomial.X ^ 4
    + Polynomial.C qT7 * Polynomial.X ^ 5

theorem Apoly_eval (z : ℂ) : Apoly.eval z
    = qT2 zc2 * (ρ : ℂ) ^ 5 * (ε : ℂ) ^ 5
      + qT3 zc2 * (ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * z
      + qT4 zc2 * (ρ : ℂ) ^ 3 * (ε : ℂ) ^ 3 * z ^ 2
      + qT5 zc2 * (ρ : ℂ) ^ 2 * (ε : ℂ) ^ 2 * z ^ 3
      + qT6 zc2 * (ρ : ℂ) * (ε : ℂ) * z ^ 4
      + qT7 * z ^ 5 := by
  simp only [Apoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  try ring

theorem Q_eval_zc2 : Q.eval zc2 = qT0 zc2 := by
  have h := Q_taylor zc2 0
  simpa using h

theorem f_shift_scaled (t : ℂ) :
    f.eval (zs + (ρ : ℂ) * (ε : ℂ) * t) - f.eval zs
      = Apoly.eval ((ρ : ℂ) * (ε : ℂ) * t) * ((ρ : ℂ) * (ε : ℂ) * t) ^ 2 := by
  have h1 : zs + (ρ : ℂ) * (ε : ℂ) * t = (ρ : ℂ) * (ε : ℂ) * (zc2 + t) := by
    unfold zs; ring
  have h2 : zs = (ρ : ℂ) * (ε : ℂ) * zc2 := rfl
  rw [h1, f_eval_rho_eps, h2, f_eval_rho_eps, Q_taylor zc2 t, Q_eval_zc2, qT1_zc2,
    Apoly_eval]
  ring

theorem f_shift (z : ℂ) :
    f.eval (zs + z) - f.eval zs = Apoly.eval z * z ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, z = (ρ : ℂ) * (ε : ℂ) * t := by
    refine ⟨z / ((ρ : ℂ) * (ε : ℂ)), ?_⟩
    rw [mul_comm ((ρ : ℂ) * (ε : ℂ)) (z / ((ρ : ℂ) * (ε : ℂ))),
      div_mul_cancel₀ z rho_eps_ne_zero]
  exact f_shift_scaled t

theorem shiftQuad_eq : shiftQuad f zs = Apoly := by
  have hmul : (shiftQuad f zs) * Polynomial.X ^ 2 = Apoly * Polynomial.X ^ 2 := by
    apply Polynomial.funext
    intro z
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [shiftQuad_spec f zs zs_crit z, f_shift z]
  exact mul_right_cancel₀ (pow_ne_zero 2 Polynomial.X_ne_zero) hmul

/-! #### The comparison coefficient and the disk bound -/

def aHat : ℂ := qT2 zc2 * (ρ : ℂ) ^ 5 * (ε : ℂ) ^ 5

theorem aHat_norm : ‖aHat‖ = ‖qT2 zc2‖ * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 := by
  unfold aHat
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ratCast, Complex.norm_ratCast,
    abs_of_pos rho_pos, abs_of_pos eps_pos]

theorem aHat_lower : 180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ := by
  rw [aHat_norm]
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 5 := pow_pos rho_pos 5
  have h2 : (0 : ℝ) < (ε : ℝ) ^ 5 := pow_pos eps_pos 5
  nlinarith [qT2_zc2_lower, h1, h2, mul_pos h1 h2]

theorem aHat_ne_zero : aHat ≠ 0 := by
  intro h
  have h1 : (0 : ℝ) < (ρ : ℝ) ^ 5 := pow_pos rho_pos 5
  have h2 : (0 : ℝ) < (ε : ℝ) ^ 5 := pow_pos eps_pos 5
  have := aHat_lower
  rw [h, norm_zero] at this
  nlinarith [this, mul_pos h1 h2]

theorem term_bound {n : ℝ} (hn : 0 ≤ n) {m k : ℕ} (hmk : m + k = 5) {Z : ℝ}
    (hZ : 0 ≤ Z) (hz : Z ≤ (ρ : ℝ) * (ε : ℝ) / 10) :
    n * (ρ : ℝ) ^ m * (ε : ℝ) ^ m * Z ^ k ≤ n * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ k := by
  have h1 : Z ^ k ≤ ((ρ : ℝ) * (ε : ℝ) / 10) ^ k := pow_le_pow_left₀ hZ hz k
  have h2 : ((ρ : ℝ) * (ε : ℝ) / 10) ^ k = (ρ : ℝ) ^ k * (ε : ℝ) ^ k / 10 ^ k := by
    rw [div_pow, mul_pow]
  have h3 : (0 : ℝ) ≤ n * (ρ : ℝ) ^ m * (ε : ℝ) ^ m :=
    mul_nonneg (mul_nonneg hn (pow_pos rho_pos m).le) (pow_pos eps_pos m).le
  calc n * (ρ : ℝ) ^ m * (ε : ℝ) ^ m * Z ^ k
      ≤ n * (ρ : ℝ) ^ m * (ε : ℝ) ^ m * ((ρ : ℝ) ^ k * (ε : ℝ) ^ k / 10 ^ k) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 h3
    _ = n * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ k := by
        rw [← hmk]; ring

theorem disk_bound (z : ℂ) (hz : ‖z‖ ≤ (ρ : ℝ) * (ε : ℝ) / 10) :
    ‖(shiftQuad f zs).eval z / aHat - 1‖ ≤ 1 / 4 := by
  have hr : (0 : ℝ) < (ρ : ℝ) := rho_pos
  have he : (0 : ℝ) < (ε : ℝ) := eps_pos
  have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hrw : (shiftQuad f zs).eval z / aHat - 1 = (Apoly.eval z - aHat) / aHat := by
    rw [shiftQuad_eq, sub_div, div_self aHat_ne_zero]
  have hnum : Apoly.eval z - aHat
      = qT3 zc2 * (ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * z
        + qT4 zc2 * (ρ : ℂ) ^ 3 * (ε : ℂ) ^ 3 * z ^ 2
        + qT5 zc2 * (ρ : ℂ) ^ 2 * (ε : ℂ) ^ 2 * z ^ 3
        + qT6 zc2 * (ρ : ℂ) * (ε : ℂ) * z ^ 4
        + qT7 * z ^ 5 := by
    rw [Apoly_eval]; unfold aHat; ring
  have hb : ∀ (d : ℂ) (n : ℝ) (m k : ℕ), ‖d‖ ≤ n →
      ‖d * (ρ : ℂ) ^ m * (ε : ℂ) ^ m * z ^ k‖ ≤ n * (ρ : ℝ) ^ m * (ε : ℝ) ^ m * ‖z‖ ^ k := by
    intro d n m k hd
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow,
      Complex.norm_ratCast, Complex.norm_ratCast, abs_of_pos rho_pos, abs_of_pos eps_pos]
    have hn : 0 ≤ n := le_trans (norm_nonneg _) hd
    have := mul_le_mul_of_nonneg_right hd (le_of_lt (pow_pos rho_pos m))
    have h2 := mul_le_mul_of_nonneg_right this (le_of_lt (pow_pos eps_pos m))
    exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hzn k)
  have t3 := hb (qT3 zc2) (189865523 / 1000000) 4 1 qT3_zc2_bound
  have t4 := hb (qT4 zc2) (19528139 / 1000000) 3 2 qT4_zc2_bound
  have t5 := hb (qT5 zc2) (5693 / 400) 2 3 qT5_zc2_bound
  have t6 := hb (qT6 zc2) (288137 / 50000) 1 4 qT6_zc2_bound
  simp only [pow_one] at t3 t6
  have t7 : ‖qT7 * z ^ 5‖ ≤ 1 * ‖z‖ ^ 5 := by
    rw [norm_mul, norm_pow]
    have : ‖qT7‖ ≤ (1 : ℝ) := qT7_bound
    nlinarith [this, pow_nonneg hzn 5]
  have htri : ‖qT3 zc2 * (ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * z
      + qT4 zc2 * (ρ : ℂ) ^ 3 * (ε : ℂ) ^ 3 * z ^ 2
      + qT5 zc2 * (ρ : ℂ) ^ 2 * (ε : ℂ) ^ 2 * z ^ 3
      + qT6 zc2 * (ρ : ℂ) * (ε : ℂ) * z ^ 4 + qT7 * z ^ 5‖
      ≤ ‖qT3 zc2 * (ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * z‖
        + ‖qT4 zc2 * (ρ : ℂ) ^ 3 * (ε : ℂ) ^ 3 * z ^ 2‖
        + ‖qT5 zc2 * (ρ : ℂ) ^ 2 * (ε : ℂ) ^ 2 * z ^ 3‖
        + ‖qT6 zc2 * (ρ : ℂ) * (ε : ℂ) * z ^ 4‖ + ‖qT7 * z ^ 5‖ :=
    le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
      (add_le_add (le_trans (norm_add_le _ _)
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  have hz1 : ‖z‖ ≤ (ρ : ℝ) * (ε : ℝ) / 10 := hz
  have hpow : ∀ k : ℕ, ‖z‖ ^ k ≤ ((ρ : ℝ) * (ε : ℝ) / 10) ^ k := fun k =>
    pow_le_pow_left₀ hzn hz1 k
  have hkey : ‖Apoly.eval z - aHat‖ ≤ (19196653 / 1000000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 := by
    rw [hnum]
    have s3 := term_bound (n := 189865523 / 1000000) (by norm_num) (m := 4) (k := 1)
      (by norm_num) hzn hz1
    have s4 := term_bound (n := 19528139 / 1000000) (by norm_num) (m := 3) (k := 2)
      (by norm_num) hzn hz1
    have s5 := term_bound (n := 5693 / 400) (by norm_num) (m := 2) (k := 3)
      (by norm_num) hzn hz1
    have s6 := term_bound (n := 288137 / 50000) (by norm_num) (m := 1) (k := 4)
      (by norm_num) hzn hz1
    have s7 := term_bound (n := 1) (by norm_num) (m := 0) (k := 5)
      (by norm_num) hzn hz1
    simp only [pow_one, pow_zero, mul_one, one_mul] at s3 s4 s5 s6 s7
    have hp5 : (0 : ℝ) < (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 :=
      mul_pos (pow_pos rho_pos 5) (pow_pos eps_pos 5)
    have hnum5 : (189865523 / 1000000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ 1
        + (19528139 / 1000000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ 2
        + (5693 / 400 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ 3
        + (288137 / 50000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ 4
        + (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 / 10 ^ 5
        ≤ (19196653 / 1000000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 := by
      nlinarith [hp5]
    linarith [htri, t3, t4, t5, t6, t7, s3, s4, s5, s6, s7, hnum5]
  have hq : (19196653 / 1000000 : ℝ) * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ / 4 := by
    rw [aHat_norm]
    have hp5 : (0 : ℝ) < (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 :=
      mul_pos (pow_pos rho_pos 5) (pow_pos eps_pos 5)
    nlinarith [qT2_zc2_lower, hp5]
  have hanz : (0 : ℝ) < ‖aHat‖ := norm_pos_iff.mpr aHat_ne_zero
  rw [hrw, norm_div, div_le_iff₀ hanz]
  linarith [hkey, hq]

theorem slit_lt : 1 - ‖f.eval zs‖ < ‖aHat‖ * ((ρ : ℝ) * (ε : ℝ) / 10) ^ 2 / 4 := by
  have hd := delta_le
  have hp7 : (0 : ℝ) < (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 :=
    mul_pos (pow_pos rho_pos 7) (pow_pos eps_pos 7)
  have ha : 180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ := aHat_lower
  have hkey : (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 * (36 / 5 / 10 ^ 6)
      < (180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5) * ((ρ : ℝ) * (ε : ℝ) / 10) ^ 2 / 4 := by
    nlinarith [hp7]
  have hmono : (180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5) * ((ρ : ℝ) * (ε : ℝ) / 10) ^ 2 / 4
      ≤ ‖aHat‖ * ((ρ : ℝ) * (ε : ℝ) / 10) ^ 2 / 4 := by
    have hsq : (0 : ℝ) ≤ ((ρ : ℝ) * (ε : ℝ) / 10) ^ 2 := sq_nonneg _
    nlinarith [ha, hsq]
  linarith [hd, hkey, hmono]

theorem s4_disk_package :
    ∃ (aHat : ℂ) (hh : ℝ), aHat ≠ 0 ∧ 0 < hh ∧
      180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ ∧
      (∀ z : ℂ, ‖z‖ ≤ hh → ‖(shiftQuad f zs).eval z / aHat - 1‖ ≤ 1 / 4) ∧
      1 - ‖f.eval zs‖ < ‖aHat‖ * hh ^ 2 / 4 :=
  ⟨aHat, (ρ : ℝ) * (ε : ℝ) / 10, aHat_ne_zero,
    by have := rho_pos; have := eps_pos; positivity, aHat_lower, disk_bound, slit_lt⟩


/-! ### Step 5: the projection bound

`‖ζ‖ = 1` gives `‖ζ − εq‖ ≥ 1 − ε·Re(ζ·conj q)` by Cauchy–Schwarz, so the sum of
the two distances is at least `2 − ε(R₃+R₆)`.  The certificate is
`R₃ + R₆ ≤ −0.2735` against the demanded `−0.143`. -/

theorem norm_cayley_sub_le {x : ℝ} {w : ℂ} {M D T : ℝ} (hT : 0 ≤ T)
    (hA : |1 - w.re - w.im * x| ≤ M) (hB : |x + w.re * x - w.im| ≤ M)
    (hD : 0 < D) (hx : D ≤ 1 + x ^ 2) (hfin : 2 * M ^ 2 ≤ T ^ 2 * D) :
    ‖cayley x - w‖ ≤ T := by
  have hden := cayley_den_ne_zero x
  have hrw : cayley x - w
      = ((1 + (x : ℂ) * Complex.I) - w * (1 - (x : ℂ) * Complex.I))
        / (1 - (x : ℂ) * Complex.I) := by
    rw [cayley]; field_simp
  have hd2 : ‖(1 : ℂ) - (x : ℂ) * Complex.I‖ ^ 2 = 1 + x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hn2 : ‖(1 + (x : ℂ) * Complex.I) - w * (1 - (x : ℂ) * Complex.I)‖ ^ 2
      = (1 - w.re - w.im * x) ^ 2 + (x + w.re * x - w.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hdpos : 0 < ‖(1 : ℂ) - (x : ℂ) * Complex.I‖ := norm_pos_iff.mpr hden
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  have hAsq : (1 - w.re - w.im * x) ^ 2 ≤ M ^ 2 := by nlinarith [hA'.1, hA'.2]
  have hBsq : (x + w.re * x - w.im) ^ 2 ≤ M ^ 2 := by nlinarith [hB'.1, hB'.2]
  have hscale : T ^ 2 * D ≤ T ^ 2 * (1 + x ^ 2) :=
    mul_le_mul_of_nonneg_left hx (sq_nonneg T)
  rw [hrw, norm_div, div_le_iff₀ hdpos]
  have hkey : ‖(1 + (x : ℂ) * Complex.I) - w * (1 - (x : ℂ) * Complex.I)‖ ^ 2
      ≤ (T * ‖(1 : ℂ) - (x : ℂ) * Complex.I‖) ^ 2 := by
    have h1 : (T * ‖(1 : ℂ) - (x : ℂ) * Complex.I‖) ^ 2
        = T ^ 2 * ‖(1 : ℂ) - (x : ℂ) * Complex.I‖ ^ 2 := by ring
    rw [h1, hd2, hn2]
    linarith [hAsq, hBsq, hfin, hscale]
  nlinarith [hkey, norm_nonneg ((1 + (x : ℂ) * Complex.I) - w * (1 - (x : ℂ) * Complex.I)),
    mul_nonneg hT hdpos.le]

theorem cayley3_near : ‖cayley (realRoot 3) - u 3‖ ≤ 1 / 500 := by
  have hx1 : (43812 / 10000 : ℝ) < realRoot 3 := (realRoot_mem 3).1
  have hx2 : realRoot 3 < (43813 / 10000 : ℝ) := (realRoot_mem 3).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_3
  refine norm_cayley_sub_le (M := 1 / 200) (D := 20) (by norm_num)
    (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)
    (by norm_num) (by nlinarith) (by norm_num)

theorem cayley6_near : ‖cayley (realRoot 6) - u 6‖ ≤ 1 / 100 := by
  have hx1 : (-4816 / 10000 : ℝ) < realRoot 6 := (realRoot_mem 6).1
  have hx2 : realRoot 6 < (-4815 / 10000 : ℝ) := (realRoot_mem 6).2
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_6
  refine norm_cayley_sub_le (M := 1 / 200) (D := 123 / 100) (by norm_num)
    (by rw [abs_le]; constructor <;> nlinarith)
    (by rw [abs_le]; constructor <;> nlinarith)
    (by norm_num) (by nlinarith) (by norm_num)

theorem re_le_of_norm_le {z w : ℂ} {T : ℝ} (h : ‖z - w‖ ≤ T) :
    |z.re - w.re| ≤ T ∧ |z.im - w.im| ≤ T := by
  constructor
  · have hb := Complex.abs_re_le_norm (z - w)
    simp only [Complex.sub_re] at hb
    linarith
  · have hb := Complex.abs_im_le_norm (z - w)
    simp only [Complex.sub_im] at hb
    linarith

/-! #### Componentwise enclosures -/

theorem zc2_comp : |zc2.re - vc2.re| ≤ 1 / 1000000 ∧ |zc2.im - vc2.im| ≤ 1 / 1000000 :=
  re_le_of_norm_le zc2_mem

theorem vc2_re_small : |vc2.re| ≤ 1 / 100000 := by
  rw [abs_le]
  unfold vc2
  constructor <;>
    (simp only [Complex.add_re, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im,
      Complex.I_re, Complex.I_im]; push_cast; norm_num)

theorem vc2_im_bounds : (8232 / 10000 : ℝ) ≤ vc2.im ∧ vc2.im ≤ 8233 / 10000 := by
  unfold vc2
  constructor <;>
    (simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
      Complex.I_re, Complex.I_im]; push_cast; norm_num)

/-! #### The projection certificate -/

theorem proj_R_bound :
    (cayley (realRoot 3)).re * zc2.re + (cayley (realRoot 3)).im * zc2.im
      + ((cayley (realRoot 6)).re * zc2.re + (cayley (realRoot 6)).im * zc2.im)
      ≤ -(143 / 1000) := by
  obtain ⟨h3re, h3im⟩ := re_le_of_norm_le cayley3_near
  obtain ⟨h6re, h6im⟩ := re_le_of_norm_le cayley6_near
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_3
  obtain ⟨⟨s1, s2⟩, ⟨t1, t2⟩⟩ := u_bounds_6
  obtain ⟨q1, q2⟩ := zc2_comp
  have hv1 := vc2_re_small
  obtain ⟨hv2, hv3⟩ := vc2_im_bounds
  rw [abs_le] at h3re h3im h6re h6im q1 q2 hv1
  nlinarith [h3re.1, h3re.2, h3im.1, h3im.2, h6re.1, h6re.2, h6im.1, h6im.2,
    q1.1, q1.2, q2.1, q2.2, hv1.1, hv1.2, r1, r2, i1, i2, s1, s2, t1, t2, hv2, hv3]

theorem proj_R3_le_one :
    (cayley (realRoot 3)).re * zc2.re + (cayley (realRoot 3)).im * zc2.im ≤ 1 := by
  obtain ⟨h3re, h3im⟩ := re_le_of_norm_le cayley3_near
  obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := u_bounds_3
  obtain ⟨q1, q2⟩ := zc2_comp
  have hv1 := vc2_re_small
  obtain ⟨hv2, hv3⟩ := vc2_im_bounds
  rw [abs_le] at h3re h3im q1 q2 hv1
  nlinarith [h3re.1, h3re.2, h3im.1, h3im.2, q1.1, q1.2, q2.1, q2.2,
    hv1.1, hv1.2, r1, r2, i1, i2, hv2, hv3]

theorem proj_R6_le_one :
    (cayley (realRoot 6)).re * zc2.re + (cayley (realRoot 6)).im * zc2.im ≤ 1 := by
  obtain ⟨h6re, h6im⟩ := re_le_of_norm_le cayley6_near
  obtain ⟨⟨s1, s2⟩, ⟨t1, t2⟩⟩ := u_bounds_6
  obtain ⟨q1, q2⟩ := zc2_comp
  have hv1 := vc2_re_small
  obtain ⟨hv2, hv3⟩ := vc2_im_bounds
  rw [abs_le] at h6re h6im q1 q2 hv1
  nlinarith [h6re.1, h6re.2, h6im.1, h6im.2, q1.1, q1.2, q2.1, q2.2,
    hv1.1, hv1.2, s1, s2, t1, t2, hv2, hv3]

theorem one_sub_eps_re_le_norm {ζ q : ℂ} (hz : ‖ζ‖ = 1) {e : ℝ} (he : 0 ≤ e)
    (hle : e * (ζ.re * q.re + ζ.im * q.im) ≤ 1) :
    1 - e * (ζ.re * q.re + ζ.im * q.im) ≤ ‖ζ - ((e : ℝ) : ℂ) * q‖ := by
  have hns : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hz2 : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    rw [← hns]; simp only [Complex.normSq_apply]; ring
  have hq2 : Complex.normSq q = q.re ^ 2 + q.im ^ 2 := by
    simp only [Complex.normSq_apply]; ring
  have hcs : (ζ.re * q.re + ζ.im * q.im) ^ 2 ≤ Complex.normSq q := by
    rw [hq2]
    nlinarith [sq_nonneg (ζ.re * q.im - ζ.im * q.re), hz2]
  have hexp : Complex.normSq (ζ - ((e : ℝ) : ℂ) * q)
      = Complex.normSq ζ - 2 * e * (ζ.re * q.re + ζ.im * q.im)
        + e ^ 2 * Complex.normSq q := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  apply le_norm_of_le_normSq (by linarith)
  rw [hexp, hns]
  nlinarith [hcs, sq_nonneg e, mul_le_mul_of_nonneg_left hcs (sq_nonneg e)]

theorem eps_cast : (((ε : ℝ)) : ℂ) = ((ε : ℚ) : ℂ) := by push_cast; ring

theorem s4_projection :
    (ρ : ℝ) * (2 + (ε : ℝ) * (143 / 1000))
      ≤ ‖physicalRoot 3 - zs‖ + ‖physicalRoot 6 - zs‖ := by
  have hRb := proj_R_bound
  have he : (0 : ℝ) ≤ (ε : ℝ) := eps_pos.le
  have heps1 : ((ε : ℝ)) ≤ 1 := by unfold ε s; norm_num
  have hle3 : (ε : ℝ) * ((cayley (realRoot 3)).re * zc2.re
      + (cayley (realRoot 3)).im * zc2.im) ≤ 1 := by
    nlinarith [proj_R3_le_one, he, heps1]
  have hle6 : (ε : ℝ) * ((cayley (realRoot 6)).re * zc2.re
      + (cayley (realRoot 6)).im * zc2.im) ≤ 1 := by
    nlinarith [proj_R6_le_one, he, heps1]
  have hb3 := one_sub_eps_re_le_norm (cayley_norm (realRoot 3)) he hle3
  have hb6 := one_sub_eps_re_le_norm (cayley_norm (realRoot 6)) he hle6
  have hp3 : physicalRoot 3 - zs
      = (ρ : ℂ) * (cayley (realRoot 3) - (((ε : ℝ)) : ℂ) * zc2) := by
    unfold physicalRoot zs
    rw [eps_cast]; ring
  have hp6 : physicalRoot 6 - zs
      = (ρ : ℂ) * (cayley (realRoot 6) - (((ε : ℝ)) : ℂ) * zc2) := by
    unfold physicalRoot zs
    rw [eps_cast]; ring
  have hmul : (ε : ℝ) * (143 / 1000)
      ≤ -((ε : ℝ) * (((cayley (realRoot 3)).re * zc2.re + (cayley (realRoot 3)).im * zc2.im)
        + ((cayley (realRoot 6)).re * zc2.re + (cayley (realRoot 6)).im * zc2.im))) := by
    nlinarith [mul_nonneg he (by linarith [hRb] :
      (0 : ℝ) ≤ -(143 / 1000) - (((cayley (realRoot 3)).re * zc2.re
        + (cayley (realRoot 3)).im * zc2.im)
        + ((cayley (realRoot 6)).re * zc2.re + (cayley (realRoot 6)).im * zc2.im)))]
  have hsum : 2 + (ε : ℝ) * (143 / 1000)
      ≤ ‖cayley (realRoot 3) - (((ε : ℝ)) : ℂ) * zc2‖
        + ‖cayley (realRoot 6) - (((ε : ℝ)) : ℂ) * zc2‖ := by
    linarith [hb3, hb6, hmul]
  rw [hp3, hp6, norm_mul, norm_mul, Complex.norm_ratCast, abs_of_pos rho_pos]
  have hfin := mul_le_mul_of_nonneg_left hsum rho_pos.le
  linarith [hfin]

end Erdos1041.Counterexample.S4Proofs

namespace Erdos1041.Counterexample

/-- Paper §4.1 and §5.1: the concrete critical-point package at `s = 10⁻⁶`.
Owner: slice S4.  Statement verbatim from the shared interface. -/
theorem s4_instance_critical :
    ∃ (zs b₃ b₆ aHat : ℂ) (h : ℝ),
      zs ∈ Omega f ∧
      (Polynomial.derivative f).IsRoot zs ∧
      Polynomial.rootMultiplicity zs (Polynomial.derivative f) = 1 ∧
      (∀ c' ∈ Omega f, (Polynomial.derivative f).IsRoot c' → c' = zs) ∧
      0 < ‖f.eval zs‖ ∧
      0 < 1 - ‖f.eval zs‖ ∧
      1 - ‖f.eval zs‖ ≤ (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 * (36 / 5 / 10 ^ 6) ∧
      aHat ≠ 0 ∧ 0 < h ∧
      180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ ∧
      (∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad f zs).eval z / aHat - 1‖ ≤ 1 / 4) ∧
      1 - ‖f.eval zs‖ < ‖aHat‖ * h ^ 2 / 4 ∧
      ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
        < (ρ : ℝ) * (ε : ℝ) / 1000 ∧
      f.IsRoot b₃ ∧ f.IsRoot b₆ ∧ b₃ ≠ b₆ ∧
      ‖b₃ - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 ∧
      ‖b₆ - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 ∧
      (∀ w, f.IsRoot w → ∃ j : Fin 7, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10) ∧
      (∀ w, f.IsRoot w →
        ‖w - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 →
        w = b₃) ∧
      (∀ w, f.IsRoot w →
        ‖w - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 →
        w = b₆) ∧
      (ρ : ℝ) * (2 + (ε : ℝ) * (143 / 1000)) ≤ ‖b₃ - zs‖ + ‖b₆ - zs‖ := by
  obtain ⟨aHat, hh, haHat, hhpos, haLo, hdisk, hslit⟩ := S4Proofs.s4_disk_package
  exact ⟨S4Proofs.zs, S4Proofs.physicalRoot 3, S4Proofs.physicalRoot 6, aHat, hh,
    S4Proofs.zs_mem_omega, S4Proofs.zs_crit, S4Proofs.zs_simple, S4Proofs.crit_unique,
    S4Proofs.norm_f_zs_pos, S4Proofs.delta_pos, S4Proofs.delta_le,
    haHat, hhpos, haLo, hdisk, hslit, S4Proofs.zs_loc,
    s4_b3_isRoot, s4_b6_isRoot, s4_b3_ne_b6, s4_b3_near, s4_b6_near,
    s4_roots_near_seventh_roots, s4_root_unique_near_u3, s4_root_unique_near_u6,
    S4Proofs.s4_projection⟩

end Erdos1041.Counterexample
