import ErdosProblems.Erdos1041.PaperCurveAssembly

/-!
# Erdős 1041: complementary binomial chords

Formalisation of the short paper's binomial-chord theorem
(`paper/1041/erdos-1041-lemniscate-newton-flow.tex`, line 1099, section
"Two chord constructions for binomials").

The paper normalises `f(z) = z^n - a` with `n ≥ 2`, `0 < |a| < 1`, and writes
`a = r^n > 0` after a rotation; it puts `ω = e^{2πi/n}`, `c = cos(π/n)`,
`r_* = (1+c^n)^{-1/n}` and `ε = (1-r^n)^{1/n}`.  The theorem asserts:

* two adjacent zeros of `z^n - a` are joined by an explicit polygonal path
  inside `{|z^n - a| < 1}` of length strictly below `2`;
* for `r < r_*` the adjacent-root chord itself works;
* for `r ≥ r_*` two radial legs and an inner adjacent crossing chord work
  after an arbitrarily small radial contraction;
* the two constructions meet at `r = r_*`, where the outer chord attains
  `|f| = 1` at its midpoint and therefore lies only in the closed lemniscate;
* open containment at and above the switch uses the inner chord after a
  radial contraction.

Everything is proved here, together with the two supporting displayed
identities: the companion's chord maximum
`max_{z ∈ [s, sω]} |z^n - r^n| = r^n + (sc)^n` for every `0 < s ≤ r`, and its
decisive step `1 + cos(nθ) ≤ 2 cos^n θ` on `|θ| ≤ π/n`.

Curve language is the tree's own: `PaperCurve.ConnectedBelow f R L a b` is a
continuous rectifiable curve on `[0,2]` with the given endpoints, staying in
`{‖f‖ < R}`, whose Mathlib extended variation is below `ENNReal.ofReal L`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Set
open scoped ENNReal NNReal

namespace BinomialChord

/-! ## The paper's notation -/

/-- `π/n`. -/
def angle (n : ℕ) : ℝ := Real.pi / (n : ℝ)

/-- `c = cos(π/n)`. -/
def chordCos (n : ℕ) : ℝ := Real.cos (angle n)

/-- `sin(π/n)`. -/
def chordSin (n : ℕ) : ℝ := Real.sin (angle n)

/-- `e^{iπ/n}`; its square is the paper's `ω = e^{2πi/n}`. -/
def halfRoot (n : ℕ) : ℂ := Complex.exp ((angle n : ℂ) * Complex.I)

/-- `ω = e^{2πi/n}`. -/
def chordOmega (n : ℕ) : ℂ := halfRoot n ^ 2

/-- `r_* = (1 + c^n)^{-1/n}`. -/
def chordThreshold (n : ℕ) : ℝ := (1 + chordCos n ^ n) ^ (-((n : ℝ)⁻¹))

/-- `ε = (1 - r^n)^{1/n}`. -/
def chordEps (n : ℕ) (r : ℝ) : ℝ := (1 - r ^ n) ^ ((n : ℝ)⁻¹)

/-- The paper's inner radius `t = ε/c`. -/
def innerRadius (n : ℕ) (r : ℝ) : ℝ := chordEps n r / chordCos n

/-- The point of the segment `[s, sω]` at parameter `u ∈ [0,1]`. -/
def chordPoint (n : ℕ) (s u : ℝ) : ℂ :=
  (s : ℂ) * (((1 - u : ℝ) : ℂ) + ((u : ℝ) : ℂ) * chordOmega n)

/-! ## Elementary facts about the angle -/

theorem cast_pos {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < (n : ℝ) := by
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

theorem angle_pos {n : ℕ} (hn : 2 ≤ n) : 0 < angle n :=
  div_pos Real.pi_pos (cast_pos hn)

theorem angle_le_pi_div_two {n : ℕ} (hn : 2 ≤ n) : angle n ≤ Real.pi / 2 := by
  have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) h2

theorem angle_le_pi_div_three {n : ℕ} (hn : 3 ≤ n) : angle n ≤ Real.pi / 3 := by
  have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) h3

theorem cast_mul_angle {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) * angle n = Real.pi := by
  have h : ((n : ℝ)) ≠ 0 := (cast_pos hn).ne'
  show (n : ℝ) * (Real.pi / (n : ℝ)) = Real.pi
  field_simp

theorem chordSin_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ chordSin n := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi (angle_pos hn).le
  have := angle_le_pi_div_two hn
  have := Real.pi_pos
  linarith

theorem chordSin_le_one (n : ℕ) : chordSin n ≤ 1 := Real.sin_le_one _

theorem chordCos_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ chordCos n := by
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · have := (angle_pos hn).le
    have := Real.pi_pos
    linarith
  · exact angle_le_pi_div_two hn

theorem chordCos_le_one (n : ℕ) : chordCos n ≤ 1 := Real.cos_le_one _

theorem chordCos_pos {n : ℕ} (hn : 3 ≤ n) : 0 < chordCos n := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have := (angle_pos (by omega : 2 ≤ n)).le
    have := Real.pi_pos
    linarith
  · have := angle_le_pi_div_three hn
    have := Real.pi_pos
    linarith

theorem sin_sq_add_cos_sq (n : ℕ) : chordSin n ^ 2 + chordCos n ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq _

theorem chordSin_lt_one {n : ℕ} (hn : 3 ≤ n) : chordSin n < 1 := by
  have hc := chordCos_pos hn
  have h := sin_sq_add_cos_sq n
  have hs := chordSin_nonneg (by omega : 2 ≤ n)
  nlinarith

theorem chordCos_eq_zero_of_two : chordCos 2 = 0 := by
  have : angle 2 = Real.pi / 2 := by norm_num [angle]
  rw [chordCos, this, Real.cos_pi_div_two]

/-! ## The half root and `ω` -/

theorem halfRoot_eq (n : ℕ) :
    halfRoot n = ((chordCos n : ℝ) : ℂ) + ((chordSin n : ℝ) : ℂ) * Complex.I := by
  rw [halfRoot, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [chordCos, chordSin]

theorem halfRoot_pow {n : ℕ} (hn : 2 ≤ n) : halfRoot n ^ n = -1 := by
  have h : ((n : ℂ)) * ((angle n : ℝ) : ℂ) * Complex.I = ((Real.pi : ℝ) : ℂ) * Complex.I := by
    have := cast_mul_angle hn
    have : ((n : ℝ) * angle n : ℝ) = Real.pi := this
    push_cast [← this]
    ring
  rw [halfRoot, ← Complex.exp_nat_mul]
  rw [show (n : ℂ) * (((angle n : ℝ) : ℂ) * Complex.I)
      = ((n : ℂ)) * ((angle n : ℝ) : ℂ) * Complex.I by ring, h]
  exact Complex.exp_pi_mul_I

theorem chordOmega_pow {n : ℕ} (hn : 2 ≤ n) : chordOmega n ^ n = 1 := by
  rw [chordOmega, ← pow_mul, mul_comm, pow_mul, halfRoot_pow hn]
  norm_num

theorem norm_halfRoot (n : ℕ) : ‖halfRoot n‖ = 1 := by
  rw [halfRoot]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_chordOmega (n : ℕ) : ‖chordOmega n‖ = 1 := by
  rw [chordOmega, norm_pow, norm_halfRoot]
  norm_num

theorem norm_one_sub_chordOmega_le (n : ℕ) : ‖1 - chordOmega n‖ ≤ 2 := by
  calc ‖1 - chordOmega n‖ ≤ ‖(1 : ℂ)‖ + ‖chordOmega n‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_one, norm_chordOmega]; norm_num

/-! ## The decisive estimate `1 + cos(nθ) ≤ 2 cos^n θ` -/

/-- The two-step induction statement: `cos(nψ/2) ≤ (√cos ψ)^n` whenever
`0 ≤ ψ` and `nψ ≤ π`. -/
private def Dec (n : ℕ) : Prop :=
  ∀ ψ : ℝ, 0 ≤ ψ → (n : ℝ) * ψ ≤ Real.pi →
    Real.cos ((n : ℝ) * ψ / 2) ≤ Real.sqrt (Real.cos ψ) ^ n

private theorem dec_two : Dec 2 := by
  intro ψ hψ0 hψ1
  have hc : 0 ≤ Real.cos ψ := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have := Real.pi_pos; linarith
    · push_cast at hψ1; linarith
  have h1 : ((2 : ℕ) : ℝ) * ψ / 2 = ψ := by push_cast; ring
  rw [h1]
  rw [show ((2 : ℕ)) = 2 from rfl, Real.sq_sqrt hc]

private theorem dec_three : Dec 3 := by
  intro ψ hψ0 hψ1
  have hψ3 : ψ ≤ Real.pi / 3 := by push_cast at hψ1; linarith
  have hπ := Real.pi_pos
  have hc : (1 : ℝ) / 2 ≤ Real.cos ψ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hψ0 (by linarith) hψ3
    rwa [Real.cos_pi_div_three] at h
  have hc0 : 0 ≤ Real.cos ψ := by linarith
  have hhalf : 0 ≤ Real.cos (((3 : ℕ) : ℝ) * ψ / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · push_cast; linarith
    · push_cast; linarith
  have hsqrt : 0 ≤ Real.sqrt (Real.cos ψ) ^ 3 := by positivity
  -- compare squares
  have hsq : Real.cos (((3 : ℕ) : ℝ) * ψ / 2) ^ 2 ≤ (Real.sqrt (Real.cos ψ) ^ 3) ^ 2 := by
    have hcs : Real.cos (((3 : ℕ) : ℝ) * ψ / 2) ^ 2
        = 1 / 2 + Real.cos (3 * ψ) / 2 := by
      have := Real.cos_sq (((3 : ℕ) : ℝ) * ψ / 2)
      rw [this]
      congr 2
      push_cast
      ring
    have hcube : (Real.sqrt (Real.cos ψ) ^ 3) ^ 2 = Real.cos ψ ^ 3 := by
      rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, Real.sq_sqrt hc0]
    rw [hcs, hcube, Real.cos_three_mul]
    have hcle : Real.cos ψ ≤ 1 := Real.cos_le_one ψ
    have hfac : (0 : ℝ) ≤ 2 * Real.cos ψ ^ 2 + 2 * Real.cos ψ - 1 := by nlinarith
    have hkey : 2 * Real.cos ψ ^ 3 - 3 * Real.cos ψ + 1 ≤ 0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcle) hfac]
    linarith
  nlinarith [hhalf, hsqrt, hsq]

private theorem dec_step {n : ℕ} (hn : 2 ≤ n) (h : Dec n) : Dec (n + 2) := by
  intro ψ hψ0 hψ1
  have hπ := Real.pi_pos
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hψ1 ⊢
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hnψ : (n : ℝ) * ψ ≤ Real.pi := by nlinarith
  have h4 : 4 * ψ ≤ Real.pi := by nlinarith [mul_nonneg (sub_nonneg.mpr hnR) hψ0]
  have hc0 : 0 ≤ Real.cos ψ := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · linarith
    · linarith
  have hs0 : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi hψ0 (by linarith)
  have hnψ0 : 0 ≤ (n : ℝ) * ψ / 2 := by positivity
  have hsn : 0 ≤ Real.sin ((n : ℝ) * ψ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hnψ0 (by linarith)
  have hih := h ψ hψ0 hnψ
  have hexpand : ((n : ℝ) + 2) * ψ / 2 = (n : ℝ) * ψ / 2 + ψ := by ring
  rw [hexpand, Real.cos_add]
  have hstep : Real.cos ((n : ℝ) * ψ / 2) * Real.cos ψ
      ≤ Real.sqrt (Real.cos ψ) ^ n * Real.cos ψ :=
    mul_le_mul_of_nonneg_right hih hc0
  have hfin : Real.sqrt (Real.cos ψ) ^ n * Real.cos ψ
      = Real.sqrt (Real.cos ψ) ^ (n + 2) := by
    rw [pow_add, Real.sq_sqrt hc0]
  nlinarith [mul_nonneg hsn hs0]

private theorem dec_pair : ∀ j : ℕ, Dec (j + 2) ∧ Dec (j + 3) := by
  intro j
  induction j with
  | zero => exact ⟨dec_two, dec_three⟩
  | succ k ih =>
      have h1 : Dec (k + 3) := ih.2
      have h2 : Dec (k + 2 + 2) := dec_step (by omega) ih.1
      exact ⟨h1, h2⟩

private theorem dec (n : ℕ) (hn : 2 ≤ n) : Dec n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  exact (dec_pair j).1

/-- **The paper's decisive step.**  `1 + cos(nθ) ≤ 2 cos^n θ` for `|θ| ≤ π/n`,
stated without a division as `n|θ| ≤ π`. -/
theorem one_add_cos_le {n : ℕ} (hn : 2 ≤ n) {ψ : ℝ} (hψ : (n : ℝ) * |ψ| ≤ Real.pi) :
    1 + Real.cos ((n : ℝ) * ψ) ≤ 2 * Real.cos ψ ^ n := by
  have hcosabs : Real.cos ψ = Real.cos |ψ| := by
    rcases abs_cases ψ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, Real.cos_neg]
  have hcosn : Real.cos ((n : ℝ) * ψ) = Real.cos ((n : ℝ) * |ψ|) := by
    rcases abs_cases ψ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.cos_neg]
  rw [hcosabs, hcosn]
  have ht0 : (0 : ℝ) ≤ |ψ| := abs_nonneg ψ
  have hπ := Real.pi_pos
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd := dec n hn |ψ| ht0 hψ
  have hc0 : 0 ≤ Real.cos |ψ| := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · linarith
    · nlinarith
  have hhalf : 0 ≤ Real.cos ((n : ℝ) * |ψ| / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have : 0 ≤ (n : ℝ) * |ψ| := by positivity
      linarith
    · linarith
  have hsq : Real.cos ((n : ℝ) * |ψ| / 2) * Real.cos ((n : ℝ) * |ψ| / 2)
      ≤ Real.sqrt (Real.cos |ψ|) ^ n * Real.sqrt (Real.cos |ψ|) ^ n :=
    mul_self_le_mul_self hhalf hd
  have hpow : Real.sqrt (Real.cos |ψ|) ^ n * Real.sqrt (Real.cos |ψ|) ^ n
      = Real.cos |ψ| ^ n := by
    rw [← pow_add, show n + n = 2 * n by ring, pow_mul, Real.sq_sqrt hc0]
  have hcs := Real.cos_sq ((n : ℝ) * |ψ| / 2)
  have hdouble : 2 * ((n : ℝ) * |ψ| / 2) = (n : ℝ) * |ψ| := by ring
  rw [hdouble] at hcs
  rw [hpow] at hsq
  rw [← sq] at hsq
  rw [hcs] at hsq
  linarith

/-! ## The complex form of the decisive estimate -/

/-- `Re(ζ^n) + ‖ζ‖^n ≤ 2c^n` for `ζ = c + iy`, `c = cos(π/n)`, `|y| ≤ sin(π/n)`. -/
theorem re_pow_add_norm_pow_le {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : |y| ≤ chordSin n) :
    ((((chordCos n : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I) ^ n).re
      + ‖((chordCos n : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I‖ ^ n
      ≤ 2 * chordCos n ^ n := by
  rcases eq_or_lt_of_le hn with h2 | h3
  · -- `n = 2`: the segment is the diameter and `c = 0`
    subst h2
    have hc0 : chordCos 2 = 0 := chordCos_eq_zero_of_two
    rw [hc0]
    have hz : ((0 : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I = ((y : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hz]
    have hre : ((((y : ℝ) : ℂ) * Complex.I) ^ 2).re = -(y ^ 2) := by
      have h : (((y : ℝ) : ℂ) * Complex.I) ^ 2 = (((-(y ^ 2) : ℝ)) : ℂ) := by
        rw [mul_pow, Complex.I_sq]
        push_cast
        ring
      rw [h, Complex.ofReal_re]
    have hnorm : ‖((y : ℝ) : ℂ) * Complex.I‖ = |y| := by
      rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one]
    rw [hre, hnorm, sq_abs]
    norm_num
  · -- `3 ≤ n`
    have hn3 : 3 ≤ n := h3
    set c := chordCos n with hcdef
    have hcpos : 0 < c := chordCos_pos hn3
    have hsin := chordSin_nonneg hn
    have hCS := sin_sq_add_cos_sq n
    set ζ : ℂ := ((c : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I with hζdef
    have hy2 : y ^ 2 ≤ chordSin n ^ 2 := by
      have := abs_nonneg y
      nlinarith [sq_abs y, hy]
    set ρ := Real.sqrt (c ^ 2 + y ^ 2) with hρdef
    have hposarg : 0 < c ^ 2 + y ^ 2 := by nlinarith
    have hρpos : 0 < ρ := Real.sqrt_pos.mpr hposarg
    have hρsq : ρ ^ 2 = c ^ 2 + y ^ 2 := Real.sq_sqrt hposarg.le
    set ψ := Real.arctan (y / c) with hψdef
    have hsqrtc : Real.sqrt (c ^ 2) = c := Real.sqrt_sq hcpos.le
    have hkey : Real.sqrt (1 + (y / c) ^ 2) = ρ / c := by
      have h1 : 1 + (y / c) ^ 2 = (c ^ 2 + y ^ 2) / c ^ 2 := by
        field_simp
      rw [h1, Real.sqrt_div hposarg.le, hsqrtc, hρdef]
    have hcosψ : Real.cos ψ = c / ρ := by
      rw [hψdef, Real.cos_arctan, hkey]
      field_simp
    have hsinψ : Real.sin ψ = y / ρ := by
      rw [hψdef, Real.sin_arctan, hkey]
      field_simp
    have e1 : ρ * Real.cos ψ = c := by
      rw [hcosψ]; field_simp
    have e2 : ρ * Real.sin ψ = y := by
      rw [hsinψ]; field_simp
    -- `|ψ| ≤ π/n`
    have htan : |y / c| ≤ Real.tan (angle n) := by
      rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcpos]
      have hdiv : |y| / c ≤ chordSin n / c := by
        rw [div_le_div_iff₀ hcpos hcpos]
        nlinarith
      simpa [chordSin, chordCos, hcdef] using hdiv
    have hangle_lt : angle n < Real.pi / 2 := by
      have := angle_le_pi_div_three hn3
      have := Real.pi_pos
      linarith
    have hangle_gt : -(Real.pi / 2) < angle n := by
      have := angle_pos hn
      have := Real.pi_pos
      linarith
    have harctan : Real.arctan (Real.tan (angle n)) = angle n :=
      Real.arctan_tan hangle_gt hangle_lt
    have hψabs : |ψ| ≤ angle n := by
      rcases abs_le.mp htan with ⟨hlow, hhigh⟩
      apply abs_le.mpr
      constructor
      · have h := Real.arctan_mono hlow
        rw [Real.arctan_neg, harctan] at h
        exact h
      · have h := Real.arctan_mono hhigh
        rwa [harctan] at h
    have hnψ : (n : ℝ) * |ψ| ≤ Real.pi := by
      have hcast := cast_mul_angle hn
      have : (n : ℝ) * |ψ| ≤ (n : ℝ) * angle n :=
        mul_le_mul_of_nonneg_left hψabs (cast_pos hn).le
      linarith [hcast]
    -- polar form
    have hζexp : ζ = ((ρ : ℝ) : ℂ) * Complex.exp (((ψ : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hζdef, ← e1, ← e2]
      push_cast
      ring
    have hnorm : ‖ζ‖ = ρ := by
      rw [hζexp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hpow : ζ ^ n
        = (((ρ ^ n : ℝ)) : ℂ) * Complex.exp (((((n : ℝ) * ψ : ℝ)) : ℂ) * Complex.I) := by
      rw [hζexp, mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow]
      congr 1
      push_cast
      ring
    have hre : (ζ ^ n).re = ρ ^ n * Real.cos ((n : ℝ) * ψ) := by
      rw [hpow]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.exp_ofReal_mul_I_re]
    rw [hre, hnorm]
    have hdec := one_add_cos_le hn hnψ
    have hρn : (0 : ℝ) ≤ ρ ^ n := by positivity
    calc ρ ^ n * Real.cos ((n : ℝ) * ψ) + ρ ^ n
        = ρ ^ n * (1 + Real.cos ((n : ℝ) * ψ)) := by ring
      _ ≤ ρ ^ n * (2 * Real.cos ψ ^ n) := by
          exact mul_le_mul_of_nonneg_left hdec hρn
      _ = 2 * (ρ * Real.cos ψ) ^ n := by rw [mul_pow]; ring
      _ = 2 * c ^ n := by rw [e1]

/-! ## The chord maximum -/

theorem chordPoint_eq (n : ℕ) (s u : ℝ) :
    chordPoint n s u
      = (s : ℂ) * halfRoot n *
          (((chordCos n : ℝ) : ℂ) + (((2 * u - 1) * chordSin n : ℝ) : ℂ) * Complex.I) := by
  have hCS : ((chordSin n : ℝ) : ℂ) ^ 2 + ((chordCos n : ℝ) : ℂ) ^ 2 = 1 := by
    have := sin_sq_add_cos_sq n
    exact_mod_cast congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) this
  simp only [chordPoint, chordOmega, halfRoot_eq]
  push_cast
  linear_combination
    ((s : ℂ) * (1 - (u : ℂ)) * ((chordSin n : ℝ) : ℂ) ^ 2) * Complex.I_sq
      - ((s : ℂ) * (1 - (u : ℂ))) * hCS

theorem chordPoint_zero (n : ℕ) (s : ℝ) : chordPoint n s 0 = (s : ℂ) := by
  simp [chordPoint]

theorem chordPoint_one (n : ℕ) (s : ℝ) : chordPoint n s 1 = (s : ℂ) * chordOmega n := by
  simp [chordPoint]

/-- The purely real inequality behind the chord maximum. -/
private theorem chord_key_inequality {S R a b k : ℝ}
    (hS0 : 0 < S) (hSR : S ≤ R) (hak : k ≤ a) (ha1 : a ≤ 1) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hlem : b + a ≤ 2 * k) :
    (S * b + R) ^ 2 + S ^ 2 * (a ^ 2 - b ^ 2) ≤ (R + S * k) ^ 2 := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le hS0 hSR
  have h1 : (0 : ℝ) ≤ a - k := by linarith
  have h2 : S * (k + a) ≤ 2 * R := by
    have hle : S * (k + a) ≤ S * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hS0.le
    linarith
  have h3 : (0 : ℝ) ≤ (a - k) * (2 * R - S * (k + a)) := mul_nonneg h1 (by linarith)
  have h4 : (0 : ℝ) ≤ 2 * k - a - b := by linarith
  nlinarith [mul_nonneg (mul_nonneg hS0.le hR0.le) h4, mul_nonneg hS0.le h3]

/-- The assembled complex bound, for an arbitrary `ζ` obeying the ζ-estimates. -/
private theorem norm_combo_le {n : ℕ} {s r k : ℝ} {ζ : ℂ}
    (hs : 0 < s) (hsr : s ≤ r) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hζ1 : ‖ζ‖ ≤ 1) (hζk : k ≤ ‖ζ‖ ^ n)
    (hlem : (ζ ^ n).re + ‖ζ‖ ^ n ≤ 2 * k) :
    ‖((s : ℝ) : ℂ) ^ n * ζ ^ n + ((r : ℝ) : ℂ) ^ n‖ ≤ r ^ n + s ^ n * k := by
  have hS0 : (0 : ℝ) < s ^ n := by positivity
  have hSR : s ^ n ≤ r ^ n := pow_le_pow_left₀ hs.le hsr n
  have hnn : (0 : ℝ) ≤ ‖ζ‖ := norm_nonneg _
  have ha1 : ‖ζ‖ ^ n ≤ 1 := by
    calc ‖ζ‖ ^ n ≤ 1 ^ n := pow_le_pow_left₀ hnn hζ1 n
      _ = 1 := one_pow n
  have hsre : (((s : ℝ) : ℂ) ^ n).re = s ^ n := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hsim : (((s : ℝ) : ℂ) ^ n).im = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hrre : (((r : ℝ) : ℂ) ^ n).re = r ^ n := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hrim : (((r : ℝ) : ℂ) ^ n).im = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hWre : (((s : ℝ) : ℂ) ^ n * ζ ^ n + ((r : ℝ) : ℂ) ^ n).re
      = s ^ n * (ζ ^ n).re + r ^ n := by
    rw [Complex.add_re, Complex.mul_re, hsre, hsim, hrre]
    ring
  have hWim : (((s : ℝ) : ℂ) ^ n * ζ ^ n + ((r : ℝ) : ℂ) ^ n).im
      = s ^ n * (ζ ^ n).im := by
    rw [Complex.add_im, Complex.mul_im, hsre, hsim, hrim]
    ring
  have hnormsq_n : (ζ ^ n).re ^ 2 + (ζ ^ n).im ^ 2 = (‖ζ‖ ^ n) ^ 2 := by
    have h := Complex.sq_norm (ζ ^ n)
    rw [norm_pow] at h
    rw [h, Complex.normSq_apply]
    ring
  have hWsq : ‖((s : ℝ) : ℂ) ^ n * ζ ^ n + ((r : ℝ) : ℂ) ^ n‖ ^ 2
      = (s ^ n * (ζ ^ n).re + r ^ n) ^ 2
        + (s ^ n) ^ 2 * ((‖ζ‖ ^ n) ^ 2 - ((ζ ^ n).re) ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hWre, hWim]
    linear_combination (s ^ n) ^ 2 * hnormsq_n
  have hkey := chord_key_inequality (S := s ^ n) (R := r ^ n)
    (a := ‖ζ‖ ^ n) (b := (ζ ^ n).re) (k := k) hS0 hSR hζk ha1 hk0 hk1 hlem
  have hM0 : (0 : ℝ) ≤ r ^ n + s ^ n * k :=
    add_nonneg (le_trans hS0.le hSR) (mul_nonneg hS0.le hk0)
  nlinarith [norm_nonneg (((s : ℝ) : ℂ) ^ n * ζ ^ n + ((r : ℝ) : ℂ) ^ n), hWsq, hkey, hM0]

theorem norm_zeta_sq (n : ℕ) (y : ℝ) :
    ‖((chordCos n : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I‖ ^ 2 = chordCos n ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

theorem norm_zeta_le_one {n : ℕ} (hn : 2 ≤ n) {y : ℝ} (hy : |y| ≤ chordSin n) :
    ‖((chordCos n : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I‖ ≤ 1 := by
  have h := norm_zeta_sq n y
  have hCS := sin_sq_add_cos_sq n
  have hy2 : y ^ 2 ≤ chordSin n ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
  nlinarith [norm_nonneg (((chordCos n : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)]

theorem cos_le_norm_zeta {n : ℕ} (hn : 2 ≤ n) (y : ℝ) :
    chordCos n ≤ ‖((chordCos n : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I‖ := by
  have h := norm_zeta_sq n y
  have hcn := chordCos_nonneg hn
  nlinarith [norm_nonneg (((chordCos n : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I), sq_nonneg y]

/-- **The companion's chord maximum, upper bound.**
`|z^n - r^n| ≤ r^n + (sc)^n` for every `z` on the segment `[s, sω]`, `0 < s ≤ r`. -/
theorem chord_norm_le {n : ℕ} (hn : 2 ≤ n) {s r u : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(chordPoint n s u) ^ n - ((r : ℝ) : ℂ) ^ n‖ ≤ r ^ n + (s * chordCos n) ^ n := by
  have hcn : 0 ≤ chordCos n := chordCos_nonneg hn
  have hsin := chordSin_nonneg hn
  have hy : |(2 * u - 1) * chordSin n| ≤ chordSin n := by
    rw [abs_mul, abs_of_nonneg hsin]
    have h1 : |2 * u - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (2 * u - 1)]
  have hid : (chordPoint n s u) ^ n - ((r : ℝ) : ℂ) ^ n
      = -(((s : ℝ) : ℂ) ^ n *
          (((chordCos n : ℝ) : ℂ) + (((2 * u - 1) * chordSin n : ℝ) : ℂ) * Complex.I) ^ n
          + ((r : ℝ) : ℂ) ^ n) := by
    rw [chordPoint_eq, mul_pow, mul_pow, halfRoot_pow hn]
    ring
  rw [hid, norm_neg]
  have hk1 : chordCos n ^ n ≤ 1 := by
    calc chordCos n ^ n ≤ 1 ^ n := pow_le_pow_left₀ hcn (chordCos_le_one n) n
      _ = 1 := one_pow n
  have hζk : chordCos n ^ n
      ≤ ‖((chordCos n : ℝ) : ℂ) + (((2 * u - 1) * chordSin n : ℝ) : ℂ) * Complex.I‖ ^ n :=
    pow_le_pow_left₀ hcn (cos_le_norm_zeta hn _) n
  have hmain := norm_combo_le (n := n) (s := s) (r := r) (k := chordCos n ^ n)
    hs hsr (pow_nonneg hcn n) hk1 (norm_zeta_le_one hn hy) hζk
    (re_pow_add_norm_pow_le hn hy)
  rw [mul_pow]
  exact hmain

/-- The value at the midpoint of `[s, sω]` is exactly `r^n + (sc)^n`. -/
theorem chord_norm_midpoint {n : ℕ} (hn : 2 ≤ n) (s r : ℝ) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    ‖(chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = r ^ n + (s * chordCos n) ^ n := by
  have hcn : 0 ≤ chordCos n := chordCos_nonneg hn
  have hid : (chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n
      = -((((s * chordCos n) ^ n + r ^ n : ℝ)) : ℂ) := by
    rw [chordPoint_eq, mul_pow, mul_pow, halfRoot_pow hn]
    push_cast
    ring
  rw [hid, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  ring

/-! ## The threshold `r_*` -/

theorem chordThreshold_pow {n : ℕ} (hn : 2 ≤ n) :
    chordThreshold n ^ n * (1 + chordCos n ^ n) = 1 := by
  have hK : (0 : ℝ) < 1 + chordCos n ^ n := by
    have := chordCos_nonneg hn
    positivity
  have hn0 : ((n : ℝ)) ≠ 0 := (cast_pos hn).ne'
  have h1 : chordThreshold n ^ n = (1 + chordCos n ^ n) ^ (-(1 : ℝ)) := by
    rw [chordThreshold, ← Real.rpow_natCast ((1 + chordCos n ^ n) ^ (-((n : ℝ)⁻¹))) n,
      ← Real.rpow_mul hK.le]
    congr 1
    field_simp
  rw [h1, Real.rpow_neg_one]
  field_simp

theorem chordThreshold_pos {n : ℕ} (hn : 2 ≤ n) : 0 < chordThreshold n := by
  have hK : (0 : ℝ) < 1 + chordCos n ^ n := by
    have := chordCos_nonneg hn
    positivity
  rw [chordThreshold]
  exact Real.rpow_pos_of_pos hK _

/-- `r < r_*` is exactly the paper's switch condition `r^n(1 + c^n) < 1`. -/
theorem lt_chordThreshold_iff {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    r < chordThreshold n ↔ r ^ n * (1 + chordCos n ^ n) < 1 := by
  have hK : (0 : ℝ) < 1 + chordCos n ^ n := by
    have := chordCos_nonneg hn
    positivity
  have hpow := chordThreshold_pow hn
  have hTpos := chordThreshold_pos hn
  have hn0 : n ≠ 0 := by omega
  constructor
  · intro h
    have : r ^ n < chordThreshold n ^ n := by
      apply pow_lt_pow_left₀ h hr hn0
    nlinarith
  · intro h
    by_contra hcon
    push_neg at hcon
    have : chordThreshold n ^ n ≤ r ^ n := pow_le_pow_left₀ hTpos.le hcon n
    nlinarith

/-! ## `ε` and the inner radius -/

theorem chordEps_pow {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : r ^ n ≤ 1) :
    chordEps n r ^ n = 1 - r ^ n := by
  have h1 : (0 : ℝ) ≤ 1 - r ^ n := by linarith
  have hn0 : ((n : ℝ)) ≠ 0 := (cast_pos hn).ne'
  rw [chordEps, ← Real.rpow_natCast ((1 - r ^ n) ^ ((n : ℝ)⁻¹)) n, ← Real.rpow_mul h1,
    inv_mul_cancel₀ hn0, Real.rpow_one]

theorem chordEps_pos {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : r ^ n < 1) : 0 < chordEps n r := by
  rw [chordEps]
  exact Real.rpow_pos_of_pos (by linarith) _

theorem innerRadius_pos {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr : r ^ n < 1) :
    0 < innerRadius n r :=
  div_pos (chordEps_pos (by omega) hr) (chordCos_pos hn)

/-- `(tc)^n = ε^n = 1 - r^n`: the inner crossing chord sits exactly on the
closed unit lemniscate. -/
theorem innerRadius_mul_cos_pow {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr : r ^ n ≤ 1) :
    (innerRadius n r * chordCos n) ^ n = 1 - r ^ n := by
  have hc := (chordCos_pos hn).ne'
  rw [innerRadius, div_mul_cancel₀ _ hc]
  exact chordEps_pow (by omega) hr

/-- `t ≤ r` is exactly the switch condition `1 ≤ r^n(1 + c^n)`. -/
theorem innerRadius_le {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r ^ n < 1)
    (hswitch : 1 ≤ r ^ n * (1 + chordCos n ^ n)) : innerRadius n r ≤ r := by
  have hc := chordCos_pos hn
  have ht0 := (innerRadius_pos hn hr1).le
  have hn0 : n ≠ 0 := by omega
  have hpow : (innerRadius n r * chordCos n) ^ n ≤ (r * chordCos n) ^ n := by
    rw [innerRadius_mul_cos_pow hn hr1.le, mul_pow]
    nlinarith
  have hbase : innerRadius n r * chordCos n ≤ r * chordCos n := by
    by_contra hcon
    push_neg at hcon
    have := pow_lt_pow_left₀ hcon (by positivity) hn0
    linarith
  exact le_of_mul_le_mul_right (by linarith) hc

/-! ## Polygonal paths -/

/-- A single affine leg has extended variation at most its length. -/
theorem affine_variation_le (p v : ℂ) {x y : ℝ} (hxy : x ≤ y) :
    eVariationOn (PaperCurve.affine p v) (Icc x y) ≤ ENNReal.ofReal ((y - x) * ‖v‖) := by
  have hl : LipschitzOnWith ‖v‖₊ (PaperCurve.affine p v) univ :=
    (PaperCurve.affine_lipschitz p v).lipschitzOnWith
  have hm : MapsTo (id : ℝ → ℝ) (Icc x y) univ := fun t _ => trivial
  have hv := hl.comp_eVariationOn_le hm
  have hid : eVariationOn (id : ℝ → ℝ) (Icc x y) ≤ ENNReal.ofReal (y - x) := by
    have h := (monotone_id.monotoneOn (univ : Set ℝ)).eVariationOn_le
      (mem_univ x) (mem_univ y)
    simpa only [univ_inter, id_eq] using h
  calc eVariationOn (PaperCurve.affine p v) (Icc x y)
      ≤ (‖v‖₊ : ℝ≥0∞) * eVariationOn (id : ℝ → ℝ) (Icc x y) := by
        simpa only [Function.comp_id] using hv
    _ ≤ (‖v‖₊ : ℝ≥0∞) * ENNReal.ofReal (y - x) := by
        exact mul_le_mul_left' hid _
    _ = ENNReal.ofReal (‖v‖ * (y - x)) := by
        rw [show ((‖v‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖v‖ by simp [enorm_eq_nnnorm],
          ← ENNReal.ofReal_mul (norm_nonneg v)]
    _ = ENNReal.ofReal ((y - x) * ‖v‖) := by rw [mul_comm]

/-- A three–leg polygonal path `z₀ → z₁ → z₂ → z₃`, parametrised on `[0,2]`
with breakpoints at `2/3` and `4/3`. -/
def leg3 (z₀ z₁ z₂ z₃ : ℂ) (t : ℝ) : ℂ :=
  z₀ + ((min (max (3 * t / 2) 0) 1 : ℝ) : ℂ) * (z₁ - z₀)
     + ((min (max (3 * t / 2 - 1) 0) 1 : ℝ) : ℂ) * (z₂ - z₁)
     + ((min (max (3 * t / 2 - 2) 0) 1 : ℝ) : ℂ) * (z₃ - z₂)

theorem leg3_continuous (z₀ z₁ z₂ z₃ : ℂ) : Continuous (leg3 z₀ z₁ z₂ z₃) := by
  unfold leg3
  fun_prop

@[simp] theorem leg3_zero (z₀ z₁ z₂ z₃ : ℂ) : leg3 z₀ z₁ z₂ z₃ 0 = z₀ := by
  norm_num [leg3]

@[simp] theorem leg3_two (z₀ z₁ z₂ z₃ : ℂ) : leg3 z₀ z₁ z₂ z₃ 2 = z₃ := by
  norm_num [leg3]

private theorem min_zero_one : min (0 : ℝ) 1 = 0 := by norm_num

theorem leg3_first {z₀ z₁ z₂ z₃ : ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 / 3) :
    leg3 z₀ z₁ z₂ z₃ t = z₀ + ((3 * t / 2 : ℝ) : ℂ) * (z₁ - z₀) := by
  have h1 : max (3 * t / 2) 0 = 3 * t / 2 := max_eq_left (by linarith)
  have h2 : min (3 * t / 2) 1 = 3 * t / 2 := min_eq_left (by linarith)
  have h3 : max (3 * t / 2 - 1) 0 = 0 := max_eq_right (by linarith)
  have h4 : max (3 * t / 2 - 2) 0 = 0 := max_eq_right (by linarith)
  simp only [leg3, h1, h2, h3, h4, min_zero_one, Complex.ofReal_zero, zero_mul, add_zero]

theorem leg3_second {z₀ z₁ z₂ z₃ : ℂ} {t : ℝ} (ht0 : 2 / 3 ≤ t) (ht : t ≤ 4 / 3) :
    leg3 z₀ z₁ z₂ z₃ t = z₁ + ((3 * t / 2 - 1 : ℝ) : ℂ) * (z₂ - z₁) := by
  have h1 : max (3 * t / 2) 0 = 3 * t / 2 := max_eq_left (by linarith)
  have h2 : min (3 * t / 2) 1 = 1 := min_eq_right (by linarith)
  have h3 : max (3 * t / 2 - 1) 0 = 3 * t / 2 - 1 := max_eq_left (by linarith)
  have h4 : min (3 * t / 2 - 1) 1 = 3 * t / 2 - 1 := min_eq_left (by linarith)
  have h5 : max (3 * t / 2 - 2) 0 = 0 := max_eq_right (by linarith)
  simp only [leg3, h1, h2, h3, h4, h5, min_zero_one, Complex.ofReal_zero, zero_mul, add_zero]
  push_cast
  ring

theorem leg3_third {z₀ z₁ z₂ z₃ : ℂ} {t : ℝ} (ht0 : 4 / 3 ≤ t) (ht : t ≤ 2) :
    leg3 z₀ z₁ z₂ z₃ t = z₂ + ((3 * t / 2 - 2 : ℝ) : ℂ) * (z₃ - z₂) := by
  have h1 : max (3 * t / 2) 0 = 3 * t / 2 := max_eq_left (by linarith)
  have h2 : min (3 * t / 2) 1 = 1 := min_eq_right (by linarith)
  have h3 : max (3 * t / 2 - 1) 0 = 3 * t / 2 - 1 := max_eq_left (by linarith)
  have h4 : min (3 * t / 2 - 1) 1 = 1 := min_eq_right (by linarith)
  have h5 : max (3 * t / 2 - 2) 0 = 3 * t / 2 - 2 := max_eq_left (by linarith)
  have h6 : min (3 * t / 2 - 2) 1 = 3 * t / 2 - 2 := min_eq_left (by linarith)
  simp only [leg3, h1, h2, h3, h4, h5, h6]
  push_cast
  ring

theorem leg3_mem {z₀ z₁ z₂ z₃ : ℂ} {S : Set ℂ}
    (h₁ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → z₀ + (u : ℂ) * (z₁ - z₀) ∈ S)
    (h₂ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → z₁ + (u : ℂ) * (z₂ - z₁) ∈ S)
    (h₃ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → z₂ + (u : ℂ) * (z₃ - z₂) ∈ S)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : leg3 z₀ z₁ z₂ z₃ t ∈ S := by
  obtain ⟨ht0, ht2⟩ := ht
  by_cases h : t ≤ 2 / 3
  · rw [leg3_first ht0 h]
    exact h₁ (3 * t / 2) (by linarith) (by linarith)
  · push_neg at h
    by_cases h' : t ≤ 4 / 3
    · rw [leg3_second (le_of_lt h) h']
      exact h₂ (3 * t / 2 - 1) (by linarith) (by linarith)
    · push_neg at h'
      rw [leg3_third (le_of_lt h') ht2]
      exact h₃ (3 * t / 2 - 2) (by linarith) (by linarith)

theorem leg3_variation_le (z₀ z₁ z₂ z₃ : ℂ) :
    eVariationOn (leg3 z₀ z₁ z₂ z₃) (Icc (0 : ℝ) 2)
      ≤ ENNReal.ofReal (‖z₁ - z₀‖ + ‖z₂ - z₁‖ + ‖z₃ - z₂‖) := by
  have hsplit1 := eVariationOn.Icc_add_Icc (leg3 z₀ z₁ z₂ z₃) (s := univ)
    (a := (0 : ℝ)) (b := (2 / 3 : ℝ)) (c := (2 : ℝ)) (by norm_num) (by norm_num) (by trivial)
  have hsplit2 := eVariationOn.Icc_add_Icc (leg3 z₀ z₁ z₂ z₃) (s := univ)
    (a := (2 / 3 : ℝ)) (b := (4 / 3 : ℝ)) (c := (2 : ℝ)) (by norm_num) (by norm_num) (by trivial)
  simp only [univ_inter] at hsplit1 hsplit2
  have hA : eVariationOn (leg3 z₀ z₁ z₂ z₃) (Icc (0 : ℝ) (2 / 3))
      ≤ ENNReal.ofReal ‖z₁ - z₀‖ := by
    have heq : EqOn (leg3 z₀ z₁ z₂ z₃)
        (PaperCurve.affine z₀ (((3 : ℝ) / 2 : ℂ) * (z₁ - z₀))) (Icc (0 : ℝ) (2 / 3)) := by
      intro t ht
      rw [leg3_first ht.1 ht.2, PaperCurve.affine]
      push_cast
      ring
    rw [eVariationOn.congr heq]
    refine le_trans (affine_variation_le _ _ (by norm_num)) ?_
    rw [norm_mul]
    have : ‖((3 : ℝ) / 2 : ℂ)‖ = 3 / 2 := by
      norm_num [Complex.norm_ofNat]
    rw [this]
    apply le_of_eq
    congr 1
    ring
  have hB : eVariationOn (leg3 z₀ z₁ z₂ z₃) (Icc (2 / 3 : ℝ) (4 / 3))
      ≤ ENNReal.ofReal ‖z₂ - z₁‖ := by
    have heq : EqOn (leg3 z₀ z₁ z₂ z₃)
        (PaperCurve.affine (z₁ - ((3 : ℝ) / 2 : ℂ) * (z₂ - z₁) * (2 / 3))
          (((3 : ℝ) / 2 : ℂ) * (z₂ - z₁))) (Icc (2 / 3 : ℝ) (4 / 3)) := by
      intro t ht
      rw [leg3_second ht.1 ht.2, PaperCurve.affine]
      push_cast
      ring
    rw [eVariationOn.congr heq]
    refine le_trans (affine_variation_le _ _ (by norm_num)) ?_
    rw [norm_mul]
    have : ‖((3 : ℝ) / 2 : ℂ)‖ = 3 / 2 := by
      norm_num [Complex.norm_ofNat]
    rw [this]
    apply le_of_eq
    congr 1
    ring
  have hC : eVariationOn (leg3 z₀ z₁ z₂ z₃) (Icc (4 / 3 : ℝ) 2)
      ≤ ENNReal.ofReal ‖z₃ - z₂‖ := by
    have heq : EqOn (leg3 z₀ z₁ z₂ z₃)
        (PaperCurve.affine (z₂ - ((3 : ℝ) / 2 : ℂ) * (z₃ - z₂) * (4 / 3))
          (((3 : ℝ) / 2 : ℂ) * (z₃ - z₂))) (Icc (4 / 3 : ℝ) 2) := by
      intro t ht
      rw [leg3_third ht.1 ht.2, PaperCurve.affine]
      push_cast
      ring
    rw [eVariationOn.congr heq]
    refine le_trans (affine_variation_le _ _ (by norm_num)) ?_
    rw [norm_mul]
    have : ‖((3 : ℝ) / 2 : ℂ)‖ = 3 / 2 := by
      norm_num [Complex.norm_ofNat]
    rw [this]
    apply le_of_eq
    congr 1
    ring
  have hfin : eVariationOn (leg3 z₀ z₁ z₂ z₃) (Icc (0 : ℝ) 2)
      ≤ ENNReal.ofReal ‖z₁ - z₀‖ + (ENNReal.ofReal ‖z₂ - z₁‖ + ENNReal.ofReal ‖z₃ - z₂‖) := by
    rw [← hsplit1, ← hsplit2]
    exact add_le_add hA (add_le_add hB hC)
  refine hfin.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (norm_nonneg (z₂ - z₁)) (norm_nonneg (z₃ - z₂)),
    ← ENNReal.ofReal_add (norm_nonneg (z₁ - z₀)) (by positivity)]
  congr 1
  ring

theorem leg3_boundedVariation (z₀ z₁ z₂ z₃ : ℂ) :
    BoundedVariationOn (leg3 z₀ z₁ z₂ z₃) (Icc (0 : ℝ) 2) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (leg3_variation_le z₀ z₁ z₂ z₃)

/-- The three-leg connector, as the tree's `ConnectedBelow`. -/
theorem connectedBelow_of_leg3 {f : ℂ → ℂ} {R L : ℝ} {z₀ z₁ z₂ z₃ : ℂ}
    (h₁ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖f (z₀ + (u : ℂ) * (z₁ - z₀))‖ < R)
    (h₂ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖f (z₁ + (u : ℂ) * (z₂ - z₁))‖ < R)
    (h₃ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖f (z₂ + (u : ℂ) * (z₃ - z₂))‖ < R)
    (hL : ‖z₁ - z₀‖ + ‖z₂ - z₁‖ + ‖z₃ - z₂‖ < L) :
    PaperCurve.ConnectedBelow f R L z₀ z₃ := by
  refine ⟨leg3 z₀ z₁ z₂ z₃, (leg3_continuous z₀ z₁ z₂ z₃).continuousOn,
    leg3_zero _ _ _ _, leg3_two _ _ _ _, ?_, leg3_boundedVariation _ _ _ _, ?_⟩
  · intro t ht
    exact leg3_mem (S := {z | ‖f z‖ < R}) h₁ h₂ h₃ ht
  · refine lt_of_le_of_lt (leg3_variation_le z₀ z₁ z₂ z₃) ?_
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hL)).mpr hL

/-! ## The two constructions -/

/-- **Below the switch: the adjacent-root chord itself works.**
For `r^n(1 + c^n) < 1`, that is `r < r_*`, the straight chord between the
adjacent zeros `r` and `rω` stays inside `{|z^n - r^n| < 1}` and has length
below `2`. -/
theorem adjacent_chord_connected {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hswitch : r ^ n * (1 + chordCos n ^ n) < 1) :
    PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := by
  have hcn : 0 ≤ chordCos n := chordCos_nonneg hn
  have hbound : ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      ‖(chordPoint n r v) ^ n - ((r : ℝ) : ℂ) ^ n‖ < 1 := by
    intro v hv0 hv1
    have h := chord_norm_le hn hr0 le_rfl hv0 hv1
    have : r ^ n + (r * chordCos n) ^ n = r ^ n * (1 + chordCos n ^ n) := by
      rw [mul_pow]; ring
    rw [this] at h
    linarith
  apply PaperCurve.connectedBelow_of_spokes (h := chordPoint n r (1 / 2))
  · intro u hu0 hu1
    have hrw : chordPoint n r (1 / 2) + (u : ℂ) * (((r : ℝ) : ℂ) - chordPoint n r (1 / 2))
        = chordPoint n r ((1 - u) / 2) := by
      simp only [chordPoint]
      push_cast
      ring
    rw [hrw]
    exact hbound _ (by linarith) (by linarith)
  · intro u hu0 hu1
    have hrw : chordPoint n r (1 / 2)
        + (u : ℂ) * (((r : ℝ) : ℂ) * chordOmega n - chordPoint n r (1 / 2))
        = chordPoint n r ((1 + u) / 2) := by
      simp only [chordPoint]
      push_cast
      ring
    rw [hrw]
    exact hbound _ (by linarith) (by linarith)
  · have h1 : chordPoint n r (1 / 2) - ((r : ℝ) : ℂ)
        = ((r : ℝ) : ℂ) * (chordOmega n - 1) * ((1 : ℂ) / 2) := by
      simp only [chordPoint]; push_cast; ring
    have h2 : ((r : ℝ) : ℂ) * chordOmega n - chordPoint n r (1 / 2)
        = ((r : ℝ) : ℂ) * (chordOmega n - 1) * ((1 : ℂ) / 2) := by
      simp only [chordPoint]; push_cast; ring
    rw [h1, h2]
    have hnorm : ‖((r : ℝ) : ℂ) * (chordOmega n - 1) * ((1 : ℂ) / 2)‖ ≤ r := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      have h3 : ‖chordOmega n - 1‖ ≤ 2 := by
        rw [← norm_neg]
        simpa using norm_one_sub_chordOmega_le n
      have h4 : ‖((1 : ℂ) / 2)‖ = 1 / 2 := by norm_num
      rw [h4]
      nlinarith [norm_nonneg (chordOmega n - 1), hr0]
    linarith

/-- **At the switch.**  When `r^n(1 + c^n) = 1`, that is `r = r_*`, the
adjacent-root chord stays in the CLOSED lemniscate and attains `|f| = 1`
exactly at its midpoint. -/
theorem threshold_chord_touches {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hEq : r ^ n * (1 + chordCos n ^ n) = 1) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖(chordPoint n r u) ^ n - ((r : ℝ) : ℂ) ^ n‖ ≤ 1) ∧
      ‖(chordPoint n r (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = 1 := by
  have hsum : r ^ n + (r * chordCos n) ^ n = 1 := by
    rw [mul_pow] at *
    linarith [hEq]
  constructor
  · intro u hu0 hu1
    have h := chord_norm_le hn hr0 le_rfl hu0 hu1
    linarith
  · rw [chord_norm_midpoint hn r r hr0.le hr0.le]
    exact hsum

/-- **Above the switch: the inner crossing chord is maximal.**
The inner chord at radius `t = ε/c` lies in the closed lemniscate and attains
`|f| = 1` at its midpoint; any larger radius `s ≤ r` already escapes there. -/
theorem inner_chord_maximal {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r ^ n < 1)
    (hswitch : 1 ≤ r ^ n * (1 + chordCos n ^ n)) :
    ‖(chordPoint n (innerRadius n r) (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = 1 ∧
      (∀ s : ℝ, innerRadius n r < s → s ≤ r →
        1 < ‖(chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖) := by
  have hn2 : 2 ≤ n := by omega
  have ht0 := innerRadius_pos hn hr1
  have hc := chordCos_pos hn
  have hmid := innerRadius_mul_cos_pow hn hr1.le
  constructor
  · rw [chord_norm_midpoint hn2 _ r ht0.le hr0.le, hmid]
    ring
  · intro s hs hsr
    rw [chord_norm_midpoint hn2 s r (by linarith) hr0.le]
    have hstrict : (innerRadius n r * chordCos n) ^ n < (s * chordCos n) ^ n := by
      apply pow_lt_pow_left₀ _ (by positivity) (by omega)
      nlinarith
    rw [hmid] at hstrict
    linarith

/-- **Above the switch: the contracted three-leg path.**
For `r ≥ r_*` and any contraction factor `0 < lam < 1`, the path
`r → lam·t → lam·t·ω → rω` lies strictly inside `{|z^n - r^n| < 1}` and has
length strictly below `2`. -/
theorem inner_path_connected {n : ℕ} (hn : 3 ≤ n) {r lam : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hswitch : 1 ≤ r ^ n * (1 + chordCos n ^ n)) (hl0 : 0 < lam) (hl1 : lam < 1) :
    PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hrn : r ^ n < 1 := by
    calc r ^ n < 1 ^ n := pow_lt_pow_left₀ hr1 hr0.le hn0
      _ = 1 := one_pow n
  have hrn0 : 0 < r ^ n := by positivity
  have ht0 := innerRadius_pos hn hrn
  have htr := innerRadius_le hn hr0 hrn hswitch
  set t := innerRadius n r with htdef
  set q := lam * t with hqdef
  have hq0 : 0 < q := by positivity
  have hqr : q ≤ r := by nlinarith
  have hqt : q < t := by nlinarith
  -- the three vertices
  set z₀ : ℂ := ((r : ℝ) : ℂ) with hz₀
  set z₁ : ℂ := ((q : ℝ) : ℂ) with hz₁
  set z₂ : ℂ := ((q : ℝ) : ℂ) * chordOmega n with hz₂
  set z₃ : ℂ := ((r : ℝ) : ℂ) * chordOmega n with hz₃
  have hradial : ∀ x : ℝ, 0 ≤ x → x ≤ r →
      ‖((x : ℝ) : ℂ) ^ n - ((r : ℝ) : ℂ) ^ n‖ < 1 := by
    intro x hx0 hxr
    have h : ((x : ℝ) : ℂ) ^ n - ((r : ℝ) : ℂ) ^ n = (((x ^ n - r ^ n : ℝ)) : ℂ) := by
      push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs]
    have hxn : x ^ n ≤ r ^ n := pow_le_pow_left₀ hx0 hxr n
    have hxn0 : 0 ≤ x ^ n := by positivity
    rw [abs_of_nonpos (by linarith)]
    linarith
  apply connectedBelow_of_leg3 (z₁ := z₁) (z₂ := z₂)
  · -- first radial leg
    intro u hu0 hu1
    have hrw : z₀ + (u : ℂ) * (z₁ - z₀) = (((r + u * (q - r) : ℝ)) : ℂ) := by
      rw [hz₀, hz₁]; push_cast; ring
    rw [hrw]
    exact hradial _ (by nlinarith) (by nlinarith)
  · -- the crossing chord
    intro u hu0 hu1
    have hrw : z₁ + (u : ℂ) * (z₂ - z₁) = chordPoint n q u := by
      rw [hz₁, hz₂, chordPoint]; push_cast; ring
    rw [hrw]
    have h := chord_norm_le hn2 hq0 hqr hu0 hu1
    have hqc : (q * chordCos n) ^ n = lam ^ n * (1 - r ^ n) := by
      rw [hqdef, htdef, mul_assoc, mul_pow, innerRadius_mul_cos_pow hn hrn.le]
    have hlam : lam ^ n < 1 := by
      calc lam ^ n < 1 ^ n := pow_lt_pow_left₀ hl1 hl0.le hn0
        _ = 1 := one_pow n
    rw [hqc] at h
    nlinarith
  · -- second radial leg
    intro u hu0 hu1
    have hrw : z₂ + (u : ℂ) * (z₃ - z₂)
        = chordOmega n * (((q + u * (r - q) : ℝ)) : ℂ) := by
      rw [hz₂, hz₃]; push_cast; ring
    rw [hrw, mul_pow, chordOmega_pow hn2, one_mul]
    exact hradial _ (by nlinarith) (by nlinarith)
  · -- the length
    have hA : ‖z₁ - z₀‖ = r - q := by
      have h : z₁ - z₀ = (((q - r : ℝ)) : ℂ) := by rw [hz₀, hz₁]; push_cast; ring
      rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hC : ‖z₃ - z₂‖ = r - q := by
      have h : z₃ - z₂ = chordOmega n * (((r - q : ℝ)) : ℂ) := by
        rw [hz₂, hz₃]; push_cast; ring
      rw [h, norm_mul, norm_chordOmega, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
    have hB : ‖z₂ - z₁‖ ≤ 2 * q := by
      have h : z₂ - z₁ = ((q : ℝ) : ℂ) * (chordOmega n - 1) := by
        rw [hz₁, hz₂]; ring
      rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
      have h3 : ‖chordOmega n - 1‖ ≤ 2 := by
        rw [← norm_neg]
        simpa using norm_one_sub_chordOmega_le n
      nlinarith
    rw [hA, hC]
    linarith

/-! ## The theorem -/

/-- **Complementary binomial chords** (paper line 1099).

For `f(z) = z^n - r^n` with `n ≥ 2` and `0 < r < 1` (the paper's post-rotation
normalisation of `z^n - a`, `0 < |a| < 1`), the adjacent zeros `r` and `rω` are
distinct zeros of `f` joined by an explicit polygonal path inside
`{|z^n - r^n| < 1}` of length strictly below `2`. -/
theorem binomial_adjacent_path {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((r : ℝ) : ℂ) ≠ ((r : ℝ) : ℂ) * chordOmega n ∧
      (((r : ℝ) : ℂ)) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      (((r : ℝ) : ℂ) * chordOmega n) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
        ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := by
  have hn0 : n ≠ 0 := by omega
  have hrn : r ^ n < 1 := by
    calc r ^ n < 1 ^ n := pow_lt_pow_left₀ hr1 hr0.le hn0
      _ = 1 := one_pow n
  have hpath : PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := by
    by_cases h : r ^ n * (1 + chordCos n ^ n) < 1
    · exact adjacent_chord_connected hn hr0 hr1 h
    · push_neg at h
      -- above the switch forces `n ≥ 3`, since `r_* = 1` when `n = 2`
      have hn3 : 3 ≤ n := by
        by_contra hcon
        have hn2 : n = 2 := by omega
        subst hn2
        rw [chordCos_eq_zero_of_two] at h
        nlinarith [h, hr0, hr1]
      exact inner_path_connected hn3 hr0 hr1 h (by norm_num : (0:ℝ) < 1/2)
        (by norm_num : (1:ℝ)/2 < 1)
  refine ⟨?_, by ring, ?_, hpath⟩
  · -- the two adjacent zeros are distinct: the path already separates them,
    -- but we argue directly from `ω ≠ 1`
    intro hcon
    obtain ⟨γ, _, hγ0, hγ2, hγmem, _, _⟩ := hpath
    have h1 : ((r : ℝ) : ℂ) * (1 - chordOmega n) = 0 := by
      have : ((r : ℝ) : ℂ) - ((r : ℝ) : ℂ) * chordOmega n = 0 := by
        rw [← hcon]; ring
      linear_combination this
    have hr : ((r : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact hr0.ne'
    have homega : chordOmega n = 1 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hr
      · linear_combination -h
    -- but then `|f|` at the midpoint would be `r^n(1 + 1) ≥ ...`; instead use that
    -- `ω = 1` forces `cos(π/n) = 1`, impossible for `n ≥ 2`
    have hre : chordCos n ^ 2 - chordSin n ^ 2 = 1 := by
      have := congrArg Complex.re homega
      rw [chordOmega, halfRoot_eq] at this
      simpa [pow_two, Complex.mul_re, Complex.mul_im] using this
    have hCS := sin_sq_add_cos_sq n
    have hs : chordSin n = 0 := by nlinarith
    have hspos : 0 < chordSin n := by
      rw [chordSin]
      apply Real.sin_pos_of_pos_of_lt_pi (angle_pos hn)
      have := angle_le_pi_div_two hn
      have := Real.pi_pos
      linarith
    linarith
  · rw [mul_pow, chordOmega_pow hn]
    ring

end BinomialChord

/-! ## Paper-form restatements -/

open BinomialChord

/-- **Complementary binomial chords, clause 1** (paper line 1099-1101):
two adjacent zeros of `z^n - a` are joined by an explicit polygonal path
inside `{|z^n - a| < 1}` of length strictly below `2`, in the paper's
normalisation `a = r^n > 0`. -/
theorem binomial_chords_path {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((r : ℝ) : ℂ) ≠ ((r : ℝ) : ℂ) * chordOmega n ∧
      (((r : ℝ) : ℂ)) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      (((r : ℝ) : ℂ) * chordOmega n) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
        ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) :=
  binomial_adjacent_path hn hr0 hr1

/-- **Clause 2** (paper line 1101-1102): for `r < r_*` the adjacent-root chord
itself works. -/
theorem binomial_chords_below_threshold {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hlt : r < chordThreshold n) :
    PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) :=
  adjacent_chord_connected hn hr0 hr1 ((lt_chordThreshold_iff hn hr0.le).mp hlt)

/-- **Clauses 3 and 5** (paper lines 1102-1103 and 1106-1107): for `r ≥ r_*`,
two radial legs and an inner adjacent crossing chord work after an arbitrarily
small radial contraction, and this is what supplies OPEN containment at and
above the switch. -/
theorem binomial_chords_above_threshold {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hge : chordThreshold n ≤ r) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := by
  have hn2 : 2 ≤ n := by omega
  have hswitch : 1 ≤ r ^ n * (1 + chordCos n ^ n) := by
    by_contra hcon
    push_neg at hcon
    exact absurd ((lt_chordThreshold_iff hn2 hr0.le).mpr hcon) (not_lt.mpr hge)
  exact inner_path_connected hn hr0 hr1 hswitch hl0 hl1

/-- **Clause 4** (paper lines 1103-1105): the two constructions meet at
`r = r_*`, where the outer chord attains `|f| = 1` at its midpoint and
therefore lies only in the CLOSED lemniscate. -/
theorem binomial_chords_at_threshold {n : ℕ} (hn : 2 ≤ n) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(chordPoint n (chordThreshold n) u) ^ n
          - ((chordThreshold n : ℝ) : ℂ) ^ n‖ ≤ 1) ∧
      ‖(chordPoint n (chordThreshold n) (1 / 2)) ^ n
        - ((chordThreshold n : ℝ) : ℂ) ^ n‖ = 1 :=
  threshold_chord_touches hn (chordThreshold_pos hn) (chordThreshold_pow hn)

/-- **The central chord calculation** (paper lines 1110-1113 and 1128-1131):
`max_{z ∈ [s, sω]} |z^n - r^n| = r^n + (sc)^n` for every `0 < s ≤ r`, with the
maximum at the midpoint. -/
theorem binomial_chord_maximum {n : ℕ} (hn : 2 ≤ n) {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(chordPoint n s u) ^ n - ((r : ℝ) : ℂ) ^ n‖ ≤ r ^ n + (s * chordCos n) ^ n) ∧
      ‖(chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = r ^ n + (s * chordCos n) ^ n :=
  ⟨fun u hu0 hu1 => chord_norm_le hn hs hsr hu0 hu1,
    chord_norm_midpoint hn s r hs.le (by linarith)⟩

/-- **The decisive step** (paper lines 1132-1134): `1 + cos(nθ) ≤ 2cos^n θ`
on `|θ| ≤ π/n`. -/
theorem binomial_chord_decisive_step {n : ℕ} (hn : 2 ≤ n) {θ : ℝ}
    (hθ : (n : ℝ) * |θ| ≤ Real.pi) :
    1 + Real.cos ((n : ℝ) * θ) ≤ 2 * Real.cos θ ^ n :=
  one_add_cos_le hn hθ

/-- **Maximality of the inner radius** (paper lines 1122-1123): a larger
crossing chord already escapes at its midpoint. -/
theorem binomial_inner_chord_maximal {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ^ n < 1) (hswitch : 1 ≤ r ^ n * (1 + chordCos n ^ n)) :
    ‖(chordPoint n (innerRadius n r) (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = 1 ∧
      (∀ s : ℝ, innerRadius n r < s → s ≤ r →
        1 < ‖(chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖) :=
  inner_chord_maximal hn hr0 hr1 hswitch

#print axioms binomial_chords_path
#print axioms binomial_chords_below_threshold
#print axioms binomial_chords_above_threshold
#print axioms binomial_chords_at_threshold
#print axioms binomial_chord_maximum
#print axioms binomial_chord_decisive_step
#print axioms binomial_inner_chord_maximal

end ErdosProblems.Erdos1041.PaperCompleteR21
