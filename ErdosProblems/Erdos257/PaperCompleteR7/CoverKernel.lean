import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

/-!
# Finite and scalar kernel of the strengthened positive cover

The short note's `thm:variable-fractional-cover` and `res:mixed-supports` are
not available as end-to-end Lean theorems. Their proofs use three ingredients
that are finite or scalar, and those are isolated here as ordinary theorems.

* `rpow_sum_le_sum_rpow` and `rpow_tsum_le_tsum_rpow` are the subadditivity of a
  fractional power used to pass from the dyadic observation mean `U_j(N)` to the
  divisor majorant `V_j(N)`.
* `rpow_neg_le_max_one_inv` is the scalar step `ε ^ (-α) ≤ max 1 ε⁻¹` that makes
  the tail budget choice uniform over the exponents `α_j`.
* `tsum_inv_pow_succ` and `tsum_rpow_two_inv_succ` evaluate the geometric factor
  `1 / (2 ^ α - 1)` appearing in the displayed cost condition (V).

Round 7 wave 2 adds the finite and scalar steps that the same two proofs use
further down: the complete-orbit facts of the observation kernel `w_{B,d}`
(`mul_sub_one_le_pow_sub_one`, `cycle_ratio_le_inv_sub_one`,
`sum_cycle_weight_eq`), the scalar minimisation behind the cover-cost display
(`two_rpow_sub_one_le_self`, `exp_one_mul_le_exp`,
`exp_one_mul_log_le_rpow_div`, which is the second inequality of the note's
cover-log obstruction for every admissible exponent), and the atom inequality
`(b^r-1)/(b^d-1) <= 2 (2^r-1)/(2^d-1)` that carries the base-two conclusion to
every integer base (`atom_base_transfer`), the one-sample step of the averaged
tail test (`exists_lt_of_mean_lt`), and the geometric lower bound of the no-wrap
case (`two_mul_sqrt_mul_le_add`, `card_mul_sqrt_le_geom_sum`).

None of these is the analytic theorem. The irrationality conclusion still needs
the one sampling step that is neither finite nor scalar: a single `N` at which
the averaged tail test `S_J(N) < 1` holds, obtained from the finite estimate (S)
by averaging over the dyadic ranges. The remaining goal is stated as
`StrengthenedPositiveCoverClaim` in `AnalyticTargets.lean`.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR7

open Finset Filter

/-- Subadditivity of a fractional power over a finite sum of nonnegative reals.
This is the finite form of the step `U_j(N) ^ α_j ≤ V_j(N)`. -/
theorem rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, f i) ^ p ≤ ∑ i ∈ s, f i ^ p := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Real.zero_rpow hp.ne']
  · intro a t hat ih
    rw [Finset.sum_insert hat, Finset.sum_insert hat]
    have hsum : 0 ≤ ∑ i ∈ t, f i := Finset.sum_nonneg fun i _ => hf i
    have hstep : (f a + ∑ i ∈ t, f i) ^ p ≤ f a ^ p + (∑ i ∈ t, f i) ^ p :=
      Real.rpow_add_le_add_rpow (hf a) hsum hp.le hp1
    linarith

/-- The countable form of the same subadditivity, under the summability that the
paper's nonnegative double series supplies on both sides. -/
theorem rpow_tsum_le_tsum_rpow (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hsum : Summable f) (hsump : Summable fun i => f i ^ p) :
    (∑' i, f i) ^ p ≤ ∑' i, f i ^ p := by
  have hcont : ContinuousAt (fun x : ℝ => x ^ p) (∑' i, f i) :=
    Real.continuousAt_rpow_const _ p (Or.inr hp.le)
  have htend : Tendsto (fun n => (∑ i ∈ Finset.range n, f i) ^ p) atTop
      (nhds ((∑' i, f i) ^ p)) :=
    hcont.tendsto.comp hsum.hasSum.tendsto_sum_nat
  refine le_of_tendsto htend (Filter.Eventually.of_forall ?_)
  intro n
  refine (rpow_sum_le_sum_rpow (Finset.range n) f hf hp hp1).trans ?_
  exact hsump.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (hf i) p)

/-- The scalar tail-budget bound `ε ^ (-α) ≤ max 1 ε⁻¹`, uniform over the
exponents `0 < α ≤ 1`. -/
theorem rpow_neg_le_max_one_inv {t α : ℝ} (ht : 0 < t) (hα : 0 < α) (hα1 : α ≤ 1) :
    t ^ (-α) ≤ max 1 t⁻¹ := by
  rcases le_total t 1 with h | h
  · have hmono : t ^ (-α) ≤ t ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht h (by linarith)
    rw [Real.rpow_neg_one] at hmono
    exact hmono.trans (le_max_right _ _)
  · have hone : t ^ (-α) ≤ t ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (by linarith)
    rw [Real.rpow_zero] at hone
    exact hone.trans (le_max_left _ _)

/-- The geometric factor of the displayed cost condition. -/
theorem tsum_inv_pow_succ {B : ℝ} (hB : 1 < B) :
    ∑' r : ℕ, (B ^ (r + 1))⁻¹ = 1 / (B - 1) := by
  have hB0 : (0 : ℝ) < B := lt_trans zero_lt_one hB
  have hBne : B ≠ 0 := ne_of_gt hB0
  have hinv0 : (0 : ℝ) ≤ B⁻¹ := by positivity
  have hinv1 : B⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hB
  have hterm : ∀ r : ℕ, (B ^ (r + 1))⁻¹ = B⁻¹ * (B⁻¹) ^ r := by
    intro r
    rw [pow_succ, mul_inv, ← inv_pow]
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hinv0 hinv1]
  have hsub : (1 : ℝ) - B⁻¹ ≠ 0 := by
    have : (0 : ℝ) < 1 - B⁻¹ := by linarith
    exact ne_of_gt this
  have hBm : B - 1 ≠ 0 := by
    have : (0 : ℝ) < B - 1 := by linarith
    exact ne_of_gt this
  field_simp

/-- The cost factor specialised to the base `2 ^ α` used in the displayed
condition (V), for every admissible exponent. -/
theorem tsum_rpow_two_inv_succ {α : ℝ} (hα : 0 < α) :
    ∑' r : ℕ, (((2 : ℝ) ^ α) ^ (r + 1))⁻¹ = 1 / ((2 : ℝ) ^ α - 1) := by
  refine tsum_inv_pow_succ ?_
  exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, hα⟩)

/-! ### Cycle weights of the finite observation kernel

The kernel weight of the short note's estimate (S) is `w_{B,d}(n) = B^(n % d) / (B^d - 1)`.
The two lemmas below are its complete-orbit facts: one full residue cycle carries total
weight exactly `1 / (B - 1)`, and the orbit of a common divisor `g` carries at most the
same total. Both are finite identities in `B`, uniform in `d` as `B` decreases to one. -/

/-- Bernoulli in the form the complete-cycle step uses. -/
theorem mul_sub_one_le_pow_sub_one (B : ℝ) (hB : 1 ≤ B) (g : ℕ) :
    (g : ℝ) * (B - 1) ≤ B ^ g - 1 := by
  have h : (1 : ℝ) + (g : ℝ) * (B - 1) ≤ (1 + (B - 1)) ^ g :=
    one_add_mul_le_pow (by linarith) g
  have hrw : (1 : ℝ) + (B - 1) = B := by ring
  rw [hrw] at h
  linarith

/-- The complete-cycle ratio bound `g / (B ^ g - 1) ≤ 1 / (B - 1)`, which is what makes
the main term of (S) uniform in the modulus. -/
theorem cycle_ratio_le_inv_sub_one {B : ℝ} (hB : 1 < B) (g : ℕ) (hg : 0 < g) :
    (g : ℝ) / (B ^ g - 1) ≤ 1 / (B - 1) := by
  have hB1 : (0 : ℝ) < B - 1 := by linarith
  have hgB : (1 : ℝ) < B ^ g := one_lt_pow₀ hB hg.ne'
  have hden : (0 : ℝ) < B ^ g - 1 := by linarith
  rw [div_le_div_iff₀ hden hB1]
  have := mul_sub_one_le_pow_sub_one B hB.le g
  linarith

/-- One full residue cycle of the kernel weight has total mass exactly `1 / (B - 1)`. -/
theorem sum_cycle_weight_eq {B : ℝ} (hB : 1 < B) (d : ℕ) (hd : 0 < d) :
    ∑ i ∈ Finset.range d, B ^ i / (B ^ d - 1) = 1 / (B - 1) := by
  have hB1 : (B : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < B - 1 := by linarith
    exact ne_of_gt this
  have hgB : (1 : ℝ) < B ^ d := one_lt_pow₀ hB hd.ne'
  have hden : (B : ℝ) ^ d - 1 ≠ 0 := by
    have : (0 : ℝ) < B ^ d - 1 := by linarith
    exact ne_of_gt this
  rw [← Finset.sum_div, geom_sum_eq (ne_of_gt hB) d]
  field_simp

/-! ### The scalar minimisation behind the cover cost

`Ψ(t) = inf_{0 < α ≤ 1} t ^ α / (2 ^ α - 1)` is the cover-independent cost of the short
note's display (eq:cover-log-obstruction). The bound `Ψ(t) ≥ e log t` is proved here for
every admissible exponent, which is the second inequality of that display. The first
inequality, the averaging over `F` against the uniform mean modulo `lcm F`, is not here. -/

/-- Convexity of `2 ^ ·` on the unit interval, the exact step the note cites. -/
theorem two_rpow_sub_one_le_self {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (2 : ℝ) ^ α - 1 ≤ α := by
  have h := rpow_one_add_le_one_add_mul_self (s := (1 : ℝ)) (by norm_num) hα0 hα1
  norm_num at h
  linarith

/-- `e u ≤ exp u`, the scalar form of `e ^ u / u ≥ e`. -/
theorem exp_one_mul_le_exp {u : ℝ} (_hu : 0 < u) :
    Real.exp 1 * u ≤ Real.exp u := by
  have h := Real.add_one_le_exp (u - 1)
  have hle : u ≤ Real.exp (u - 1) := by linarith
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  calc Real.exp 1 * u ≤ Real.exp 1 * Real.exp (u - 1) := by
        exact mul_le_mul_of_nonneg_left hle hpos.le
    _ = Real.exp u := by rw [← Real.exp_add]; ring_nf

/-- The cover-cost lower bound `t ^ α / (2 ^ α - 1) ≥ e log t`, uniformly over the
admissible exponents `0 < α ≤ 1`. Taking the infimum over `α` gives `Ψ(t) ≥ e log t`. -/
theorem exp_one_mul_log_le_rpow_div {t α : ℝ} (ht : 1 ≤ t) (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.exp 1 * Real.log t ≤ t ^ α / ((2 : ℝ) ^ α - 1) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have h2 : (1 : ℝ) < (2 : ℝ) ^ α :=
    Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, hα⟩)
  have hden : (0 : ℝ) < (2 : ℝ) ^ α - 1 := by linarith
  have htpos : (0 : ℝ) < t ^ α := Real.rpow_pos_of_pos ht0 α
  have hstep : t ^ α / α ≤ t ^ α / ((2 : ℝ) ^ α - 1) :=
    div_le_div_of_nonneg_left htpos.le hden (two_rpow_sub_one_le_self hα.le hα1)
  refine le_trans ?_ hstep
  rcases eq_or_lt_of_le hlog with hz | hz
  · rw [← hz]
    simp only [mul_zero]
    positivity
  · have hu : 0 < α * Real.log t := mul_pos hα hz
    have hexp : t ^ α = Real.exp (α * Real.log t) := by
      rw [Real.rpow_def_of_pos ht0]
      ring_nf
    have hkey : Real.exp 1 * (α * Real.log t) ≤ Real.exp (α * Real.log t) :=
      exp_one_mul_le_exp hu
    rw [hexp, le_div_iff₀ hα]
    calc Real.exp 1 * Real.log t * α = Real.exp 1 * (α * Real.log t) := by ring
      _ ≤ Real.exp (α * Real.log t) := hkey

/-! ### The base-transfer atom inequality

The short note's proof closes at base two and then transfers to every integer base `b ≥ 2`
through the atom inequality `(b^r - 1)/(b^d - 1) ≤ 2 (2^r - 1)/(2^d - 1)` for `0 ≤ r < d`.
That inequality is finite and is proved here. It is not the transfer step itself: the
displacement estimate it is applied to is still open. -/

/-- The geometric comparison the base-transfer envelope needs: at every positive
exponent, three copies of `2 ^ m` are below two copies of `3 ^ m`. -/
theorem three_mul_two_pow_le_two_mul_three_pow {m : ℕ} (hm : 1 ≤ m) :
    3 * (2 : ℝ) ^ m ≤ 2 * (3 : ℝ) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    calc 3 * (2 : ℝ) ^ (n + 1) = 2 * (3 * (2 : ℝ) ^ n) := by ring
      _ ≤ 2 * (2 * (3 : ℝ) ^ n) := by linarith
      _ ≤ 2 * (3 : ℝ) ^ (n + 1) := by rw [pow_succ]; linarith

theorem atom_base_transfer (b r d : ℕ) (hb : 2 ≤ b) (hrd : r < d) :
    ((b : ℝ) ^ r - 1) / ((b : ℝ) ^ d - 1) ≤ 2 * ((2 : ℝ) ^ r - 1) / ((2 : ℝ) ^ d - 1) := by
  have hd0 : 0 < d := lt_of_le_of_lt (Nat.zero_le r) hrd
  have hB : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hBd : (2 : ℝ) ^ d ≤ (b : ℝ) ^ d := by
    exact pow_le_pow_left₀ (by norm_num) hB d
  have h2d : (2 : ℝ) ≤ (2 : ℝ) ^ d := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd0
  have hden2 : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by linarith
  have hdenb : (0 : ℝ) < (b : ℝ) ^ d - 1 := by linarith
  rw [div_le_div_iff₀ hdenb hden2]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hbr : ((b : ℝ) ^ 0 - 1) = 0 := by norm_num
    rw [hbr]
    simp
  -- from here `1 ≤ r < d`
  have hm : 1 ≤ d - r := by omega
  have hsplit : d = r + (d - r) := by omega
  have h2r : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  have hBr : (0 : ℝ) < (b : ℝ) ^ r := by positivity
  have h2rpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  -- crude but sufficient envelope
  have hL : ((b : ℝ) ^ r - 1) * ((2 : ℝ) ^ d - 1) ≤ (b : ℝ) ^ r * (2 : ℝ) ^ d := by
    nlinarith [hBr, pow_pos (show (0:ℝ) < 2 by norm_num) d]
  have hRhalf : (2 : ℝ) ^ r / 2 ≤ (2 : ℝ) ^ r - 1 := by
    nlinarith [h2r]
  by_cases hb2 : b = 2
  · subst hb2
    push_cast
    nlinarith [hden2, pow_pos (show (0:ℝ) < 2 by norm_num) r,
      pow_pos (show (0:ℝ) < 2 by norm_num) d, h2r]
  · have hb3 : 3 ≤ b := by omega
    have hB3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb3
    have hBd3 : (3 : ℝ) ^ d ≤ (b : ℝ) ^ d := pow_le_pow_left₀ (by norm_num) hB3 d
    have h3d : (3 : ℝ) ≤ (3 : ℝ) ^ d := by
      calc (3 : ℝ) = (3 : ℝ) ^ 1 := by norm_num
        _ ≤ (3 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd0
    have hBdge : (3 : ℝ) ≤ (b : ℝ) ^ d := le_trans h3d hBd3
    have hDen : (2 : ℝ) / 3 * (b : ℝ) ^ d ≤ (b : ℝ) ^ d - 1 := by linarith
    -- the geometric comparison `3 * 2 ^ (d - r) ≤ 2 * b ^ (d - r)`
    have hgeom : 3 * (2 : ℝ) ^ (d - r) ≤ 2 * (b : ℝ) ^ (d - r) := by
      have h3m : (3 : ℝ) ^ (d - r) ≤ (b : ℝ) ^ (d - r) :=
        pow_le_pow_left₀ (by norm_num) hB3 (d - r)
      have hstep := three_mul_two_pow_le_two_mul_three_pow hm
      linarith
    have hadd : r + (d - r) = d := by omega
    have hpowsplit2 : (2 : ℝ) ^ d = (2 : ℝ) ^ r * (2 : ℝ) ^ (d - r) := by
      rw [← pow_add, hadd]
    have hpowsplitb : (b : ℝ) ^ d = (b : ℝ) ^ r * (b : ℝ) ^ (d - r) := by
      rw [← pow_add, hadd]
    have hBmpos : (0 : ℝ) < (b : ℝ) ^ (d - r) := by positivity
    have h2mpos : (0 : ℝ) < (2 : ℝ) ^ (d - r) := by positivity
    have hR : (b : ℝ) ^ r * (2 : ℝ) ^ d ≤ 2 * ((2 : ℝ) ^ r - 1) * ((b : ℝ) ^ d - 1) := by
      have hchain : (b : ℝ) ^ r * (2 : ℝ) ^ d
          ≤ 2 * ((2 : ℝ) ^ r / 2) * ((2 : ℝ) / 3 * (b : ℝ) ^ d) := by
        rw [hpowsplit2, hpowsplitb]
        have := mul_le_mul_of_nonneg_left hgeom (le_of_lt (mul_pos hBr h2rpos))
        nlinarith [hBr, h2rpos, hBmpos, h2mpos]
      have hstep2 : 2 * ((2 : ℝ) ^ r / 2) * ((2 : ℝ) / 3 * (b : ℝ) ^ d)
          ≤ 2 * ((2 : ℝ) ^ r - 1) * ((b : ℝ) ^ d - 1) := by
        have hA : (0 : ℝ) < 2 * ((2 : ℝ) ^ r / 2) := by positivity
        nlinarith [hRhalf, hDen, h2rpos, hBdge]
      linarith
    linarith

/-! ### The one-sample step

The printed proof averages the tail test `S_J` over an observation range and then
says "one sample therefore has `S_J(N) < 1`". That step is finite and is recorded
here in the form the cover proof uses it, over an arbitrary nonempty range. -/

/-- A nonnegative test whose mean over a nonempty finite range is below a threshold
is below that threshold at one sample of the range. -/
theorem exists_lt_of_mean_lt {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) {c : ℝ} (hmean : (∑ i ∈ s, f i) / (s.card : ℝ) < c) :
    ∃ i ∈ s, f i < c := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hsum : c * (s.card : ℝ) ≤ ∑ i ∈ s, f i := by
    calc c * (s.card : ℝ) = ∑ _i ∈ s, c := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ i ∈ s, f i := Finset.sum_le_sum fun i hi => hcon i hi
  rw [div_lt_iff₀ hcard] at hmean
  linarith

/-! ### The no-wrap case of the finite estimate

When the modulus exceeds twice the observation length there is no wrap, and the
printed proof bounds each atom by `1 / (d (B - 1))` through the geometric lower
bound `sum_{i<d} B^i >= d B^{(d-1)/2}`. That bound is two-term AM-GM applied to
the reflected pairing `B^i + B^{d-1-i}`, and it is proved here. The square root
of `B ^ (d - 1)` is the printed `B^{(d-1)/2}`. -/

/-- Two-term AM-GM in the form the pairing uses. -/
theorem two_mul_sqrt_mul_le_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  have h := two_mul_le_add_sq (Real.sqrt x) (Real.sqrt y)
  rw [Real.sq_sqrt hx, Real.sq_sqrt hy] at h
  rw [Real.sqrt_mul hx]
  linarith

/-- The geometric lower bound of the no-wrap case: a complete block of `d`
powers is at least `d` copies of the central power. -/
theorem card_mul_sqrt_le_geom_sum {B : ℝ} (hB : 0 ≤ B) (d : ℕ) :
    (d : ℝ) * Real.sqrt (B ^ (d - 1)) ≤ ∑ i ∈ Finset.range d, B ^ i := by
  classical
  have hpow : ∀ i : ℕ, (0 : ℝ) ≤ B ^ i := fun i => pow_nonneg hB i
  have hpair : ∀ i ∈ Finset.range d,
      2 * Real.sqrt (B ^ (d - 1)) ≤ B ^ i + B ^ (d - 1 - i) := by
    intro i hi
    have hid : i < d := Finset.mem_range.mp hi
    have hsplit : B ^ i * B ^ (d - 1 - i) = B ^ (d - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have h := two_mul_sqrt_mul_le_add (hpow i) (hpow (d - 1 - i))
    rwa [hsplit] at h
  have hsum : ∑ i ∈ Finset.range d, (2 * Real.sqrt (B ^ (d - 1)))
      ≤ ∑ i ∈ Finset.range d, (B ^ i + B ^ (d - 1 - i)) :=
    Finset.sum_le_sum hpair
  have hrefl : ∑ i ∈ Finset.range d, B ^ (d - 1 - i) = ∑ i ∈ Finset.range d, B ^ i := by
    rw [← Finset.sum_range_reflect (fun i => B ^ (d - 1 - i)) d]
    apply Finset.sum_congr rfl
    intro i hi
    have hid : i < d := Finset.mem_range.mp hi
    congr 1
    omega
  rw [Finset.sum_add_distrib, hrefl, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  linarith

end ErdosProblems.Erdos257.PaperCompleteR7

end
