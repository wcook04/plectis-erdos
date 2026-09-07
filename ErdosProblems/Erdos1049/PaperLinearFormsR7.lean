import ErdosProblems.Erdos1049.PaperHomogenisationR7
import ErdosProblems.Erdos1049.RationalBaseContour
import ErdosProblems.Erdos1049.TwoSelectorRemainderEscape
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

/-!
# R7: the integer-form irrationality consumer and its polynomial bridge

Uncompiled proof-source candidate. No axioms and no admitted proofs.

`CancelledApproximationSupply` is an OPEN analytic/source obligation. There is
no declaration asserting that it exists. In particular the conditional region
and power corollaries below are not advertised as proofs of the displayed
unconditional irrationality theorems. The coverage ledger retains that gap.
-/

namespace ErdosProblems.Erdos1049.PaperR7

open Filter
open scoped Topology BigOperators

/-- Precisely the real Lambert value in the paper, indexed from exponent one.
Outside x > 1 this is still Lean's totalised sum; none of the target statements
uses those other inputs. Summability is a separate analytic obligation. -/
noncomputable def paperLambert (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x ^ (n + 1) - 1)

/-- A denominator-by-denominator version of the standard small-form test.
No independence, degree, sign, or coefficient-height hypothesis is needed. -/
theorem irrational_of_integer_forms_below_every_denominator (ξ : ℝ)
    (hsmall : ∀ q : ℕ, 0 < q → ∃ A B : ℤ,
      (A : ℝ) * ξ - B ≠ 0 ∧ |(A : ℝ) * ξ - B| < 1 / (q : ℝ)) :
    Irrational ξ := by
  intro hrat
  obtain ⟨r, hr⟩ := hrat
  have hden : 0 < r.den := Nat.pos_of_ne_zero r.den_nz
  obtain ⟨A, B, hne, hlt⟩ := hsmall r.den hden
  have hξ : ξ = (r.num : ℝ) / (r.den : ℝ) := by
    rw [← hr]
    exact Rat.cast_def r
  rw [hξ] at hne hlt
  have hgap := rational_integerLinearForm_gap r.num (r.den : ℤ) B A
    (by exact_mod_cast hden) (by simpa using hne)
  have hgap' : (1 : ℝ) / (r.den : ℝ) ≤
      |(A : ℝ) * ((r.num : ℝ) / (r.den : ℝ)) - B| := by
    simpa using hgap
  exact (not_lt_of_ge hgap') hlt

/-- The same criterion from an actual convergent sequence of integral forms.
Eventual nonvanishing suffices; the earlier finite prefix is irrelevant. -/
theorem irrational_of_integer_forms_tendsto_zero (ξ : ℝ)
    (A B : ℕ → ℤ)
    (hne : ∀ᶠ n in atTop, (A n : ℝ) * ξ - B n ≠ 0)
    (hlim : Tendsto (fun n => (A n : ℝ) * ξ - B n) atTop (𝓝 0)) :
    Irrational ξ := by
  apply irrational_of_integer_forms_below_every_denominator ξ
  intro q hq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (1 / (q : ℝ)) (one_div_pos.mpr hqR)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hne
  let n := max N M
  refine ⟨A n, B n, hM n (le_max_right _ _), ?_⟩
  simpa only [Real.dist_eq, sub_zero] using hN n (le_max_left _ _)

/-- The polynomial version of the exact endpoint consumer: the input is
ordinary polynomial integrality, a common post-cancellation degree, and the
actual nonzero decaying homogeneous remainders. -/
theorem irrational_of_cancelled_polynomial_forms
    (a b : ℕ) (hb : 0 < b) (ξ : ℝ)
    (U V : ℕ → Polynomial ℤ) (W : ℕ → ℕ)
    (hU : ∀ n, (U n).natDegree ≤ W n)
    (hV : ∀ n, (V n).natDegree ≤ W n)
    (hne : ∀ᶠ n in atTop,
      (U n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * ξ -
        (V n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) ≠ 0)
    (hlim : Tendsto (fun n => (b : ℝ) ^ (W n) *
      ((U n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * ξ -
        (V n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b))) atTop (𝓝 0)) :
    Irrational ξ := by
  let A : ℕ → ℤ := fun n => homEval a b (W n) (U n)
  let B : ℕ → ℤ := fun n => homEval a b (W n) (V n)
  have hid : ∀ n, (A n : ℝ) * ξ - B n = (b : ℝ) ^ (W n) *
      ((U n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * ξ -
        (V n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b)) := by
    intro n
    exact cleared_linear_form_identity a b (W n) (U n) (V n) ξ hb.ne' (hU n) (hV n)
  apply irrational_of_integer_forms_tendsto_zero ξ A B
  · filter_upwards [hne] with n hn
    rw [hid n]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hb.ne')) hn
  · simpa only [hid] using hlim

/-- EXACTLY the unproved source-supply step. The definition records all the
integrality and post-cancellation conditions; it does not assume the endpoint
irrationality and does not assert that a source family meeting them exists. -/
def CancelledApproximationSupply (a b : ℕ) : Prop :=
  ∃ (U V : ℕ → Polynomial ℤ) (W : ℕ → ℕ),
    (∀ n, (U n).natDegree ≤ W n) ∧
    (∀ n, (V n).natDegree ≤ W n) ∧
    (∀ᶠ n in atTop,
      (U n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * paperLambert ((a : ℝ) / b) -
        (V n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) ≠ 0) ∧
    Tendsto (fun n => (b : ℝ) ^ (W n) *
      ((U n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * paperLambert ((a : ℝ) / b) -
        (V n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b))) atTop (𝓝 0)

/-- A consumer, not the paper's unconditional main theorem. -/
theorem irrational_paperLambert_of_supply (a b : ℕ) (hb : 0 < b)
    (hsupply : CancelledApproximationSupply a b) :
    Irrational (paperLambert ((a : ℝ) / b)) := by
  obtain ⟨U, V, W, hU, hV, hne, hlim⟩ := hsupply
  exact irrational_of_cancelled_polynomial_forms a b hb _ U V W hU hV hne hlim

/-- This names the unproved region-wide source construction with the live
contour definition, rather than introducing a rounded replacement constant. -/
def ContourSourceSupply : Prop :=
  ∀ a b : ℕ, 0 < b → b < a → a.Coprime b →
    ZudilinContourRegion a b → CancelledApproximationSupply a b

/-- Unconditional conclusion only AFTER `ContourSourceSupply` has been
proved. Its missing premise remains displayed in the coverage file. -/
theorem rational_base_region_of_source_supply (hsource : ContourSourceSupply)
    (a b : ℕ) (hb : 0 < b) (hab : b < a) (hcop : a.Coprime b)
    (hregion : ZudilinContourRegion a b) :
    Irrational (paperLambert ((a : ℝ) / b)) :=
  irrational_paperLambert_of_supply a b hb (hsource a b hb hab hcop hregion)

/-- The paper's power-family corollary as a consumer of the SAME open source
supply, with the actual base `(31/4)^r` rather than a symbolic label. -/
theorem thirtyone_four_powers_of_source_supply
    (hsource : ContourSourceSupply) (r : ℕ) (hr : 0 < r) :
    Irrational (paperLambert (((31 : ℝ) / 4) ^ r)) := by
  have hb : 0 < (4 : ℕ) ^ r := Nat.pow_pos (by norm_num)
  have hab : (4 : ℕ) ^ r < 31 ^ r :=
    Nat.pow_lt_pow_left (by norm_num) hr.ne'
  have hc : ((31 : ℕ) ^ r).Coprime (4 ^ r) :=
    (show Nat.Coprime 31 4 by norm_num).pow r r
  have ht := rational_base_region_of_source_supply hsource (31 ^ r) (4 ^ r)
    hb hab hc (thirtyoneFour_power_mem_zudilinContourRegion r hr)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, div_pow] using ht

end ErdosProblems.Erdos1049.PaperR7
