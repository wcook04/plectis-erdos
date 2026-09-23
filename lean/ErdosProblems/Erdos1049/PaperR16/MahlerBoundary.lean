import ErdosProblems.Erdos1049.PaperR16.RootOrders
import ErdosProblems.Erdos1049.PaperR16.RowScaling

/-!
# From a literal polynomial Mahler equation to every boundary row

Checked in the eight-paper audit build (EightPaperR21Audit).

The input is the equation on the open complex unit disc, not a radial-limit
hypothesis, not a family of rows, and not a nonvanishing determinant premise.
The concluding theorem invokes the supplied R11 consumer verbatim.
-/

noncomputable section
open scoped BigOperators
open Filter Topology
open Polynomial

namespace ErdosProblems.Erdos1049.PaperR16

open ErdosProblems.Erdos1049.PaperR11

/-- The literal source equation. Coefficients outside `0,…,D` are irrelevant. -/
def PolynomialMahlerEquation (k D : ℕ) (A : ℕ → ℂ[X]) : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 →
    ∑ i ∈ Finset.range (D + 1), (A i).eval z * lambert (z ^ (k ^ i)) = 0

/-- Every function value in the literal equation is an absolutely convergent sum. -/
theorem mahler_iterate_norm_lt_one (k i : ℕ) (hk : 0 < k)
    (z : ℂ) (hz : ‖z‖ < 1) : ‖z ^ (k ^ i)‖ < 1 := by
  rw [norm_pow]
  exact unit_pow_lt_one (norm_nonneg z) hz (pow_pos hk i)

theorem mahler_iterate_norm_summable (k i : ℕ) (hk : 0 < k)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖lambertTerm (z ^ (k ^ i)) n‖) :=
  lambert_norm_summable _ (mahler_iterate_norm_lt_one k i hk z hz)

private lemma finite_sum_radial_limit (S : Finset ℕ) (f : ℕ → ℝ → ℂ)
    (v : ℕ → ℂ) (h : ∀ i, Tendsto (f i) radial (𝓝 (v i))) :
    Tendsto (fun r : ℝ => ∑ i ∈ S, f i r) radial (𝓝 (∑ i ∈ S, v i)) := by
  induction S using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) radial (𝓝 0))
  | @insert a S ha ih =>
      simpa only [Finset.sum_insert ha] using (h a).add ih

/-- Transport through `z=rζ` and the one-sided radial limit. -/
theorem literal_mahler_boundary_sum (k D : ℕ) (hk : 0 < k)
    (A : ℕ → ℂ[X]) (hEq : PolynomialMahlerEquation k D A)
    (ell s : ℕ) (hell : 0 < ell) (hc : ell.Coprime k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (ell * k ^ s)) :
    (∑ i ∈ Finset.range (D + 1), (A i).eval ζ *
      ((ell : ℂ) * (k : ℂ) ^ max s i)⁻¹) = 0 := by
  have hn : 0 < ell * k ^ s := mul_pos hell (pow_pos hk s)
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one (Nat.ne_of_gt hn)
  let f : ℕ → ℝ → ℂ := fun i r => (A i).eval ((r : ℂ) * ζ) *
    ((radialGauge r : ℂ) * lambert (((r : ℂ) * ζ) ^ (k ^ i)))
  let v : ℕ → ℂ := fun i => (A i).eval ζ *
    ((ell : ℂ) * (k : ℂ) ^ max s i)⁻¹
  have hterm : ∀ i, Tendsto (f i) radial (𝓝 (v i)) := by
    intro i
    have hcont : Continuous (fun r : ℝ => (A i).eval ((r : ℂ) * ζ)) := by fun_prop
    have hp : Tendsto (fun r : ℝ => (A i).eval ((r : ℂ) * ζ))
        radial (𝓝 ((A i).eval ζ)) := by
      simpa only [Complex.ofReal_one, one_mul] using
        (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    exact hp.mul (lambert_mahler_radial_weight ell k s i hell hk hc ζ hζ)
  have hlimit := finite_sum_radial_limit (Finset.range (D + 1)) f v hterm
  have he : (fun r : ℝ => ∑ i ∈ Finset.range (D + 1), f i r) =ᶠ[radial]
      (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [radial_eventually_unit] with r hr
    have hz : ‖(r : ℂ) * ζ‖ < 1 := by
      simpa only [norm_mul, hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr.1] using hr.2
    have heq := hEq ((r : ℂ) * ζ) hz
    calc
      (∑ i ∈ Finset.range (D + 1), f i r) =
          (radialGauge r : ℂ) *
            (∑ i ∈ Finset.range (D + 1), (A i).eval ((r : ℂ) * ζ) *
              lambert (((r : ℂ) * ζ) ^ (k ^ i))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [f]
        ring
      _ = 0 := by rw [heq, mul_zero]
  have hzero : Tendsto (fun r : ℝ => ∑ i ∈ Finset.range (D + 1), f i r)
      radial (𝓝 (0 : ℂ)) := (tendsto_congr' he).2 tendsto_const_nhds
  exact tendsto_nhds_unique hlimit hzero

/-- The exact R11 polynomial row vanishes at each admissible primitive root. -/
theorem literal_mahler_row_at_root (k D : ℕ) (hk : 0 < k)
    (A : ℕ → ℂ[X]) (hEq : PolynomialMahlerEquation k D A)
    (ell s : ℕ) (hell : 0 < ell) (hc : ell.Coprime k)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (ell * k ^ s)) :
    (mahlerPolynomialRow D (k : ℂ) A s).eval ζ = 0 := by
  have hboundary := literal_mahler_boundary_sum k D hk A hEq ell s hell hc ζ hζ
  have hellC : (ell : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hell)
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  calc
    (mahlerPolynomialRow D (k : ℂ) A s).eval ζ =
        ∑ i ∈ Finset.range (D + 1), mahlerWeight (k : ℂ) s i * (A i).eval ζ := by
      simp [mahlerPolynomialRow, Polynomial.eval_finset_sum]
    _ = ((ell : ℂ) * (k : ℂ) ^ s) *
        (∑ i ∈ Finset.range (D + 1), (A i).eval ζ *
          ((ell : ℂ) * (k : ℂ) ^ max s i)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← full_radial_weight_scale (ell : ℂ) (k : ℂ) hellC hkC s i]
      ring
    _ = 0 := by rw [hboundary, mul_zero]

/-- Every row is produced from the equation, without supplying rows as assumptions. -/
theorem literal_mahler_polynomial_row (k D : ℕ) (hk : 0 < k)
    (A : ℕ → ℂ[X]) (hEq : PolynomialMahlerEquation k D A) (s : ℕ) :
    mahlerPolynomialRow D (k : ℂ) A s = 0 := by
  apply polynomial_eq_zero_of_testRoots k s hk
  intro n _hn
  exact literal_mahler_row_at_root k D hk A hEq (k * n + 1) s
    (by omega) (testOrder_coprime k n) (testRoot k s n) (testRoot_primitive k s n hk)

/-- The same producer in the recovered R15 normalisation, via the proved equivalence. -/
theorem literal_mahler_R15_rows (k D : ℕ) (hk : 0 < k)
    (A : ℕ → ℂ[X]) (hEq : PolynomialMahlerEquation k D A) (s : ℕ) :
    Rolling1049.Remaining.R15BoundaryWeights.polynomialBoundaryRow (k : ℂ) D A s = 0 := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  exact (polynomialBoundaryRow_zero_iff (k : ℂ) hkC D s A).2
    (literal_mahler_polynomial_row k D hk A hEq s)

/-- Complete endpoint: the literal equation is composed with the existing R11 consumer. -/
theorem polynomial_mahler_coefficients_eq_zero (k D : ℕ) (hk : 2 ≤ k)
    (A : ℕ → ℂ[X]) (hEq : PolynomialMahlerEquation k D A) :
    ∀ i ≤ D, A i = 0 := by
  have hk1 : (k : ℂ) ≠ 1 := by exact_mod_cast (show k ≠ 1 by omega)
  apply mahler_polynomial_rows_injective D (k : ℂ) hk1 A
  intro s _hs
  exact literal_mahler_polynomial_row k D (by omega) A hEq s

/-- The same endpoint with every Lambert value expanded into its literal positive-index series. -/
theorem literal_positive_series_coefficients_eq_zero (k D : ℕ) (hk : 2 ≤ k)
    (A : ℕ → ℂ[X])
    (hEq : ∀ z : ℂ, ‖z‖ < 1 →
      (∑ i ∈ Finset.range (D + 1), (A i).eval z *
        (∑' n : ℕ, (z ^ (k ^ i)) ^ (n + 1) /
          (1 - (z ^ (k ^ i)) ^ (n + 1)))) = 0) :
    ∀ i ≤ D, A i = 0 := by
  apply polynomial_mahler_coefficients_eq_zero k D hk A
  intro z hz
  calc
    (∑ i ∈ Finset.range (D + 1), (A i).eval z * lambert (z ^ (k ^ i))) =
        ∑ i ∈ Finset.range (D + 1), (A i).eval z *
          (∑' n : ℕ, (z ^ (k ^ i)) ^ (n + 1) /
            (1 - (z ^ (k ^ i)) ^ (n + 1))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lambert_eq_tsum_positive _
        (mahler_iterate_norm_lt_one k i (by omega) z hz)]
    _ = 0 := hEq z hz

def HasNontrivialPolynomialMahlerEquation (k : ℕ) : Prop :=
  ∃ D : ℕ, ∃ A : ℕ → ℂ[X],
    (∃ i ≤ D, A i ≠ 0) ∧ PolynomialMahlerEquation k D A

/-- The Lambert divisor series has no polynomial Mahler relation for any `k≥2`. -/
theorem no_polynomial_mahler_relation (k : ℕ) (hk : 2 ≤ k) :
    ¬ HasNontrivialPolynomialMahlerEquation k := by
  rintro ⟨D, A, ⟨i, hi, hne⟩, hEq⟩
  exact hne (polynomial_mahler_coefficients_eq_zero k D hk A hEq i hi)

end ErdosProblems.Erdos1049.PaperR16
