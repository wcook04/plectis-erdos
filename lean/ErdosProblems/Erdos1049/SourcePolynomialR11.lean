import ErdosProblems.Erdos1049.GaussianCoefficientsR11
import ErdosProblems.Erdos1049.PaperOmegaIndicatorR7
import ErdosProblems.Erdos1049.ZudilinConeArithmetic
import Mathlib

/-!
# Actual finite 2004 A coefficient and its normalisation


The reindexing k = 14*n+1+s makes every exponent nonnegative. In particular
A is an actual integral polynomial, not a postulated source package.
This module proves the A-channel inclusion for every n, including n=0.
It does not assert the missing B-channel cancellation or the analytic source
identity. Those obligations are recorded separately, not hidden in a premise.
-/
namespace ErdosProblems.Erdos1049.PaperR11
open Polynomial
open scoped BigOperators

/-- The exact published normalising exponent. -/
def sourceM (n : ℕ) : ℕ := 266 * n ^ 2 + 34 * n + 1

/-- The exponent left after X^M is removed from the s-th actual A summand. -/
def sourceAExponent (n s : ℕ) : ℕ :=
  2 * n ^ 2 + (n + 1) * s + s.choose 2

noncomputable def sourceGaussianProduct (n s : ℕ) : ℤ[X] :=
  gaussBinom X (14 * n + s) (12 * n) *
    gaussBinom X (13 * n) (13 * n - s)

noncomputable def sourceNormalisedASummand (n s : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) * X ^ sourceAExponent n s * sourceGaussianProduct n s

/-- The unnormalised coefficient, equal to the literal source after reindexing. -/
noncomputable def sourceASummand (n s : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) * X ^ (sourceM n + sourceAExponent n s) *
    sourceGaussianProduct n s

noncomputable def sourceA (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1), sourceASummand n s

noncomputable def sourceAWithoutMonomial (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1), sourceNormalisedASummand n s

lemma sourceASummand_factor (n s : ℕ) :
    sourceASummand n s = X ^ sourceM n * sourceNormalisedASummand n s := by
  simp only [sourceASummand, sourceNormalisedASummand, pow_add]
  ring

/-- All-index monomial divisibility for the actual A coefficient. -/
theorem sourceA_factor (n : ℕ) :
    sourceA n = X ^ sourceM n * sourceAWithoutMonomial n := by
  simp only [sourceA, sourceAWithoutMonomial, sourceASummand_factor,
    Finset.mul_sum]

lemma twice_choose_two_int (s : ℕ) :
    (2 : ℤ) * (s.choose 2 : ℤ) = (s : ℤ) * ((s : ℤ) - 1) := by
  induction s with
  | zero => norm_num
  | succ s ih =>
      have hchoose : (s + 1).choose 2 = s + s.choose 2 := by
        simpa using (Nat.choose_succ_succ s 1)
      rw [hchoose]
      push_cast
      nlinarith

/-- Exact algebra connecting our nonnegative exponent with the printed E_k.
This proves the reindexing rather than merely naming a new unrelated A. -/
theorem sourceASummand_exponent_matches (n s : ℕ) :
    zudilinPartialFractionExpTwice
        (12 * (n : ℤ) + 1) (14 * (n : ℤ) + 1) (27 * (n : ℤ) + 2)
        (14 * (n : ℤ) + 1 + s) +
      2 * (14 * (n : ℤ) + 1) * (14 * (n : ℤ) + 1 + s) =
      2 * ((sourceM n + sourceAExponent n s : ℕ) : ℤ) := by
  have hc := twice_choose_two_int s
  simp only [zudilinPartialFractionExpTwice, sourceM, sourceAExponent]
  push_cast
  nlinarith

lemma sourceASummand_sign_matches (n s : ℕ) :
    (-1 : ℤ) ^ ((12 * n + 1) + (14 * n + 1) + (14 * n + 1 + s) + 1) =
      (-1 : ℤ) ^ s := by
  have he : (12 * n + 1) + (14 * n + 1) + (14 * n + 1 + s) + 1 =
      40 * n + 4 + s := by omega
  rw [he, pow_add, pow_add, pow_mul]
  norm_num

lemma source_index_range (n s : ℕ) (hs : s < 13 * n + 1) :
    14 * n + 1 ≤ 14 * n + 1 + s ∧
    14 * n + 1 + s ≤ 27 * n + 1 ∧
    (27 * n + 2) - (14 * n + 1 + s) - 1 = 13 * n - s := by
  omega

/-- Integer shifts in the floor argument cancel in each balanced floor sum. -/
lemma floor_mul_fract (x : ℝ) (a : ℤ) :
    ⌊(a : ℝ) * Int.fract x⌋ = ⌊(a : ℝ) * x⌋ - a * ⌊x⌋ := by
  change ⌊(a : ℝ) * (x - (⌊x⌋ : ℝ))⌋ = _
  rw [mul_sub, ← Int.cast_mul, Int.floor_sub_intCast]

/-- The checked indicator on [0,1) extends to the actual n/l arguments.
No period-one property is assumed. -/
theorem omegaWeight_fract (x : ℝ) :
    PaperR7.omegaWeight (Int.fract x) = PaperR7.omegaWeight x := by
  have h12 : ⌊(12 : ℝ) * Int.fract x⌋ = ⌊(12 : ℝ) * x⌋ - 12 * ⌊x⌋ := by
    simpa using floor_mul_fract x 12
  have h13 : ⌊(13 : ℝ) * Int.fract x⌋ = ⌊(13 : ℝ) * x⌋ - 13 * ⌊x⌋ := by
    simpa using floor_mul_fract x 13
  have h14 : ⌊(14 : ℝ) * Int.fract x⌋ = ⌊(14 : ℝ) * x⌋ - 14 * ⌊x⌋ := by
    simpa using floor_mul_fract x 14
  have h15 : ⌊(15 : ℝ) * Int.fract x⌋ = ⌊(15 : ℝ) * x⌋ - 15 * ⌊x⌋ := by
    simpa using floor_mul_fract x 15
  unfold PaperR7.omegaWeight
  rw [h12, h13, h14, h15]
  congr 2 <;> ring

theorem omegaWeight_zero_or_one (x : ℝ) :
    PaperR7.omegaWeight x = 0 ∨ PaperR7.omegaWeight x = 1 := by
  have h := (PaperR7.omega_indicator (Int.fract x)
    (Int.fract_nonneg x) (Int.fract_lt_one x)).1
  simpa only [omegaWeight_fract] using h

theorem omegaWeight_int (z : ℤ) : PaperR7.omegaWeight (z : ℝ) = 0 := by
  rw [← omegaWeight_fract, Int.fract_intCast]
  norm_num [PaperR7.omegaWeight]

noncomputable def sourceWeight (n l : ℕ) : ℤ :=
  PaperR7.omegaWeight ((n : ℝ) / (l : ℝ))

lemma sourceWeight_zero_or_one (n l : ℕ) :
    sourceWeight n l = 0 ∨ sourceWeight n l = 1 := by
  exact omegaWeight_zero_or_one _

/-- The l=1 factor in Ω is exactly 1, as required by the paper's product
starting at l=2. -/
lemma sourceWeight_one (n : ℕ) : sourceWeight n 1 = 0 := by
  simpa [sourceWeight] using omegaWeight_int (n : ℤ)

noncomputable def sourceD (n : ℕ) : ℤ[X] :=
  ∏ l ∈ Finset.Icc 1 (15 * n), cyclotomic l ℤ

/-- Including l=1 is harmless: its weight is omega(n)=0. -/
noncomputable def sourceOmega (n : ℕ) : ℤ[X] :=
  ∏ l ∈ Finset.Icc 1 (15 * n), (cyclotomic l ℤ) ^ (sourceWeight n l).toNat

noncomputable def sourceComplement (n : ℕ) : ℤ[X] :=
  ∏ l ∈ Finset.Icc 1 (15 * n),
    if sourceWeight n l = 0 then cyclotomic l ℤ else 1

/-- The actual 0/1 weights produce a polynomial complement, without rational
function division or a divisibility hypothesis. -/
theorem sourceD_factor (n : ℕ) :
    sourceD n = sourceOmega n * sourceComplement n := by
  classical
  unfold sourceD sourceOmega sourceComplement
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  rcases sourceWeight_zero_or_one n l with h | h
  · simp [h]
  · simp [h]

noncomputable def sourceU (n : ℕ) : ℤ[X] :=
  sourceComplement n * sourceAWithoutMonomial n

/-- Division-free A-channel form of X^-M (D/Omega) A ∈ Z[X]. -/
theorem actual_A_polynomial_inclusion (n : ℕ) :
    sourceD n * sourceA n =
      sourceOmega n * X ^ sourceM n * sourceU n := by
  rw [sourceD_factor, sourceA_factor]
  unfold sourceU
  ring

/-- The normalised coefficient at every real x != 0 with Omega(x) != 0. -/
theorem actual_A_normalisation_eval (n : ℕ) (x : ℝ)
    (hx : x ≠ 0) (ho : (sourceOmega n).eval₂ (Int.castRingHom ℝ) x ≠ 0) :
    x ^ (-(sourceM n : ℤ)) *
        ((sourceD n).eval₂ (Int.castRingHom ℝ) x /
          (sourceOmega n).eval₂ (Int.castRingHom ℝ) x) *
        (sourceA n).eval₂ (Int.castRingHom ℝ) x =
      (sourceU n).eval₂ (Int.castRingHom ℝ) x := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom ℝ) x)
    (actual_A_polynomial_inclusion n)
  simp only [eval₂_mul, eval₂_pow, eval₂_X] at h
  rw [zpow_neg, zpow_natCast]
  have hp : x ^ sourceM n ≠ 0 := pow_ne_zero _ hx
  field_simp [hp, ho]
  nlinarith [h]

end ErdosProblems.Erdos1049.PaperR11
