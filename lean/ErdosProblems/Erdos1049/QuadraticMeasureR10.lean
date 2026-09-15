import ErdosProblems.Erdos1049.PaperAsymptoticsR9
import ErdosProblems.Erdos1049.PaperLinearFormsR7
import ErdosProblems.Erdos1049.RationalApproximationSeparation

/-!
# A complete quadratic-mesh irrationality-measure consumer

The conclusion is uniform over all integer numerators
and all sufficiently large positive denominators. No independence assumption
on successive coefficient pairs is used. The actual 2004 source construction
is NOT asserted by this module.
-/
namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped Topology
open PaperR9

/-- The eventual approximation formulation of an upper irrationality exponent.
It uses every integer numerator, so in particular covers reduced fractions. -/
def ApproximationExponentUpper (ξ μ : ℝ) : Prop :=
  ∀ ν : ℝ, μ < ν → ∃ q₀ : ℕ, 0 < q₀ ∧
    ∀ q : ℕ, q₀ ≤ q → ∀ p : ℤ,
      (q : ℝ) ^ (-ν) ≤ |ξ - (p : ℝ) / (q : ℝ)|

/-- The exponential form of the finite separation lemma. -/
theorem separation_of_exponential_envelope
    (A B p : ℤ) (q : ℕ) (ξ u v w : ℝ) (hq : 0 < q)
    (hlo : Real.exp (-u) ≤ |(A : ℝ) * ξ - B|)
    (hup : |(A : ℝ) * ξ - B| ≤ Real.exp (-v))
    (hA : |(A : ℝ)| ≤ Real.exp w)
    (hcross : Real.log (2 * (q : ℝ)) ≤ v) :
    Real.exp (-(u + w)) ≤ |ξ - (p : ℝ) / (q : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h2q : (0 : ℝ) < 2 * q := by positivity
  have hsmall : 2 * (q : ℝ) * |(A : ℝ) * ξ - B| ≤ 1 := by
    calc
      2 * (q : ℝ) * |(A : ℝ) * ξ - B| ≤
          2 * (q : ℝ) * Real.exp (-v) :=
        mul_le_mul_of_nonneg_left hup h2q.le
      _ ≤ 2 * (q : ℝ) * Real.exp (-Real.log (2 * (q : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ h2q.le
        exact Real.exp_le_exp.mpr (neg_le_neg hcross)
      _ = 1 := by rw [Real.exp_neg, Real.exp_log h2q, mul_inv_cancel₀ h2q.ne']
  have hsep := rational_separation_of_small_integer_form A B p (q : ℤ) ξ
    (by exact_mod_cast hq) (by simpa using hsmall)
  have hsep' : |(A : ℝ) * ξ - B| ≤
      |(A : ℝ)| * |ξ - (p : ℝ) / (q : ℝ)| := by
    simpa using hsep
  have hmain : Real.exp (-u) ≤ Real.exp w * |ξ - (p : ℝ) / (q : ℝ)| := by
    exact hlo.trans (hsep'.trans
      (mul_le_mul_of_nonneg_right hA (abs_nonneg _)))
  have hdivide : Real.exp (-u) / Real.exp w ≤ |ξ - (p : ℝ) / (q : ℝ)| :=
    (div_le_iff₀ (Real.exp_pos w)).mpr (by simpa [mul_comm] using hmain)
  simpa only [← Real.exp_sub, show -u - w = -(u + w) by ring] using hdivide

/-- A positive quadratic crosses every fixed real level. -/
lemma exists_quadratic_crossing (T x : ℝ) (hT : 0 < T) :
    ∃ n : ℕ, x ≤ T * (n : ℝ) ^ 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (x / T))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hnx : x / T < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hx : x < (n : ℝ) * T := (div_lt_iff₀ hT).mp hnx
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  exact ⟨n, hx.le.trans (by nlinarith [mul_le_mul_of_nonneg_left hsq hT.le])⟩

/-- Exact two-sided quadratic error rate and an upper coefficient rate imply
an upper approximation exponent. This proof includes the integer-mesh choice
and discards only a finite initial segment of the supplied estimates. -/
theorem approximationExponentUpper_of_quadratic_forms
    (A B : ℕ → ℤ) (ξ α τ : ℝ) (hα : 0 ≤ α) (hτ : 0 < τ)
    (hne : ∀ᶠ n in atTop, (A n : ℝ) * ξ - B n ≠ 0)
    (hA : QuadExpUpper (fun n => (A n : ℝ)) α)
    (hL : QuadLogRate (fun n => (A n : ℝ) * ξ - B n) (-τ)) :
    ApproximationExponentUpper ξ (1 + α / τ) := by
  intro ν hν
  have hν1 : 1 < ν := by
    have : 0 ≤ α / τ := div_nonneg hα hτ.le
    linarith
  have hν0 : 0 < ν := by linarith
  let g : ℝ := ν * τ - (α + τ)
  have hg : 0 < g := by
    have hdiv : α / τ < ν - 1 := by linarith
    have := (div_lt_iff₀ hτ).mp hdiv
    dsimp [g]
    nlinarith
  let η : ℝ := min (τ / 2) (g / (2 * (ν + 2)))
  have hη : 0 < η := lt_min (half_pos hτ) (div_pos hg (by linarith))
  have hητ : η ≤ τ / 2 := min_le_left _ _
  have hηg : η * (2 * (ν + 2)) ≤ g := by
    exact (le_div_iff₀ (by linarith : 0 < 2 * (ν + 2))).mp (min_le_right _ _)
  let T : ℝ := τ - η
  let S : ℝ := α + τ + 2 * η
  let D : ℝ := ν * T - S
  let C : ℝ := ν * T + ν * |Real.log 2|
  have hT : 0 < T := by dsimp [T]; linarith
  have hS : 0 < S := by dsimp [S]; linarith
  have hD : 0 < D := by dsimp [D, T, S, g] at *; nlinarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlow := hL.exp_lower hne η hη
  have hupp := hL.exp_upper η hη
  have hcoeff := hA η hη
  have hmesh := eventually_linear_le_square C D hC hD
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (((hlow.and hupp).and hcoeff).and hmesh)
  let N := max N₀ 1
  obtain ⟨q₀, hq₀⟩ := exists_nat_gt (Real.exp (T * (N : ℝ) ^ 2))
  have hq₀pos : 0 < q₀ := by
    have : (0 : ℝ) < q₀ := (Real.exp_pos _).trans hq₀
    exact_mod_cast this
  refine ⟨q₀, hq₀pos, ?_⟩
  intro q hq p
  have hqpos : 0 < q := hq₀pos.trans_le hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hqgt : Real.exp (T * (N : ℝ) ^ 2) < q :=
    hq₀.trans_le (by exact_mod_cast hq)
  have hlogq : T * (N : ℝ) ^ 2 < Real.log (q : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hqgt
    simpa using h
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogmul : Real.log (2 * (q : ℝ)) = Real.log 2 + Real.log (q : ℝ) :=
    Real.log_mul (by norm_num) hqR.ne'
  let ex := exists_quadratic_crossing T (Real.log (2 * (q : ℝ))) hT
  let n : ℕ := Nat.find ex
  have hcross : Real.log (2 * (q : ℝ)) ≤ T * (n : ℝ) ^ 2 := Nat.find_spec ex
  have hnN : N ≤ n := by
    by_contra hh
    have hnlt : n < N := Nat.lt_of_not_ge hh
    have hnle : (n : ℝ) ≤ N := by exact_mod_cast hnlt.le
    have hsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hnle 2
    have hprod := mul_le_mul_of_nonneg_left hsq hT.le
    rw [hlogmul] at hcross
    linarith
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hnN
  have hn0 : 0 < n := by omega
  have hnN₀ : N₀ ≤ n := (le_max_left _ _).trans hnN
  obtain ⟨⟨⟨hlo, hup⟩, hAn⟩, hmn⟩ := hN₀ n hnN₀
  have hprev : T * ((n - 1 : ℕ) : ℝ) ^ 2 < Real.log (2 * (q : ℝ)) := by
    exact lt_of_not_ge (Nat.find_min ex (Nat.sub_lt hn0 (by decide)))
  have hprev' : T * ((n : ℝ) - 1) ^ 2 < Real.log 2 + Real.log (q : ℝ) := by
    simpa [Nat.cast_sub hn1, hlogmul] using hprev
  have hνT : 0 ≤ ν * T := mul_nonneg hν0.le hT.le
  have hνabs : 0 ≤ ν * |Real.log 2| := mul_nonneg hν0.le (abs_nonneg _)
  have hlinear : ν * T * (2 * (n : ℝ) - 1) + ν * Real.log 2 ≤
      C * (2 * (n : ℝ) + 1) := by
    have hfirst : ν * T * (2 * (n : ℝ) - 1) ≤
        ν * T * (2 * (n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hνT
    have hsecond : ν * Real.log 2 ≤ ν * |Real.log 2| * (2 * (n : ℝ) + 1) := by
      calc
        ν * Real.log 2 ≤ ν * |Real.log 2| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hν0.le
        _ = ν * |Real.log 2| * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by
          have hn0R : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith) hνabs
    dsimp [C]
    nlinarith
  have hmeshfinal : S * (n : ℝ) ^ 2 ≤ ν * Real.log (q : ℝ) := by
    have hprevν := mul_le_mul_of_nonneg_left hprev'.le hν0.le
    dsimp [sqScale, D] at hmn
    nlinarith
  have hsep : Real.exp (-(S * (n : ℝ) ^ 2)) ≤
      |ξ - (p : ℝ) / (q : ℝ)| := by
    have hh := separation_of_exponential_envelope (A n) (B n) p q ξ
      ((τ + η) * (n : ℝ) ^ 2) (T * (n : ℝ) ^ 2)
      ((α + η) * (n : ℝ) ^ 2) hqpos
      (by
        have he : (-τ - η) * sqScale n = -((τ + η) * (n : ℝ) ^ 2) := by
          unfold sqScale
          ring
        simpa only [he] using hlo)
      (by
        have he : (-τ + η) * sqScale n = -(T * (n : ℝ) ^ 2) := by
          dsimp [T, sqScale]
          ring
        simpa only [he] using hup)
      (by simpa [sqScale] using hAn) hcross
    have hid : (τ + η) * (n : ℝ) ^ 2 + (α + η) * (n : ℝ) ^ 2 =
        S * (n : ℝ) ^ 2 := by dsimp [S]; ring
    simpa only [hid] using hh
  calc
    (q : ℝ) ^ (-ν) = Real.exp (Real.log (q : ℝ) * (-ν)) :=
      Real.rpow_def_of_pos hqR _
    _ ≤ Real.exp (-(S * (n : ℝ) ^ 2)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := hsep

/-- The same hypotheses also prove irrationality, including when some early
forms vanish or early coefficient pairs are degenerate. -/
theorem irrational_and_measure_of_quadratic_forms
    (A B : ℕ → ℤ) (ξ α τ : ℝ) (hα : 0 ≤ α) (hτ : 0 < τ)
    (hne : ∀ᶠ n in atTop, (A n : ℝ) * ξ - B n ≠ 0)
    (hA : QuadExpUpper (fun n => (A n : ℝ)) α)
    (hL : QuadLogRate (fun n => (A n : ℝ) * ξ - B n) (-τ)) :
    Irrational ξ ∧ ApproximationExponentUpper ξ (1 + α / τ) := by
  exact ⟨PaperR7.irrational_of_integer_forms_tendsto_zero ξ A B hne
      (hL.exp_upper.tendsto_zero (by linarith)),
    approximationExponentUpper_of_quadratic_forms A B ξ α τ hα hτ hne hA hL⟩

end ErdosProblems.Erdos1049.PaperR10
