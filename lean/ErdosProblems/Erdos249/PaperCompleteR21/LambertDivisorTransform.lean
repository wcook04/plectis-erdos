import Erdos249257.MersenneLambertLadder
import Erdos249257.CertificateKernel

/-! The Lambert-series identities of the long #249 manuscript
(`catalogue:cert:d7`): for an arithmetic function whose sums converge
absolutely, `L(f) = ∑_{n≥1} f(n)/(2ⁿ-1)` equals `∑_{m≥1} (f*1)(m)/2^m`; and
for `α = φ * μ` one has `α*1 = φ` and `L(α) = S`. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open Erdos249257
open MersenneLambertLadder
open scoped BigOperators

/-- The manuscript's Lambert value `L(f) = ∑_{n≥1} f(n)/(2ⁿ-1)`. -/
def lambertValue (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ+, f (n : ℕ) / ((2 : ℝ) ^ (n : ℕ) - 1)

private lemma tsum_pow_succ_of_lt_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑' j : ℕ, x ^ (j + 1) = x / (1 - x) := by
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one hnorm, ← tsum_mul_left]
  exact tsum_congr fun j => pow_succ' x j

private lemma halfTerm' (d : ℕ+) :
    ((1 : ℝ) / 2) ^ (d : ℕ) / (1 - ((1 : ℝ) / 2) ^ (d : ℕ))
      = 1 / ((2 : ℝ) ^ (d : ℕ) - 1) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (d : ℕ) := by positivity
  have hpow : ((1 : ℝ) / 2) ^ (d : ℕ) = 1 / (2 : ℝ) ^ (d : ℕ) := by
    rw [div_pow, one_pow]
  have hden : (1 : ℝ) - ((1 : ℝ) / 2) ^ (d : ℕ)
      = ((2 : ℝ) ^ (d : ℕ) - 1) / (2 : ℝ) ^ (d : ℕ) := by
    rw [hpow]
    field_simp
  rw [hden, hpow, div_div_eq_mul_div, one_div_mul_cancel (ne_of_gt hpos)]

/-- **The Lambert divisor transform** (`catalogue:cert:d7`, first display):
if the expanded double series converges absolutely, then
`L(f) = ∑_{m≥1} (f*1)(m)/2^m`, where `(f*1)(m) = ∑_{e ∣ m} f(e)`. -/
theorem lambertValue_eq_divisor_sum_series (f : ℕ → ℝ)
    (hf : Summable (fun p : ℕ+ × ℕ+ =>
      f (p.1 : ℕ) * ((1 : ℝ) / 2) ^ ((p.1 : ℕ) * (p.2 : ℕ)))) :
    lambertValue f
      = ∑' m : ℕ+, (∑ e ∈ (m : ℕ).divisors, f e) * ((1 : ℝ) / 2) ^ (m : ℕ) := by
  have hterm : ∀ d : ℕ+, f (d : ℕ) / ((2 : ℝ) ^ (d : ℕ) - 1)
      = ∑' m : ℕ+, f (d : ℕ) * ((1 : ℝ) / 2) ^ ((d : ℕ) * (m : ℕ)) := by
    intro d
    have hx0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (d : ℕ) := by positivity
    have hx1 : ((1 : ℝ) / 2) ^ (d : ℕ) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) d.pos.ne'
    have hgeo : ∑' j : ℕ, (((1 : ℝ) / 2) ^ (d : ℕ)) ^ (j + 1)
        = ((1 : ℝ) / 2) ^ (d : ℕ) / (1 - ((1 : ℝ) / 2) ^ (d : ℕ)) :=
      tsum_pow_succ_of_lt_one hx0 hx1
    calc f (d : ℕ) / ((2 : ℝ) ^ (d : ℕ) - 1)
        = f (d : ℕ) * (((1 : ℝ) / 2) ^ (d : ℕ) / (1 - ((1 : ℝ) / 2) ^ (d : ℕ))) := by
          rw [halfTerm' d, mul_one_div]
      _ = f (d : ℕ) * ∑' j : ℕ, (((1 : ℝ) / 2) ^ (d : ℕ)) ^ (j + 1) := by rw [hgeo]
      _ = ∑' j : ℕ, f (d : ℕ) * (((1 : ℝ) / 2) ^ (d : ℕ)) ^ (j + 1) := tsum_mul_left.symm
      _ = ∑' m : ℕ+, f (d : ℕ) * ((1 : ℝ) / 2) ^ ((d : ℕ) * (m : ℕ)) := by
          rw [← tsum_pnat_eq_tsum_succ
            (f := fun j : ℕ => f (d : ℕ) * (((1 : ℝ) / 2) ^ (d : ℕ)) ^ j)]
          exact tsum_congr fun m => by rw [← pow_mul]
  have hsig : Summable
      (fun x : (Σ n : ℕ+, {y // y ∈ ((n : ℕ)).divisorsAntidiagonal}) =>
        f x.2.1.1 * ((1 : ℝ) / 2) ^ (x.2.1.1 * x.2.1.2)) := by
    have h := (Equiv.summable_iff sigmaAntidiagonalEquivProd).mpr hf
    refine h.congr fun x => ?_
    rcases x with ⟨n, ⟨⟨a, e⟩, hae⟩⟩
    simp [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors]
  calc lambertValue f
      = ∑' d : ℕ+, ∑' m : ℕ+, f (d : ℕ) * ((1 : ℝ) / 2) ^ ((d : ℕ) * (m : ℕ)) :=
        tsum_congr hterm
    _ = ∑' p : ℕ+ × ℕ+, f (p.1 : ℕ) * ((1 : ℝ) / 2) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
        (hf.tsum_prod).symm
    _ = ∑' x : (Σ n : ℕ+, {y // y ∈ ((n : ℕ)).divisorsAntidiagonal}),
          f x.2.1.1 * ((1 : ℝ) / 2) ^ (x.2.1.1 * x.2.1.2) := by
        rw [← sigmaAntidiagonalEquivProd.tsum_eq
          (f := fun p : ℕ+ × ℕ+ =>
            f (p.1 : ℕ) * ((1 : ℝ) / 2) ^ ((p.1 : ℕ) * (p.2 : ℕ)))]
        refine tsum_congr fun x => ?_
        rcases x with ⟨n, ⟨⟨a, e⟩, hae⟩⟩
        simp [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors]
    _ = ∑' n : ℕ+, ∑' y : {y // y ∈ ((n : ℕ)).divisorsAntidiagonal},
          f y.1.1 * ((1 : ℝ) / 2) ^ (y.1.1 * y.1.2) := Summable.tsum_sigma hsig
    _ = ∑' m : ℕ+, (∑ e ∈ (m : ℕ).divisors, f e) * ((1 : ℝ) / 2) ^ (m : ℕ) := by
        refine tsum_congr fun n => ?_
        rw [tsum_fintype, Finset.univ_eq_attach,
          Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
            (fun y : ℕ × ℕ => f y.1 * ((1 : ℝ) / 2) ^ (y.1 * y.2)),
          Nat.sum_divisorsAntidiagonal (fun d e => f d * ((1 : ℝ) / 2) ^ (d * e))]
        have hstep : ∀ d ∈ (n : ℕ).divisors,
            f d * ((1 : ℝ) / 2) ^ (d * ((n : ℕ) / d))
              = f d * ((1 : ℝ) / 2) ^ (n : ℕ) := by
          intro d hd
          rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
        rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]

/-- **`α * 1 = φ` for `α = φ * μ`** (`catalogue:cert:d7`, second sentence). -/
theorem alpha_divisor_sum_eq_totient (n : ℕ) :
    ∑ e ∈ n.divisors, ((primWeight e : ℤ) : ℝ) = (Nat.totient n : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (sum_divisors_primWeight n)
  push_cast at h
  simpa using h

/-- **`L(α) = S`** (`catalogue:cert:d7`, second sentence): the Lambert value
of `α = φ * μ` is the #249 constant. -/
theorem lambertValue_alpha_eq_totientSeries :
    lambertValue (fun d => ((primWeight d : ℤ) : ℝ))
      = ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := by
  have hlam := tsum_primWeight_lambert (r := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  have hleft : lambertValue (fun d => ((primWeight d : ℤ) : ℝ))
      = ∑' d : ℕ+, ((primWeight (d : ℕ) : ℤ) : ℝ) *
          (((1 : ℝ) / 2) ^ (d : ℕ) / (1 - ((1 : ℝ) / 2) ^ (d : ℕ))) := by
    unfold lambertValue
    refine tsum_congr fun d => ?_
    rw [halfTerm' d, mul_one_div]
  rw [hleft, hlam, ← tsum_totient_div_pow_two_eq_pnat_half_pow]

#print axioms lambertValue_eq_divisor_sum_series
#print axioms alpha_divisor_sum_eq_totient
#print axioms lambertValue_alpha_eq_totientSeries
end ErdosProblems.Erdos249.PaperCompleteR21
