import Erdos249257.GcdMomentCalculus

/-! The third member of the long #249 manuscript's divisor-sum chain: the
`q`-zeta reading `∑_{d≥1} 1/(2ᵈ-1)² = ζ_q(2) - ζ_q(1)` at `q = 1/2`, with
`ζ_q(s) = ∑_{n≥1} n^{s-1} qⁿ/(1-qⁿ)`.  Only the identity is proved; the
irrationality of the value is the cited Postelmans--Van Assche theorem and is
not formalised anywhere in this corpus. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open GcdMomentCalculus
open MersenneLambertLadder
open scoped BigOperators

/-- The manuscript's `q`-zeta value `ζ_q(s) = ∑_{n≥1} n^{s-1} qⁿ/(1-qⁿ)`. -/
def qZeta (q : ℝ) (s : ℕ) : ℝ :=
  ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ (s - 1) * (q ^ (n : ℕ) / (1 - q ^ (n : ℕ)))

private lemma two_le_two_pow' (n : ℕ+) : (2 : ℝ) ≤ (2 : ℝ) ^ (n : ℕ) := by
  calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
    _ ≤ (2 : ℝ) ^ (n : ℕ) := pow_le_pow_right₀ (by norm_num) n.pos

private lemma halfTerm (n : ℕ+) :
    ((1 : ℝ) / 2) ^ (n : ℕ) / (1 - ((1 : ℝ) / 2) ^ (n : ℕ))
      = 1 / ((2 : ℝ) ^ (n : ℕ) - 1) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (n : ℕ) := by positivity
  have h2 := two_le_two_pow' n
  have hpow : ((1 : ℝ) / 2) ^ (n : ℕ) = 1 / (2 : ℝ) ^ (n : ℕ) := by
    rw [div_pow, one_pow]
  have hden : (1 : ℝ) - ((1 : ℝ) / 2) ^ (n : ℕ)
      = ((2 : ℝ) ^ (n : ℕ) - 1) / (2 : ℝ) ^ (n : ℕ) := by
    rw [hpow]
    field_simp
  rw [hden, hpow, div_div_eq_mul_div, one_div_mul_cancel (ne_of_gt hpos)]

private lemma summable_pnat_pow_mul_half (k : ℕ) :
    Summable (fun n : ℕ+ => ((n : ℕ) : ℝ) ^ k * ((1 : ℝ) / 2) ^ (n : ℕ)) := by
  have hr : ‖((1 : ℝ) / 2)‖ < 1 := by
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
    norm_num
  have h : Summable (fun n : ℕ => (n : ℝ) ^ k * ((1 : ℝ) / 2) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k hr
  simpa [Function.comp] using h.comp_injective PNat.coe_injective

private lemma summable_qZetaTerm (k : ℕ) :
    Summable (fun n : ℕ+ => ((n : ℕ) : ℝ) ^ k *
      (((1 : ℝ) / 2) ^ (n : ℕ) / (1 - ((1 : ℝ) / 2) ^ (n : ℕ)))) := by
  have hmaj := (summable_pnat_pow_mul_half k).mul_left 2
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · rw [halfTerm n]
    have h2 := two_le_two_pow' n
    have hd : (0 : ℝ) < (2 : ℝ) ^ (n : ℕ) - 1 := by linarith
    positivity
  · rw [halfTerm n]
    have h2 := two_le_two_pow' n
    have hd : (0 : ℝ) < (2 : ℝ) ^ (n : ℕ) - 1 := by linarith
    have hA : (0 : ℝ) < (2 : ℝ) ^ (n : ℕ) := by positivity
    have hpow : ((1 : ℝ) / 2) ^ (n : ℕ) = 1 / (2 : ℝ) ^ (n : ℕ) := by
      rw [div_pow, one_pow]
    have hnk : (0 : ℝ) ≤ ((n : ℕ) : ℝ) ^ k := by positivity
    have hkey : 1 / ((2 : ℝ) ^ (n : ℕ) - 1) ≤ 2 * ((1 : ℝ) / 2) ^ (n : ℕ) := by
      rw [hpow, mul_one_div, div_le_div_iff₀ hd hA]
      linarith
    calc ((n : ℕ) : ℝ) ^ k * (1 / ((2 : ℝ) ^ (n : ℕ) - 1))
        ≤ ((n : ℕ) : ℝ) ^ k * (2 * ((1 : ℝ) / 2) ^ (n : ℕ)) :=
          mul_le_mul_of_nonneg_left hkey hnk
      _ = 2 * (((n : ℕ) : ℝ) ^ k * ((1 : ℝ) / 2) ^ (n : ℕ)) := by ring

private lemma qZeta_one_eq (q : ℝ) :
    qZeta q 1 = ∑' n : ℕ+, q ^ (n : ℕ) / (1 - q ^ (n : ℕ)) := by
  simp [qZeta]

private lemma qZeta_two_eq (q : ℝ) :
    qZeta q 2 = ∑' n : ℕ+, ((n : ℕ) : ℝ) * (q ^ (n : ℕ) / (1 - q ^ (n : ℕ))) := by
  simp [qZeta]

/-- **The `q`-zeta anchor of the divisor-sum identity** (`prop:zetaq`,
`catalogue:mob:a4`): `ζ_q(2) - ζ_q(1) = ∑_{d≥1} 1/(2ᵈ-1)²` at `q = 1/2`. -/
theorem qZeta_half_two_sub_one :
    qZeta ((1 : ℝ) / 2) 2 - qZeta ((1 : ℝ) / 2) 1
      = ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  have hS1 : Summable (fun n : ℕ+ =>
      ((1 : ℝ) / 2) ^ (n : ℕ) / (1 - ((1 : ℝ) / 2) ^ (n : ℕ))) :=
    (summable_qZetaTerm 0).congr fun n => by rw [pow_zero, one_mul]
  have hS2 : Summable (fun n : ℕ+ => ((n : ℕ) : ℝ) *
      (((1 : ℝ) / 2) ^ (n : ℕ) / (1 - ((1 : ℝ) / 2) ^ (n : ℕ)))) :=
    (summable_qZetaTerm 1).congr fun n => by rw [pow_one]
  have hw : ∀ d : ℕ, 0 < d → |((d : ℝ) - 1)| ≤ (d : ℝ) := by
    intro d hd
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hlam := tsum_lambert_linear_weight (fun m : ℕ => ((m : ℝ) - 1)) hw
    (r := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  have hdiv : ∀ n : ℕ+,
      (∑ e ∈ (n : ℕ).divisors, (((e : ℕ) : ℝ) - 1))
        = (∑ e ∈ (n : ℕ).divisors, (((n : ℕ) / e : ℕ) : ℝ))
            - (((n : ℕ).divisors.card : ℕ) : ℝ) := by
    intro n
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.sum_div_divisors (n : ℕ) (fun d => (d : ℝ))]
  calc qZeta ((1 : ℝ) / 2) 2 - qZeta ((1 : ℝ) / 2) 1
      = (∑' n : ℕ+, ((n : ℕ) : ℝ) *
            (((1 : ℝ) / 2) ^ (n : ℕ) / (1 - ((1 : ℝ) / 2) ^ (n : ℕ))))
          - ∑' n : ℕ+, ((1 : ℝ) / 2) ^ (n : ℕ) / (1 - ((1 : ℝ) / 2) ^ (n : ℕ)) := by
        rw [qZeta_one_eq, qZeta_two_eq]
    _ = ∑' n : ℕ+, (((n : ℕ) : ℝ) - 1) *
            (((1 : ℝ) / 2) ^ (n : ℕ) / (1 - ((1 : ℝ) / 2) ^ (n : ℕ))) := by
        rw [← hS2.tsum_sub hS1]
        exact tsum_congr fun n => by ring
    _ = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, (((e : ℕ) : ℝ) - 1))
            * ((1 : ℝ) / 2) ^ (n : ℕ) := hlam
    _ = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (((n : ℕ) / e : ℕ) : ℝ))
            - (((n : ℕ).divisors.card : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
        exact tsum_congr fun n => by rw [hdiv n]
    _ = ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 :=
        tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series.symm

#print axioms qZeta_half_two_sub_one
end ErdosProblems.Erdos249.PaperCompleteR21
