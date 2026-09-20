import ErdosProblems.Erdos257.PaperCompleteR21.LogarithmicInitialInterval

/-!
# The probabilistic estimates of the arithmetic logarithmic counterexample

The three probabilistic steps of the long Erdős #257 `thm`
"arithmetic logarithmic counterexample"
(`paper/reasoning-parts/erdos257/a257_front.tex:9212`), each in the finite
counting form the paper's uniform sampling gives.

* "the mean of `Z_q(N+r)` is `μ_r = ∑_{d ∣ r} S_{q,d} ≥ (4/H) σ(r) ≥ 4r`, and
  its variance is at most `μ_r`": `sum_sq_sub_mean_le` computes the second
  moment of a sum of indicator variables from the marginal and pairwise joint
  frequencies alone, which is exactly what the Chinese remainder theorem
  supplies for the tag events.
* "Chebyshev's inequality gives
  `ℙ(Z_q(N+r) < r ∣ q ∣ N+r) ≤ μ_r/(μ_r - r)² ≤ 4/(9r) ≤ 4/9`, thus success has
  conditional probability at least `1/2`": `card_lt_le_of_sum_sq` is Chebyshev
  as a count, and `mean_div_sq_le` is the elementary monotonicity
  `μ/(μ-r)² ≤ 4/(9r)` for `μ ≥ 4r`.
* "the `E_q` are independent ..., it follows that
  `ℙ_L(U_F > 1) ≥ 1 - ∏_q (1 - ℙ_L(E_q)) ≥ 1 - exp(-∑_q ℙ_L(E_q))`":
  `prod_one_sub_le_exp_neg_sum`.

These are the estimates, stated over an arbitrary finite sample set.  Producing
the sample set itself — the Chinese remainder theorem identification of `N`
uniform modulo `Q` subject to `L ∣ N` with independent residues at the parent
and tag primes — is not formalised here.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Finset

/-! ### Indicator sums over a finite sample set -/

theorem sum_indicator_eq_card {α : Type*} [DecidableEq α] {Ω A : Finset α}
    (hA : A ⊆ Ω) :
    (∑ ω ∈ Ω, (if ω ∈ A then (1 : ℝ) else 0)) = (A.card : ℝ) := by
  classical
  rw [Finset.sum_boole]
  have hfil : Ω.filter (fun ω => ω ∈ A) = A := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hA]
  rw [hfil]

theorem sum_indicator_mul_eq_card {α : Type*} [DecidableEq α] {Ω A B : Finset α}
    (hA : A ⊆ Ω) :
    (∑ ω ∈ Ω, (if ω ∈ A then (1 : ℝ) else 0) * (if ω ∈ B then (1 : ℝ) else 0))
      = ((A ∩ B).card : ℝ) := by
  classical
  have hstep : ∀ ω : α,
      (if ω ∈ A then (1 : ℝ) else 0) * (if ω ∈ B then (1 : ℝ) else 0)
        = (if ω ∈ A ∩ B then (1 : ℝ) else 0) := by
    intro ω
    by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ B <;>
      simp [h1, h2, Finset.mem_inter]
  simp only [hstep]
  exact sum_indicator_eq_card (Finset.Subset.trans Finset.inter_subset_left hA)

/-- The paper's "the mean of `Z_q(N+r)` is `μ_r` and its variance is at most
`μ_r`", as an exact second-moment computation from the marginal frequencies
`a p` and the pairwise joint frequencies `a p · a p'` alone. -/
theorem sum_sq_sub_mean_eq {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (Ω : Finset α) (S : Finset ι) (A : ι → Finset α) (a : ι → ℝ)
    (hA : ∀ p ∈ S, A p ⊆ Ω)
    (hmarg : ∀ p ∈ S, ((A p).card : ℝ) = (Ω.card : ℝ) * a p)
    (hpair : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' →
      ((A p ∩ A p').card : ℝ) = (Ω.card : ℝ) * (a p * a p')) :
    (∑ ω ∈ Ω, ((∑ p ∈ S, (if ω ∈ A p then (1 : ℝ) else 0)) - ∑ p ∈ S, a p) ^ 2)
      = (Ω.card : ℝ) * ((∑ p ∈ S, a p) - ∑ p ∈ S, a p ^ 2) := by
  classical
  have hmean : (∑ ω ∈ Ω, ∑ p ∈ S, (if ω ∈ A p then (1 : ℝ) else 0))
      = (Ω.card : ℝ) * ∑ p ∈ S, a p := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [sum_indicator_eq_card (hA p hp), hmarg p hp]
  have hrow : ∀ p ∈ S, (∑ p' ∈ S, ((A p ∩ A p').card : ℝ))
      = (Ω.card : ℝ) * (a p * (∑ p' ∈ S, a p') + a p - a p * a p) := by
    intro p hp
    have hsplit : (∑ p' ∈ S, ((A p ∩ A p').card : ℝ))
        = ((A p ∩ A p).card : ℝ) + ∑ p' ∈ S.erase p, ((A p ∩ A p').card : ℝ) :=
      (Finset.add_sum_erase S (fun p' => ((A p ∩ A p').card : ℝ)) hp).symm
    have hsplit2 : (∑ p' ∈ S, (Ω.card : ℝ) * (a p * a p'))
        = (Ω.card : ℝ) * (a p * a p)
          + ∑ p' ∈ S.erase p, (Ω.card : ℝ) * (a p * a p') :=
      (Finset.add_sum_erase S (fun p' => (Ω.card : ℝ) * (a p * a p')) hp).symm
    have herase : (∑ p' ∈ S.erase p, ((A p ∩ A p').card : ℝ))
        = ∑ p' ∈ S.erase p, (Ω.card : ℝ) * (a p * a p') := by
      refine Finset.sum_congr rfl fun p' hp' => ?_
      obtain ⟨hne, hp'S⟩ := Finset.mem_erase.mp hp'
      exact hpair p hp p' hp'S (Ne.symm hne)
    have hself : ((A p ∩ A p).card : ℝ) = (Ω.card : ℝ) * a p := by
      rw [Finset.inter_self]
      exact hmarg p hp
    have hfull : (∑ p' ∈ S, (Ω.card : ℝ) * (a p * a p'))
        = (Ω.card : ℝ) * (a p * ∑ p' ∈ S, a p') := by
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [hsplit, hself, herase]
    rw [hfull] at hsplit2
    linarith
  have hsq : ∀ ω : α, (∑ p ∈ S, (if ω ∈ A p then (1 : ℝ) else 0)) ^ 2
      = ∑ p ∈ S, ∑ p' ∈ S,
        (if ω ∈ A p then (1 : ℝ) else 0) * (if ω ∈ A p' then (1 : ℝ) else 0) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  have hsecond : (∑ ω ∈ Ω, (∑ p ∈ S, (if ω ∈ A p then (1 : ℝ) else 0)) ^ 2)
      = (Ω.card : ℝ) * ((∑ p ∈ S, a p) * (∑ p ∈ S, a p)
          + (∑ p ∈ S, a p) - ∑ p ∈ S, a p ^ 2) := by
    simp only [hsq]
    rw [Finset.sum_comm]
    have hinner : ∀ p ∈ S,
        (∑ ω ∈ Ω, ∑ p' ∈ S,
          (if ω ∈ A p then (1 : ℝ) else 0) * (if ω ∈ A p' then (1 : ℝ) else 0))
          = ∑ p' ∈ S, ((A p ∩ A p').card : ℝ) := by
      intro p hp
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p' _ => ?_
      exact sum_indicator_mul_eq_card (hA p hp)
    rw [Finset.sum_congr rfl hinner, Finset.sum_congr rfl hrow, ← Finset.mul_sum]
    congr 1
    have hterm : ∀ p : ι, a p * (∑ p' ∈ S, a p') + a p - a p * a p
        = a p * (∑ p' ∈ S, a p') + a p - a p ^ 2 := fun p => by ring
    simp only [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hexpand : (∑ ω ∈ Ω, ((∑ p ∈ S, (if ω ∈ A p then (1 : ℝ) else 0))
        - ∑ p ∈ S, a p) ^ 2)
      = (∑ ω ∈ Ω, (∑ p ∈ S, (if ω ∈ A p then (1 : ℝ) else 0)) ^ 2)
        - 2 * (∑ p ∈ S, a p)
            * (∑ ω ∈ Ω, ∑ p ∈ S, (if ω ∈ A p then (1 : ℝ) else 0))
        + (Ω.card : ℝ) * (∑ p ∈ S, a p) ^ 2 := by
    have hpt : ∀ ω : α,
        ((∑ p ∈ S, (if ω ∈ A p then (1 : ℝ) else 0)) - ∑ p ∈ S, a p) ^ 2
          = (∑ p ∈ S, (if ω ∈ A p then (1 : ℝ) else 0)) ^ 2
            - 2 * (∑ p ∈ S, a p) * (∑ p ∈ S, (if ω ∈ A p then (1 : ℝ) else 0))
            + (∑ p ∈ S, a p) ^ 2 := fun ω => by ring
    simp only [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
  rw [hexpand, hsecond, hmean]
  ring

/-- "its variance is at most `μ_r`". -/
theorem sum_sq_sub_mean_le {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (Ω : Finset α) (S : Finset ι) (A : ι → Finset α) (a : ι → ℝ)
    (hA : ∀ p ∈ S, A p ⊆ Ω)
    (hmarg : ∀ p ∈ S, ((A p).card : ℝ) = (Ω.card : ℝ) * a p)
    (hpair : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' →
      ((A p ∩ A p').card : ℝ) = (Ω.card : ℝ) * (a p * a p')) :
    (∑ ω ∈ Ω, ((∑ p ∈ S, (if ω ∈ A p then (1 : ℝ) else 0)) - ∑ p ∈ S, a p) ^ 2)
      ≤ (Ω.card : ℝ) * ∑ p ∈ S, a p := by
  rw [sum_sq_sub_mean_eq Ω S A a hA hmarg hpair]
  have hsq : (0 : ℝ) ≤ ∑ p ∈ S, a p ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg (a p)
  have hcard : (0 : ℝ) ≤ (Ω.card : ℝ) := Nat.cast_nonneg _
  nlinarith

/-! ### Chebyshev as a count -/

/-- Chebyshev's inequality in the counting form the paper's uniform sampling
gives: a second-moment bound `∑_ω (X ω - μ)² ≤ |Ω| V` bounds the number of
samples with `X < r` by `|Ω| V/(μ - r)²`. -/
theorem card_lt_le_of_sum_sq {α : Type*} [DecidableEq α] (Ω : Finset α)
    (X : α → ℝ) (μ V r : ℝ) (hr : r < μ)
    (hV : (∑ ω ∈ Ω, (X ω - μ) ^ 2) ≤ (Ω.card : ℝ) * V) :
    (((Ω.filter (fun ω => X ω < r)).card : ℝ)) * (μ - r) ^ 2
      ≤ (Ω.card : ℝ) * V := by
  classical
  have hsub : (∑ ω ∈ Ω.filter (fun ω => X ω < r), (X ω - μ) ^ 2)
      ≤ ∑ ω ∈ Ω, (X ω - μ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro ω _ _
    exact sq_nonneg _
  have hlow : ((Ω.filter (fun ω => X ω < r)).card : ℝ) * (μ - r) ^ 2
      ≤ ∑ ω ∈ Ω.filter (fun ω => X ω < r), (X ω - μ) ^ 2 := by
    have hterm : ∀ ω ∈ Ω.filter (fun ω => X ω < r), (μ - r) ^ 2 ≤ (X ω - μ) ^ 2 := by
      intro ω hω
      have hlt : X ω < r := (Finset.mem_filter.mp hω).2
      have h1 : 0 ≤ μ - r := by linarith
      nlinarith
    calc ((Ω.filter (fun ω => X ω < r)).card : ℝ) * (μ - r) ^ 2
        = ∑ _ω ∈ Ω.filter (fun ω => X ω < r), (μ - r) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hterm
  linarith

/-- The paper's `μ_r/(μ_r - r)² ≤ 4/(9r)` for `μ_r ≥ 4r`: the bound is
decreasing in the mean, so the extreme case `μ_r = 4r` is the worst. -/
theorem mean_div_sq_le {μ r : ℝ} (hr : 0 < r) (hμ : 4 * r ≤ μ) :
    μ / (μ - r) ^ 2 ≤ 4 / (9 * r) := by
  have hden : 0 < (μ - r) ^ 2 := by nlinarith
  have hr9 : 0 < 9 * r := by linarith
  rw [div_le_div_iff₀ hden hr9]
  nlinarith [sq_nonneg (μ - 4 * r)]

/-! ### The independence product -/

/-- "It follows that `ℙ_L(U_F > 1) ≥ 1 - ∏_q(1 - ℙ_L(E_q)) ≥ exp(-∑_q ℙ_L(E_q))`
subtracted from one", from `1 - x ≤ e^{-x}`. -/
theorem prod_one_sub_le_exp_neg_sum {ι : Type*} (B : Finset ι) (x : ι → ℝ)
    (hx1 : ∀ q ∈ B, x q ≤ 1) :
    ∏ q ∈ B, (1 - x q) ≤ Real.exp (-∑ q ∈ B, x q) := by
  have hexp : Real.exp (-∑ q ∈ B, x q) = ∏ q ∈ B, Real.exp (-x q) := by
    rw [← Real.exp_sum]
    congr 1
    simp
  rw [hexp]
  refine Finset.prod_le_prod (fun q hq => by linarith [hx1 q hq]) ?_
  intro q _
  linarith [Real.add_one_le_exp (-x q)]

#print axioms sum_sq_sub_mean_eq
#print axioms sum_sq_sub_mean_le
#print axioms card_lt_le_of_sum_sq
#print axioms mean_div_sq_le
#print axioms prod_one_sub_le_exp_neg_sum

end ErdosProblems.Erdos257.PaperCompleteR21

end
