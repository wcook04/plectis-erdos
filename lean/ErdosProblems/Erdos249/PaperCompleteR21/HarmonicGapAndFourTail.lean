import Erdos249257.FirstHarmonicPivot
import Erdos249257.PrimeJumpWindow

/-! Paper-form restatements of two long-paper environments:

* `catalogue:mob:e1` — "The block norm condition implies irrationality": a
  cofinal supply of dyadic blocks `X ≤ N < 2X` on which the first additive
  character `E(h,N,L)` has norm at most `(21/25)X`, under the size condition
  `16(2X+h+L+2) ≤ 2^L`, gives `S ∉ ℚ`.  The intermediate real-part bound
  `Re ∑ E ≤ (9/10)X`, the numerical gap `cos(π/8) > 9/10`, and the passage to
  a finite residue certificate are recorded separately.
* `catalogue:mob:e2` — "A four-tail residue criterion": the four-tail
  combination `J(H,p)`, its finite numerator `W(H,p,L)`, the error bound
  `|2^L J - W| ≤ B`, the residue criterion, the cofinal supply implication,
  and the checked instance `(H,p,L) = (12,5,15)`.

Here `R_N = totientTail N`, `D(h,N,L) = windowDiscrepancy h N L`,
`H(t) = periodLcm t`, and `E(h,N,L) = windowFirstExp h N L`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.PrimeJumpWindow

/-! ### `catalogue:mob:e1` — the block norm condition -/

/-- The numerical gap driving the averaging step: `cos(π/8) > 9/10`. -/
theorem nine_tenths_lt_cos_pi_div_eight : (9 / 10 : ℝ) < Real.cos (Real.pi / 8) := by
  rw [Real.cos_pi_div_eight]
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h2 : (1.4 : ℝ) < Real.sqrt 2 := by nlinarith
  have hnn : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by linarith
  have hsq : Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 := Real.sq_sqrt hnn
  have hnns : (0 : ℝ) ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
  have hs : (1.8 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by nlinarith
  linarith

/-- The complex norm bound implies the real-part bound `Re ∑ E ≤ (9/10)X`. -/
theorem first_harmonic_re_bound_of_norm_bound {h X L : ℕ}
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X := by
  calc
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L)
        = (∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L).re := by simp
    _ ≤ ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ := Complex.re_le_norm _
    _ ≤ (21 / 25 : ℝ) * X := hgap
    _ ≤ (9 / 10 : ℝ) * X := by
        have hXnonneg : (0 : ℝ) ≤ X := by positivity
        nlinarith

/-- Under the displayed size condition, the real-part bound already produces a
finite residue certificate inside the block. -/
theorem exists_certificate_of_first_harmonic_real_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hre : (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L :=
  exists_certifiedKill_of_first_harmonic_gap hX hroom hre

/-- The same conclusion straight from the norm bound. -/
theorem exists_certificate_of_first_harmonic_norm_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L :=
  exists_certifiedKill_of_first_harmonic_norm_gap hX hroom hgap

/-- **The block norm condition implies irrationality.**  If for every `h ≥ 1`
and every threshold `X₀` there are `X, L` with `X ≥ max(X₀,1)`,
`16(2X+h+L+2) ≤ 2^L` and `‖∑_{X ≤ N < 2X} E(h,N,L)‖ ≤ (21/25)X`, then
`S ∉ ℚ`. -/
theorem irrational_of_first_harmonic_norm_gap
    (hgap : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X L : ℕ,
      max X₀ 1 ≤ X ∧ 16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_first_harmonic_norm_gap hgap

/-! ### `catalogue:mob:e2` — the four-tail residue criterion -/

/-- The diagonal window discrepancy is a difference of window numerators. -/
theorem windowDiscrepancy_diagonal_eq (M L : ℕ) :
    windowDiscrepancy M M L =
      (windowNumerator (2 * M) L : ℤ) - (windowNumerator M L : ℤ) := by
  unfold windowDiscrepancy windowNumerator
  push_cast
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show M + M + 1 + j = 2 * M + 1 + j from by ring]
  ring

/-- The paper's finite numerator `W(H,p,L) = D(pH,pH,L) - p·D(H,H,L)` is the
tree's four-vertex window commutator. -/
theorem four_tail_window_eq (H p L : ℕ) :
    windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L =
      primeJumpWindowCommutator H p L := by
  unfold primeJumpWindowCommutator
  rw [windowDiscrepancy_diagonal_eq (p * H) L, windowDiscrepancy_diagonal_eq H L,
    show 2 * (p * H) = 2 * p * H from by ring]
  ring

/-- The paper's four-tail combination
`J(H,p) = R_{2pH} - R_{pH} - p R_{2H} + p R_H`. -/
theorem four_tail_combination_eq (H p : ℕ) :
    primeJumpTailCommutator H p =
      totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H := by
  unfold primeJumpTailCommutator diagonalTailDifferenceAt
  rw [show 2 * (p * H) = 2 * p * H from by ring]
  ring

/-- **The error bound** `|2^L J(H,p) - W(H,p,L)| ≤ B(H,p,L)` with
`B(H,p,L) = 3pH + (p+1)(L+2)`. -/
theorem four_tail_error_bound (H p L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (2 * p * H) - totientTail (p * H)
          - p * totientTail (2 * H) + p * totientTail H)
        - ((windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L : ℤ) : ℝ)|
      ≤ ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℝ) := by
  obtain ⟨e, hsplit, hbound⟩ := primeJumpTailCommutator_eq_window_add_remainder H p L
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  rw [four_tail_window_eq H p L, ← four_tail_combination_eq H p, hsplit]
  have hrw : (2 : ℝ) ^ L * ((primeJumpWindowCommutator H p L : ℝ) / 2 ^ L + e)
      - (primeJumpWindowCommutator H p L : ℝ) = e * 2 ^ L := by
    field_simp
    ring
  rw [hrw]
  simpa [primeJumpSharpRadius] using hbound

/-- The tail enclosure used for the error bound: `0 ≤ R_n ≤ n + 2`. -/
theorem totientTail_bounds (n : ℕ) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 2 :=
  ⟨(totientTail_pos n).le, totientTail_le n⟩

/-- **The converse direction.**  Rationality makes both diagonal differences
occurring in `J(H(t),p)` integral for every sufficiently large `t`. -/
theorem rational_forces_four_tail_diagonals_integral
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ p : ℕ, 0 < p →
      (totientTail (2 * periodLcm t) - totientTail (periodLcm t) ∈
          Set.range ((↑) : ℤ → ℝ)) ∧
        (totientTail (2 * (p * periodLcm t)) - totientTail (p * periodLcm t) ∈
          Set.range ((↑) : ℤ → ℝ)) := by
  obtain ⟨t₁, hflat⟩ := rational_totient_series_forces_lcm_cone_flatness hrat
  refine ⟨t₁, fun t ht p hp => ⟨?_, ?_⟩⟩
  · have hone := hflat t ht 1 1 (by omega)
    rwa [show 1 * periodLcm t + 1 * periodLcm t = 2 * periodLcm t from by ring,
      one_mul] at hone
  · have hpp := hflat t ht p p hp
    rwa [show p * periodLcm t + p * periodLcm t = 2 * (p * periodLcm t) from by ring] at hpp

/-- **The residue criterion.**  If `B < W mod 2^L < 2^L - B` then
`J(H,p) ∉ ℤ`. -/
theorem four_tail_criterion_sound {H p L : ℕ}
    (hlow : ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ) <
      (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L)
    (hhigh : (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L <
      2 ^ L - ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ)) :
    totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H ∉ Set.range ((↑) : ℤ → ℝ) := by
  rw [four_tail_window_eq H p L] at hlow hhigh
  have hkill : primeJumpSharpKill H p L := by
    constructor
    · simpa [primeJumpSharpRadius] using hlow
    · simpa [primeJumpSharpRadius] using hhigh
  rw [← four_tail_combination_eq H p]
  exact primeJumpTailCommutator_notMem_int_of_sharpKill hkill

/-- **The cofinal supply implication.**  If for every `t₀` there are `t ≥ t₀`,
`p ≥ 1` and `L` satisfying the criterion at `H = H(t)`, then `S ∉ ℚ`. -/
theorem irrational_of_four_tail_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ p L : ℕ, 1 ≤ p ∧
      ((3 * p * periodLcm t + (p + 1) * (L + 2) : ℕ) : ℤ) <
        (windowDiscrepancy (p * periodLcm t) (p * periodLcm t) L
          - p * windowDiscrepancy (periodLcm t) (periodLcm t) L) % 2 ^ L ∧
      (windowDiscrepancy (p * periodLcm t) (p * periodLcm t) L
          - p * windowDiscrepancy (periodLcm t) (periodLcm t) L) % 2 ^ L <
        2 ^ L - ((3 * p * periodLcm t + (p + 1) * (L + 2) : ℕ) : ℤ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_primeJumpSharpKill_supply fun t₀ => ?_
  obtain ⟨t, ht, p, L, hp, hlow, hhigh⟩ := hsupply t₀
  rw [four_tail_window_eq (periodLcm t) p L] at hlow hhigh
  refine ⟨t, ht, p, L, hp, ?_, ?_⟩
  · simpa [primeJumpSharpRadius] using hlow
  · simpa [primeJumpSharpRadius] using hhigh

/-- The checked instance `(H,p,L) = (12,5,15)`: `W mod 2^L = 18834` and
`B = 282`, so the criterion fires. -/
theorem four_tail_checked_instance :
    (windowDiscrepancy (5 * 12) (5 * 12) 15
        - ((5 : ℕ) : ℤ) * windowDiscrepancy 12 12 15) % 2 ^ 15 = 18834 ∧
      (3 * 5 * 12 + (5 + 1) * (15 + 2) : ℕ) = 282 := by
  refine ⟨?_, by norm_num⟩
  rw [four_tail_window_eq 12 5 15]
  set_option maxRecDepth 100000 in decide

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.nine_tenths_lt_cos_pi_div_eight
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.first_harmonic_re_bound_of_norm_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_real_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_norm_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_first_harmonic_norm_gap
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.windowDiscrepancy_diagonal_eq
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.four_tail_window_eq
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.four_tail_combination_eq
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.four_tail_error_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientTail_bounds
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_four_tail_diagonals_integral
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.four_tail_criterion_sound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_four_tail_supply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.four_tail_checked_instance
