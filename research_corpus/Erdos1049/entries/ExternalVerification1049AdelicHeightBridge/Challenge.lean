/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge: Erdős #1049 sharp adelic height bridge

These statements isolate the strongest exact arithmetic and finite-counting
obstructions presently checked at the rational base `3 / 2`.  They do not
construct an approximation family, bound analytic remainder fibres, or prove
irrationality.
-/

namespace Erdos249257.ExternalVerification1049AdelicHeightBridge

open Polynomial

noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma

noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)

noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2

noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)

def homEvalThreeTwo (W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * 3 ^ i * 2 ^ (W - i)

def bottomJet3 (R W : ℕ) (P : Polynomial ℤ) : ZMod (3 ^ R) :=
  homEvalThreeTwo W P

def topJet2 (S W : ℕ) (P : Polynomial ℤ) : ZMod (2 ^ S) :=
  homEvalThreeTwo W P

abbrev FourJetSignature (R S : ℕ) :=
  (ZMod (3 ^ R) × ZMod (3 ^ R)) ×
    (ZMod (2 ^ S) × ZMod (2 ^ S))

def fourJetSignature (R S W : ℕ) (U V : Polynomial ℤ) :
    FourJetSignature R S :=
  ((bottomJet3 R W U, bottomJet3 R W V),
    (topJet2 S W U, topJet2 S W V))

def selectedFourJetSum {n : ℕ} (R S W : ℕ)
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (ε : Fin n → Bool) : FourJetSignature R S :=
  ∑ i, if ε i then
    fourJetSignature R S W (forms i).1 (forms i).2
  else 0

/-- Finite `q`-Pochhammer product `(q^start;q)_len`. -/
noncomputable def zudilinPochhammerPS (start len : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ Finset.range len,
    (1 - PowerSeries.X ^ (start + r) : PowerSeries ℤ)

/-- The unit factor in the `t`th normalized Zudilin summand. -/
noncomputable def zudilinNormalizedTailUnit (n t : ℕ) : PowerSeries ℤ :=
  zudilinPochhammerPS 1 n ^ 3 * zudilinPochhammerPS (t + 1) n *
    PowerSeries.invOfUnit (zudilinPochhammerPS (n + 1 + t) (n + 1)) 1

/-- The exact `t`th summand of the normalized moment `v_n^*`. -/
noncomputable def zudilinNormalizedTail (n t : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ ((n + 1) * t) * zudilinNormalizedTailUnit n t

/-- The normalized moment, defined coefficientwise by its finite support at
each degree. -/
noncomputable def zudilinNormalizedMoment (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    ∑ t ∈ Finset.range (d / (n + 1) + 1),
      PowerSeries.coeff d (zudilinNormalizedTail n t)

/-- The first nontrivial transformed row
`D₁v^*_(l+1) = v^*_(l+1) - v^*_l`. -/
noncomputable def zudilinFirstTransformedRow (l : ℕ) : PowerSeries ℤ :=
  zudilinNormalizedMoment (l + 1) - zudilinNormalizedMoment l

/-- In every column, the complete initial monomial of the first nontrivial
transformed row is `-6 X^(l+1)`.  This is an unconditional all-column partial
result; no assertion about transformed rows `j ≥ 2` is included. -/
theorem zudilin_firstTransformedRow_initialMonomial (l : ℕ) :
    PowerSeries.order (zudilinFirstTransformedRow l) = l + 1 ∧
      PowerSeries.coeff (l + 1) (zudilinFirstTransformedRow l) = -6 := by
  sorry

/-- The exact upper half of the sharp `41/65` power bracket. -/
theorem threePow_fortyOne_lt_twoPow_sixtyFive : 3 ^ 41 < 2 ^ 65 := by
  sorry

/-- The lower half: the exponent `65` cannot be replaced by `64`. -/
theorem twoPow_sixtyFour_lt_threePow_fortyOne : 2 ^ 64 < 3 ^ 41 := by
  sorry

/-- Uniform deficit for the entire admissible rectangular exponent cone. -/
theorem threeHalves_rectangular_hp_gap_gt_threeThirteenths (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma := by
  sorry

/-- Exact rational ceiling for the cubic Hankel charge threshold. -/
theorem threeHalves_hankelChargeThreshold_lt_eightFortyOne :
    (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41 := by
  sorry

/-- Any scalar extraction under the source ceiling misses the required charge. -/
theorem zudilinScalarContent_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 0 < N)
    (hextracted : extractedDegree ≤ N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  sorry

/-- Scalar content plus the forced first-order border still misses the charge. -/
theorem zudilinScalarPlusBorder_cannot_meet_required_charge
    (N extractedDegree : ℤ) (hN : 2 ≤ N)
    (hextracted : extractedDegree ≤ 2 * N ^ 3 - N) :
    41 * extractedDegree < 39 * (4 * N ^ 3 - 3 * N ^ 2) := by
  sorry

/-- Quantitative fixed-margin exclusion of the positive source scalar ray. -/
theorem three_two_scalar_margin_lt_explicit {C0 C1 : ℝ}
    (hC0 : 0 < C0) (hsource : 2 * C0 ≤ C1) :
    C0 * Real.log 3 - C1 * Real.log 2 <
      -((17 : ℝ) / 41) * C0 * Real.log 2 := by
  sorry

/-- At depth `41T`, `130T + 2S` binary forms force a four-jet collision. -/
theorem exists_distinct_binary_selectors_same_fourJet_of_rank_41
    {n T S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ) (hT : 0 < T)
    (hrank : 130 * T + 2 * S ≤ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum (41 * T) S W forms ε =
        selectedFourJetSum (41 * T) S W forms η := by
  sorry

/-- For `T = 1`, `129 + 2S` selectors are still fewer than the target. -/
theorem fourJet_card_gt_two_pow_of_rank_41 (S : ℕ) :
    2 ^ (129 + 2 * S) < Fintype.card (FourJetSignature 41 S) := by
  sorry

/-- A bounded remainder fibre converts a finite-signature collision into an
escape from the remainder nullspace. -/
theorem exists_ne_map_eq_map_ne_of_card_mul_lt {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : α → γ) (k : ℕ)
    (hg : ∀ x : α, (Finset.univ.filter fun y => g y = g x).card ≤ k)
    (hcard : Fintype.card β * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧ g x ≠ g y := by
  sorry

end Erdos249257.ExternalVerification1049AdelicHeightBridge
