import Erdos249257.MersenneShadowDenominatorGrowth
import Erdos249257.LcmConeFlatness
import Mathlib.Tactic

/-!
# Diagonal pincer decomposition

This file wires the exact reduced explicit shadow into the actual lcm-diagonal
tail difference.  The scaled Möbius shadow is retained canonically in `ℚ`, with
reduced numerator `a_t` and denominator `d_t`, and separated from the residual
foreign defect by definition.  The primary exact algebraic pincer is

`diagonal ∈ ℤ ↔ d_t * foreignDefect = -a_t (mod d_t)`.

For compatibility with the finite T4 channel interface, each selected target
representative `u` may still be split off from the explicit shadow, leaving an
orthogonal complement.  That projected pincer is

`diagonal ∈ ℤ ↔ m * (foreignDefect + channelComplement) = -u (mod m)`.

The final theorems expose both supply sockets from the master development.  They are
conditional implications: an unbounded supply of channel misses gives an
unbounded supply of non-integral diagonal cells, which the already-landed
completeness theorem converts to irrationality.  This file does not prove the
avoidance supply itself and does not assert that denominator growth implies a
miss.
-/

namespace Erdos249257.DiagonalPincerDecomposition

open MersenneShadowCyclotomicNoncollapse
open CyclotomicProjectionOfShadow
open RadicalMobiusShadow
open TotientTailPeriodKiller

/-! ## The two LCM implementations agree -/

/-- The recursive universal-period LCM and T4's finite-LCM definition are the
same integer.  This is the bridge between the existing diagonal completeness
theorem and the T4 channel family. -/
theorem periodLcm_eq_lcmHeight (t : ℕ) : periodLcm t = lcmHeight t := by
  apply Nat.dvd_antisymm
  · induction t with
    | zero => simp [periodLcm, lcmHeight]
    | succ t ih =>
        rw [periodLcm]
        apply Nat.lcm_dvd
        · exact ih.trans <| Finset.lcm_mono <| by
            intro n hn
            simp only [Finset.mem_Icc] at hn ⊢
            omega
        · exact Finset.dvd_lcm <| by
            simp only [Finset.mem_Icc]
            omega
  · unfold lcmHeight
    apply Finset.lcm_dvd
    intro n hn
    exact dvd_periodLcm (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2

/-! ## Actual diagonal, exact rational shadow, and foreign defect -/

/-- The actual lcm-diagonal tail difference consumed by the established
non-integrality completeness theorem. -/
noncomputable def diagonalTailDifference (t : ℕ) : ℝ :=
  totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)

/-- The canonical exact rational explicit shadow
`Q_t = H_t * numericMobiusShadow H_t`. -/
def explicitLcmShadowRat (t : ℕ) : ℚ :=
  (lcmHeight t : ℚ) * numericMobiusShadow (lcmHeight t)

/-- The reduced numerator `a_t` of the exact explicit shadow. -/
def lcmShadowNumerator (t : ℕ) : ℤ := (explicitLcmShadowRat t).num

/-- The reduced denominator `d_t` of the exact explicit shadow. -/
def lcmShadowDenominator (t : ℕ) : ℕ := (explicitLcmShadowRat t).den

/-- The real explicit shadow is exactly the cast of its canonical rational
representative.  The public real-valued API is retained for existing users. -/
noncomputable def explicitLcmShadow (t : ℕ) : ℝ :=
  (explicitLcmShadowRat t : ℝ)

theorem lcmShadowDenominator_pos (t : ℕ) : 0 < lcmShadowDenominator t := by
  exact (explicitLcmShadowRat t).den_pos

/-- `a_t / d_t` is in lowest terms by construction. -/
theorem lcmShadowNumerator_coprime_denominator (t : ℕ) :
    (lcmShadowNumerator t).natAbs.Coprime (lcmShadowDenominator t) := by
  exact (explicitLcmShadowRat t).reduced

/-- The real shadow displayed through its reduced numerator and denominator. -/
theorem explicitLcmShadow_eq_num_div_den (t : ℕ) :
    explicitLcmShadow t =
      (lcmShadowNumerator t : ℝ) / (lcmShadowDenominator t : ℝ) := by
  rw [explicitLcmShadow, lcmShadowNumerator, lcmShadowDenominator,
    Rat.cast_def]

/-- Everything in the actual diagonal not contained in the explicit finite
Möbius shadow.  This is the foreign defect, kept exact rather than assigned a
sign or asymptotic model. -/
noncomputable def foreignDiagonalDefect (t : ℕ) : ℝ :=
  diagonalTailDifference t - explicitLcmShadow t

theorem diagonalTailDifference_eq_explicit_add_foreign (t : ℕ) :
    diagonalTailDifference t =
      explicitLcmShadow t + foreignDiagonalDefect t := by
  simp [foreignDiagonalDefect]

/-! ## Full-shadow target and complement-free pincer -/

/-- Predicate that the foreign defect alone hits the exact reduced target
`-a_t / d_t` modulo the integer lattice. -/
def ForeignDiagonalDefectHitsFullTarget (t : ℕ) : Prop :=
  ∃ k : ℤ, (lcmShadowDenominator t : ℝ) * foreignDiagonalDefect t =
    (-lcmShadowNumerator t : ℝ) +
      (lcmShadowDenominator t : ℝ) * (k : ℝ)

/-! ## T4 channel target and exact hit predicate -/

/-- The canonical integer representative of T4's upper-half unit target. -/
noncomputable def lcmChannelNumerator (t p : ℕ) : ℤ :=
  ((upperHalfUnitTarget
    (lcmScale t) (lcmRadical t / p) p
    (jordanTotientTwo (lcmRadical t / p))).val : ℤ)

/-- The selected concrete T4 target is genuinely a unit for every upper-half
prime.  This prevents the pincer target from degenerating to a zero channel. -/
theorem lcmChannelTarget_isUnit
    {t p : ℕ} (ht : 5 ≤ t) (hpMem : p ∈ upperHalfPrimes t) :
    IsUnit (upperHalfUnitTarget
      (lcmScale t) (lcmRadical t / p) p
      (jordanTotientTwo (lcmRadical t / p))) := by
  have hp : p.Prime := (Finset.mem_filter.mp hpMem).2
  have hpBounds := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpMem).1
  have hp3 : 3 ≤ p := by omega
  have hupper : t < 2 * p := by omega
  have hpRad : p ∣ lcmRadical t :=
    (prime_dvd_lcmRadical_iff hp).mpr hpBounds.2
  have hquotSq : Squarefree (lcmRadical t / p) := by
    have hrSq : Squarefree (lcmRadical t) := by
      simpa [lcmRadical] using squarefreeKernel_squarefree (lcmHeight t)
    exact hrSq.squarefree_of_dvd (Nat.div_dvd_of_dvd hpRad)
  apply upperHalfUnitTarget_isUnit_of_primeFactors_le hp hp3 hupper
  · exact lcmScale_primeFactors_le t
  · exact lcmRadical_div_primeFactors_le hpRad
  · exact jordanTotientTwo_natAbs_primeFactors_le (by omega) hquotSq
      (lcmRadical_div_primeFactors_le hpRad)

/-- The Mersenne modulus of the `p`-channel. -/
def channelModulus (p : ℕ) : ℕ := mersenne p

/-- The part of the explicit shadow left after splitting off the selected
`u/(2^p-1)` channel representative.  No denominator claim about this
complement is hidden in the definition. -/
noncomputable def channelComplement (t p : ℕ) : ℝ :=
  explicitLcmShadow t -
    (lcmChannelNumerator t p : ℝ) / (channelModulus p : ℝ)

/-- The foreign defect plus the non-selected explicit fibres, rescaled by the
selected Mersenne modulus. -/
noncomputable def renormalizedDefect (t p : ℕ) : ℝ :=
  (channelModulus p : ℝ) *
    (foreignDiagonalDefect t + channelComplement t p)

/-- The additive target the residual must hit modulo the selected channel. -/
noncomputable def freshTarget (t p : ℕ) : ℤ := -lcmChannelNumerator t p

/-- Exact real-lattice formulation of a modular target hit. -/
def RenormalizedDefectHitsFreshTarget (t p : ℕ) : Prop :=
  ∃ k : ℤ, renormalizedDefect t p =
    (freshTarget t p : ℝ) + (channelModulus p : ℝ) * (k : ℝ)

/-- Predicate for a real quantity to be an integer. -/
def IsIntegralValue (x : ℝ) : Prop := x ∈ Set.range ((↑) : ℤ → ℝ)

private theorem diagonal_int_iff_hit_generic
    {D E G C : ℝ} {m : ℕ} {u : ℤ} (hm : 0 < m)
    (hD : D = E + G)
    (hE : E = (u : ℝ) / (m : ℝ) + C) :
    IsIntegralValue D ↔
      ∃ k : ℤ, (m : ℝ) * (G + C) =
        (-u : ℝ) + (m : ℝ) * (k : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hk' : D = (k : ℝ) := hk.symm
    have hres : G + C = (k : ℝ) - (u : ℝ) / (m : ℝ) := by
      calc
        G + C = (E + G) - (u : ℝ) / (m : ℝ) := by rw [hE]; ring
        _ = D - (u : ℝ) / (m : ℝ) := by rw [hD]
        _ = (k : ℝ) - (u : ℝ) / (m : ℝ) := by rw [hk']
    rw [hres]
    field_simp
    ring
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hres : G + C = -(u : ℝ) / (m : ℝ) + (k : ℝ) := by
      apply (mul_left_cancel₀ hmR)
      rw [hk]
      field_simp
    rw [hD, hE]
    calc
      (k : ℝ) = (u : ℝ) / (m : ℝ) +
          (-(u : ℝ) / (m : ℝ) + (k : ℝ)) := by
            field_simp
            ring
      _ = (u : ℝ) / (m : ℝ) + C + G := by
            rw [← hres]
            ring

/-- The primary complement-free pincer.  Integrality of the actual diagonal
is exactly a hit by `foreignDiagonalDefect` alone on the full reduced target
`-a_t / d_t` modulo `ℤ`. -/
theorem diagonal_int_iff_foreignDiagonalDefect_hits_fullTarget (t : ℕ) :
    IsIntegralValue (diagonalTailDifference t) ↔
      ForeignDiagonalDefectHitsFullTarget t := by
  unfold ForeignDiagonalDefectHitsFullTarget
  have hshadow : explicitLcmShadow t =
      (lcmShadowNumerator t : ℝ) / (lcmShadowDenominator t : ℝ) + 0 := by
    rw [explicitLcmShadow_eq_num_div_den]
    ring
  simpa only [add_zero] using
    (diagonal_int_iff_hit_generic
      (D := diagonalTailDifference t) (E := explicitLcmShadow t)
      (G := foreignDiagonalDefect t) (C := 0)
      (m := lcmShadowDenominator t) (u := lcmShadowNumerator t)
      (lcmShadowDenominator_pos t)
      (diagonalTailDifference_eq_explicit_add_foreign t) hshadow)

/-- Expanded form of the complement-free pincer, exposing the lattice witness
without an intermediate predicate. -/
theorem diagonal_int_iff_exists_fullTarget_lattice (t : ℕ) :
    IsIntegralValue (diagonalTailDifference t) ↔
      ∃ k : ℤ, (lcmShadowDenominator t : ℝ) * foreignDiagonalDefect t =
        (-lcmShadowNumerator t : ℝ) +
          (lcmShadowDenominator t : ℝ) * (k : ℝ) := by
  simpa only [ForeignDiagonalDefectHitsFullTarget] using
    diagonal_int_iff_foreignDiagonalDefect_hits_fullTarget t

theorem diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget (t : ℕ) :
    ¬IsIntegralValue (diagonalTailDifference t) ↔
      ¬ForeignDiagonalDefectHitsFullTarget t := by
  rw [diagonal_int_iff_foreignDiagonalDefect_hits_fullTarget]

/-- The load-bearing channel-hit equivalence requested by the master development.
For every prime channel, integrality of the actual diagonal is exactly a hit
of the rescaled foreign-plus-complement residual on the negative T4 target. -/
theorem diagonal_int_iff_renormalizedDefect_hits_freshTarget
    {t p : ℕ} (hp : p.Prime) :
    IsIntegralValue (diagonalTailDifference t) ↔
      RenormalizedDefectHitsFreshTarget t p := by
  unfold RenormalizedDefectHitsFreshTarget renormalizedDefect freshTarget
  simp only [Int.cast_neg]
  have hm : 0 < channelModulus p := by
    simp only [channelModulus, mersenne, Nat.sub_pos_iff_lt]
    exact Nat.one_lt_two_pow hp.ne_zero
  apply diagonal_int_iff_hit_generic
    (m := channelModulus p) (u := lcmChannelNumerator t p)
    (C := channelComplement t p) hm
    (diagonalTailDifference_eq_explicit_add_foreign t)
  simp [channelComplement]

theorem diagonal_not_int_iff_renormalizedDefect_misses_freshTarget
    {t p : ℕ} (hp : p.Prime) :
    ¬IsIntegralValue (diagonalTailDifference t) ↔
      ¬RenormalizedDefectHitsFreshTarget t p := by
  rw [diagonal_int_iff_renormalizedDefect_hits_freshTarget hp]

/-! ## A finite certificate transported to the full target -/

/-- The existing kernel-checked diagonal certificate at `t = 7` misses the
new full reduced target.  This confirms that the complement-free pincer is
connected to the established finite certificate lane. -/
theorem foreignDiagonalDefect_misses_fullTarget_seven :
    ¬ForeignDiagonalDefectHitsFullTarget 7 := by
  apply (diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget 7).mp
  change diagonalTailDifference 7 ∉ Set.range ((↑) : ℤ → ℝ)
  exact tail_diff_not_int_periodLcm_diagonal_seven_eight.1

/-! ## The primary full-target supply socket -/

/-- The complement-free analytic supply: at arbitrarily large LCM heights,
the foreign defect misses the complete reduced shadow target. -/
def FullTargetAvoidanceSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ¬ForeignDiagonalDefectHitsFullTarget t

/-- Full-target avoidance at arbitrarily large LCM heights closes the existing
diagonal non-integrality socket and hence conditionally proves #249. -/
theorem irrational_totientSeries_of_full_target_avoidance_supply
    (hsupply : FullTargetAvoidanceSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
  intro t₀
  obtain ⟨t, ht, hmiss⟩ := hsupply t₀
  refine ⟨t, ht, ?_⟩
  change ¬IsIntegralValue (diagonalTailDifference t)
  exact (diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget t).2 hmiss

/-! ## The two selected-channel supply sockets -/

/-- The development's selectable upper-half-channel avoidance supply. -/
def UpperHalfChannelAvoidanceSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ 5 ≤ t ∧
    ∃ p ∈ upperHalfPrimes t,
      ¬RenormalizedDefectHitsFreshTarget t p

/-- The minimal new-prime-scale avoidance supply, using `t=p`. -/
def FreshPrimeChannelAvoidanceSupply : Prop :=
  ∀ p₀ : ℕ, ∃ p, p₀ ≤ p ∧ 5 ≤ p ∧ p.Prime ∧
    ¬RenormalizedDefectHitsFreshTarget p p

/-- A selectable upper-half miss at arbitrarily large LCM heights closes the
existing diagonal non-integrality socket and hence conditionally proves the
totient series irrational.  The hypothesis is the unresolved analytic supply. -/
theorem irrational_totientSeries_of_upper_half_channel_avoidance_supply
    (hsupply : UpperHalfChannelAvoidanceSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
  intro t₀
  obtain ⟨t, ht, _ht5, p, hpMem, hmiss⟩ := hsupply t₀
  have hp : p.Prime := (Finset.mem_filter.mp hpMem).2
  refine ⟨t, ht, ?_⟩
  change ¬IsIntegralValue (diagonalTailDifference t)
  exact (diagonal_not_int_iff_renormalizedDefect_misses_freshTarget hp).2 hmiss

/-- The one-new-prime-scale version of the same conditional closure. -/
theorem irrational_totientSeries_of_fresh_prime_channel_avoidance_supply
    (hsupply : FreshPrimeChannelAvoidanceSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
  intro t₀
  obtain ⟨p, hp0, _hp5, hp, hmiss⟩ := hsupply t₀
  refine ⟨p, hp0, ?_⟩
  change ¬IsIntegralValue (diagonalTailDifference p)
  exact (diagonal_not_int_iff_renormalizedDefect_misses_freshTarget hp).2 hmiss

/-! Kernel boundary fixtures. -/

theorem periodLcm_eq_lcmHeight_five : periodLcm 5 = 60 := by
  rw [periodLcm_eq_lcmHeight, lcmHeight_five_fixture]

theorem channelModulus_three : channelModulus 3 = 7 := by
  norm_num [channelModulus, mersenne]

#print axioms periodLcm_eq_lcmHeight
#print axioms diagonalTailDifference_eq_explicit_add_foreign
#print axioms lcmShadowNumerator_coprime_denominator
#print axioms explicitLcmShadow_eq_num_div_den
#print axioms diagonal_int_iff_foreignDiagonalDefect_hits_fullTarget
#print axioms diagonal_int_iff_exists_fullTarget_lattice
#print axioms diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget
#print axioms lcmChannelTarget_isUnit
#print axioms diagonal_int_iff_renormalizedDefect_hits_freshTarget
#print axioms diagonal_not_int_iff_renormalizedDefect_misses_freshTarget
#print axioms foreignDiagonalDefect_misses_fullTarget_seven
#print axioms irrational_totientSeries_of_full_target_avoidance_supply
#print axioms irrational_totientSeries_of_upper_half_channel_avoidance_supply
#print axioms irrational_totientSeries_of_fresh_prime_channel_avoidance_supply
#print axioms periodLcm_eq_lcmHeight_five
#print axioms channelModulus_three

end Erdos249257.DiagonalPincerDecomposition
