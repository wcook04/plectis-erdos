import Erdos249257.TotientActualLcmTopEdgeStaircase
import Erdos249257.TotientActualLcmOrbitNonintegrality

/-! Paper-form restatements of the long #249 paper's sign-corridor,
top-edge and separation environments:

* the unconditional positive corridor `0 < R(2H+J) - R(H+J)` for `a ≥ 8`
  inside the lookahead window, with the two uniform arithmetic facts it rests
  on;
* the one-sided upper-endpoint residue gap, which already forces
  `R(2H+J) - R(H+J) ∉ ℤ`, and its cofinal form implying irrationality;
* `prop:te-chain` — five sufficient conditions, each implying irrationality,
  with the proved implications among them;
* the terminal-dominance implication, and the sufficient extension by either
  the lower-escape branch or the two-sided magnitude form;
* the unconditional separation `|Ω_a - ρ_{a,q}| < (4H + 2(2q+1) + 4)/2^{2q+2}`,
  the vanishing of that radius as `q` grows, and the separation supply
  implying irrationality.

Here `H = H(2^a) = periodLcm (2^a)`, `R_N = totientTail N`,
`Ω_a = R_{2H} - R_H`, `D(h,N,L) = windowDiscrepancy h N L`,
`δ_t(s) = diagonalWindowIncrement t s` and
`u_{a,q} = actualOddHalfCenteredLift a q`. -/

noncomputable section

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.DiagonalFreshLossBridge
open Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine

/-! ### The positive sign corridor -/

/-- **The unconditional positive corridor.**  For every `a ≥ 8` and every `J`
with `J + (a+6) < 2·2^a`, `0 < R(2H+J) - R(H+J)`; in particular `0 < Ω_a`
for every `a ≥ 8`. -/
theorem actualLcm_corridor_pos {a : ℕ} (ha : 8 ≤ a) :
    (∀ J : ℕ, J + (a + 6) < 2 * 2 ^ a →
        0 < totientTail (2 * periodLcm (2 ^ a) + J)
              - totientTail (periodLcm (2 ^ a) + J)) ∧
      0 < totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) := by
  refine ⟨fun J hJ => actualLcmTailDiff_shift_pos ha hJ, ?_⟩
  simpa [actualLcmTailOrbit, actualLcmHeight] using actualLcmTailOrbit_pos a ha

/-- The first uniform arithmetic fact behind the corridor: every arithmetic
letter inside the short window is positive. -/
theorem corridor_letter_pos {a j : ℕ} (ha : 8 ≤ a) (hj : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    0 < lcmRayArithmeticLetter (2 ^ a) j :=
  lcmRayArithmeticLetter_pos_of_lt_two_mul ha hj hjlt

/-- The second uniform arithmetic fact behind the corridor: the height is
below `8·2^a` times any such letter, with absolute constant `8`. -/
theorem corridor_height_lt_letter {a j : ℕ} (ha : 8 ≤ a) (hj : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    (periodLcm (2 ^ a) : ℤ) < 8 * (2 ^ a : ℤ) * lcmRayArithmeticLetter (2 ^ a) j :=
  periodLcm_lt_eight_mul_t_mul_lcmRayArithmeticLetter ha hj hjlt

/-! ### The one-sided upper-endpoint residue gap -/

/-- The one-sided residue gap `G_a(J,K,m)`, written out. -/
theorem topEdgeResidueGap_unfolded (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      (m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)) :=
  Iff.rfl

/-- **The one-sided gap already forces nonintegrality.**  For every `a ≥ 8`
and every `J, K, m` with `J + K + (a+6) < 2·2^a`, the gap `G_a(J,K,m)` gives
`R(2H+J) - R(H+J) ∉ ℤ`.  No lower margin is demanded. -/
theorem topEdgeResidueGap_forces_nonintegral {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a J K m) :
    totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J)
      ∉ Set.range ((↑) : ℤ → ℝ) :=
  actualLcmTailDiff_notMem_int_of_topEdgeResidueGap ha hshort hgap

/-- The same at the orbit `J = 0`. -/
theorem topEdgeResidueGap_orbit_nonintegral {a K m : ℕ} (ha : 8 ≤ a)
    (hshort : K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a 0 K m) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      ∉ Set.range ((↑) : ℤ → ℝ) := by
  simpa [actualLcmTailOrbit, actualLcmHeight] using
    actualLcmTailOrbit_notMem_int_of_topEdgeResidueGap ha hshort hgap

/-- **The cofinal upper-endpoint condition implies irrationality.** -/
theorem irrational_of_topEdgeResidueGapSupply
    (hsupply : PowerTwoActualLcmTopEdgeResidueGapSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_topEdgeResidueGapSupply hsupply

/-! ### `prop:te-chain` — five sufficient conditions -/

/-- Item 1, written out: a two-sided band on the adjacent-suffix residue. -/
theorem teChain_item_one_unfolded :
    PowerTwoAdjacentSuffixMidbandSupply ↔
      ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        m + 1 + (a + 6) < 2 * 2 ^ a ∧
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
          diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) :=
  Iff.rfl

/-- Item 2, written out: at the odd guarded depth `2q+1`, a two-sided band of
half-width `H+q+2` on the half-word residue modulo `4^q`. -/
theorem teChain_item_two_unfolded :
    PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
          powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
        powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
          (4 : ℤ) ^ q - ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) :=
  Iff.rfl

/-- Item 3, written out: `H + q + 2 ≤ |u_{a,q}|` at the prescribed depth. -/
theorem teChain_item_three_unfolded :
    PowerTwoActualFinalTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q| :=
  Iff.rfl

/-- Item 4, written out: the same magnitude bound at any odd depth `2q+1`
satisfying the half-cell fit and the sign-corridor room. -/
theorem teChain_item_four_unfolded :
    PowerTwoFlexibleActualTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q| :=
  Iff.rfl

/-- Item 5, written out: `δ_{2^a}(2q+2) ≤ 2 u_{a,q}` under the same bounds. -/
theorem teChain_item_five_unfolded :
    PowerTwoFlexibleActualTerminalDominanceSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
          2 * actualOddHalfCenteredLift a q :=
  Iff.rfl

/-- **Each of the five conditions suffices for irrationality.** -/
theorem teChain_five_sufficient_for_irrationality :
    (PowerTwoAdjacentSuffixMidbandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :=
  ⟨irrational_totientSeries_of_adjacentSuffixMidbandSupply,
    irrational_totientSeries_of_oddGuardTopEdgeHalfWordBandSupply,
    irrational_totientSeries_of_actualFinalTopEdgeMagnitudeSupply,
    irrational_totientSeries_of_flexibleActualTopEdgeMagnitudeSupply,
    irrational_totientSeries_of_flexibleActualTerminalDominanceSupply⟩

/-- **The first four imply the upper-endpoint condition.** -/
theorem teChain_first_four_imply_topEdgeSupply :
    (PowerTwoAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) := by
  refine ⟨powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband,
    fun h => powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband
      (powerTwoAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand h),
    fun h => powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband
      (powerTwoAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand
        (topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply.mpr h)),
    fun h => powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband
      (powerTwoAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude h)⟩

/-- **The fifth gives nonintegrality directly by the endpoint identity.** -/
theorem teChain_fifth_gives_nonintegrality :
    PowerTwoFlexibleActualTerminalDominanceSupply →
      PowerTwoActualLcmOrbitNonintegralitySupply :=
  actualLcmOrbitNonintegralitySupply_of_flexibleActualTerminalDominance

/-- **The proved implications among the conditions.**  They are not a linear
hierarchy: the half-word band and the final magnitude are equivalent, both
the half-word band and the flexible magnitude reach the midband, and the
final magnitude also specialises to the flexible magnitude. -/
theorem teChain_relations :
    (PowerTwoAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PowerTwoAdjacentSuffixMidbandSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoAdjacentSuffixMidbandSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply) :=
  ⟨powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband,
    powerTwoAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand,
    topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply,
    powerTwoAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude,
    flexibleActualTopEdgeMagnitudeSupply_of_actualFinal⟩

/-! ### Terminal dominance -/

/-- **The dominance hypothesis at a single odd rank excludes integrality of
`Ω_a`.** -/
theorem terminalDominance_orbit_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hdom : diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
      2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      ∉ Set.range ((↑) : ℤ → ℝ) := by
  simpa [actualLcmTailOrbit, actualLcmHeight] using
    actualLcmTailOrbit_notMem_int_of_actualTerminalDominance ha hshort hfit hdom

/-- **The supply predicate composes to `S ∉ ℚ`.** -/
theorem irrational_of_terminalDominanceSupply
    (hsupply : PowerTwoFlexibleActualTerminalDominanceSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_flexibleActualTerminalDominanceSupply hsupply

/-! ### The sufficient extension: either branch -/

/-- **Branch (i): the lower-escape branch cofinally suffices.** -/
theorem irrational_of_lower_escape_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
      2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
      2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
      2 * actualOddHalfCenteredLift a q ≤
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
          ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totientSeries_of_flexibleActualTerminalCarryCorridorEscapeSupply ?_
  intro a₀
  obtain ⟨a, q, h1, h2, h3, h4, h5⟩ := hsupply a₀
  exact ⟨a, q, h1, h2, h3, h4, Or.inl h5⟩

/-- **Branch (ii): the two-sided magnitude form implies corridor escape, and
hence irrationality.**  It asks only `H + q + 2 ≤ |u_{a,q}|`, with no sign
prescribed for the centred representative. -/
theorem corridor_escape_and_irrational_of_magnitude :
    (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :=
  ⟨flexibleActualTerminalCarryCorridorEscapeSupply_of_magnitude,
    irrational_totientSeries_of_flexibleActualTerminalCarryCorridorEscapeSupply,
    irrational_totientSeries_of_flexibleActualTopEdgeMagnitudeSupply⟩

/-! ### Separation of the rational approximation -/

/-- `2^(2q+1) = 2·4^q`. -/
theorem two_pow_odd_eq (q : ℕ) : (2 : ℝ) ^ (2 * q + 1) = 2 * (4 : ℝ) ^ q := by
  induction q with
  | zero => norm_num
  | succ n ih =>
    have hexp : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [hexp, pow_add, ih, pow_succ]
    ring

/-- **The unconditional separation bound.**  For every `a` and `q`,
`|Ω_a - ρ_{a,q}| < (4H + 2(2q+1) + 4)/2^{2q+2}`. -/
theorem abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form (a q : ℕ) :
    |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)))
        - actualLcmRawApprox a q|
      < (4 * (periodLcm (2 ^ a) : ℝ) + 2 * (2 * (q : ℝ) + 1) + 4) / 2 ^ (2 * q + 2) := by
  have h := abs_actualLcmTailOrbit_sub_rawApprox_lt a q
  have hrad : actualLcmRawErrorRadius a q
      = (4 * (periodLcm (2 ^ a) : ℝ) + 2 * (2 * (q : ℝ) + 1) + 4) / 2 ^ (2 * q + 2) := by
    unfold actualLcmRawErrorRadius actualLcmHeight
    have hp : (2 : ℝ) ^ (2 * q + 2) = 2 ^ (2 * q + 1) * 2 := by
      rw [show 2 * q + 2 = (2 * q + 1) + 1 from by omega, pow_succ]
    rw [hp]
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [← hrad]
  simpa [actualLcmTailOrbit, actualLcmHeight] using h

/-- **The error radius tends to zero as the depth grows, for fixed `a`.** -/
theorem actualLcmRawErrorRadius_tendsto_zero (a : ℕ) :
    Filter.Tendsto (fun q : ℕ => actualLcmRawErrorRadius a q) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun q : ℕ => ((1 : ℝ) / 4) ^ q) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 : Filter.Tendsto (fun q : ℕ => (q : ℝ) * ((1 : ℝ) / 4) ^ q)
      Filter.atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have h3 := (h1.const_mul (((2 * actualLcmHeight a + 3 : ℕ) : ℝ) / 2)).add h2
  rw [mul_zero, add_zero] at h3
  refine h3.congr fun q => ?_
  unfold actualLcmRawErrorRadius
  rw [two_pow_odd_eq q, div_pow, one_pow]
  push_cast
  have h4 : (4 : ℝ) ^ q ≠ 0 := by positivity
  field_simp
  try ring

/-- **`ρ_{a,q}` is an explicit finite rational block.** -/
theorem actualLcmRawApprox_isRat (a q : ℕ) :
    ∃ v : ℚ, actualLcmRawApprox a q = (v : ℝ) :=
  ⟨(diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) : ℚ) / 2 ^ (2 * q + 1), by
    unfold actualLcmRawApprox
    push_cast
    try ring⟩

/-- **The separation supply implies irrationality of `S`.** -/
theorem irrational_of_actualLcmOrbitSeparationSupply
    (hsupply : PowerTwoActualLcmOrbitSeparationSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_actualLcmOrbitSeparationSupply hsupply

end ErdosProblems.Erdos249.PaperCompleteR21

end

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.actualLcm_corridor_pos
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.corridor_letter_pos
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.corridor_height_lt_letter
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_forces_nonintegral
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_orbit_nonintegral
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_topEdgeResidueGapSupply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_one_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_two_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_three_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_four_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_five_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_five_sufficient_for_irrationality
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_first_four_imply_topEdgeSupply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_fifth_gives_nonintegrality
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.teChain_relations
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.terminalDominance_orbit_nonintegral
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_terminalDominanceSupply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_lower_escape_supply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.corridor_escape_and_irrational_of_magnitude
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.two_pow_odd_eq
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.actualLcmRawErrorRadius_tendsto_zero
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.actualLcmRawApprox_isRat
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_actualLcmOrbitSeparationSupply
