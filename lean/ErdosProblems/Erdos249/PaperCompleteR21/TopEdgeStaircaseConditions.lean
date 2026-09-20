import Erdos249257.TotientActualLcmTopEdgeStaircase
import Erdos249257.TotientActualLcmOrbitNonintegrality

/-! Paper-form restatements of the long paper's top-edge staircase
environments:

* `prop:TE-04` — the finite condition `G_a(J,K,m)` implies
  `R_{2H+J} - R_{H+J} ∉ ℤ`, and its cofinal `J = 0` form implies
  irrationality;
* `prop:TE-05` — the proved implications among the five sufficient
  conditions, which do not form a single linear chain;
* `prop:TE-06` — the exact endpoint identity
  `2u_{a,q} = δ_{2^a}(2q+2) - c_{H,H,z}(2q+1)` under integrality, and the two
  inequalities each sufficient for `Ω_a ∉ ℤ`.

Here `H(t) = periodLcm t`, `R_N = totientTail N`, `D(h,N,L) =
windowDiscrepancy h N L`, `δ_t(s) = diagonalWindowIncrement t s`,
`c_{h,N,z} = carryOrbit h N z` and `u_{a,q} = actualOddHalfCenteredLift a q`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.DiagonalFreshLossBridge
open Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine

/-! ### `prop:TE-04` — a sufficient upper-endpoint separation -/

/-- The finite condition `G_a(J,K,m)` written out. -/
theorem upper_endpoint_condition_iff (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      (m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)) :=
  Iff.rfl

/-- **`G_a(J,K,m)` implies `R_{2H+J} - R_{H+J} ∉ ℤ`.** -/
theorem upper_endpoint_gap_nonintegral {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a J K m) :
    totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J) ∉
      Set.range ((↑) : ℤ → ℝ) :=
  actualLcmTailDiff_notMem_int_of_topEdgeResidueGap ha hshort hgap

/-- **The sign theorem forces an integral tail to give a residue in the upper
endpoint interval.**  If `R_{2H+J} - R_{H+J}` is the integer `d` and the
modulus is large enough, then `D(H,H+J,K) mod 2^K` lies in
`(2^K - (2H+J+K+2), 2^K)` — exactly the interval the one-sided test
excludes. -/
theorem integral_tail_forces_upper_endpoint_residue {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hroom : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ K)
    {d : ℤ}
    (hd : (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J)) :
    (2 : ℤ) ^ K - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ K ∧
      windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ K <
        (2 : ℤ) ^ K := by
  obtain ⟨-, hlow, hhigh⟩ :=
    actualLcm_integral_forces_topEdgeResidue ha hshort hd hroom
  exact ⟨hlow, hhigh⟩

/-- **In particular irrationality follows** if for every `a₀` there are
`a ≥ max(a₀, 8)` and `K, m` with `K + (a+6) < 2·2^a` and `G_a(0,K,m)`. -/
theorem irrational_of_upper_endpoint_gap_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a K m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
      K + (a + 6) < 2 * 2 ^ a ∧ ActualLcmTopEdgeResidueGap a 0 K m) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_topEdgeResidueGapSupply hsupply

/-! ### `prop:TE-05` — relations among the sufficient conditions -/

/-- **The proved implications.**  The guarded odd-prefix band and the guarded
centred-magnitude bound are equivalent; the guarded bound implies the flexible
one; the flexible bound implies the adjacent-suffix band, which implies the
upper-endpoint test.  Separately, terminal dominance and the flexible centred
magnitude each imply the two-sided exclusion of `prop:TE-06`, which implies
diagonal nonintegrality. -/
theorem te_chain_relations :
    (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoAdjacentSuffixMidbandSupply) ∧
      (PowerTwoAdjacentSuffixMidbandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply →
        PowerTwoActualLcmOrbitNonintegralitySupply) :=
  ⟨topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply,
    flexibleActualTopEdgeMagnitudeSupply_of_actualFinal,
    powerTwoAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude,
    powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband,
    flexibleActualTerminalCarryCorridorEscapeSupply_of_dominance,
    flexibleActualTerminalCarryCorridorEscapeSupply_of_magnitude,
    actualLcmOrbitNonintegralitySupply_of_flexibleActualTerminalCarryCorridorEscape⟩

/-! ### `prop:TE-06` — an exact endpoint formula -/

/-- Every centred lift lies in the half-open cell `(-M/2, M/2]`. -/
theorem centeredLift_range {A M : ℤ} (hM : 0 < M) :
    -M < 2 * actualCenteredLift A M ∧ 2 * actualCenteredLift A M ≤ M := by
  have hr0 : 0 ≤ A % M := Int.emod_nonneg A hM.ne'
  have hrM : A % M < M := Int.emod_lt_of_pos A hM
  simp only [actualCenteredLift]
  split_ifs with hhalf <;> omega

/-- `u_{a,q}` is exactly the paper's centred integer representative of
`(D(H,H,2q+1) + δ_{2^a}(2q+2))/2` modulo `4^q`: the numerator is even, the
lift is congruent to its half, and it lies in `(-4^q/2, 4^q/2]`. -/
theorem oddHalfCenteredLift_spec {a : ℕ} (q : ℕ) (ha : 2 ≤ a) :
    Even (windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
        diagonalWindowIncrement (2 ^ a) (2 * q + 2)) ∧
      Int.ModEq ((4 : ℤ) ^ q) (actualOddHalfCenteredLift a q)
        ((windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
          diagonalWindowIncrement (2 ^ a) (2 * q + 2)) / 2) ∧
      -((4 : ℤ) ^ q) < 2 * actualOddHalfCenteredLift a q ∧
      2 * actualOddHalfCenteredLift a q ≤ (4 : ℤ) ^ q := by
  have hraw :
      diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) =
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
          diagonalWindowIncrement (2 ^ a) (2 * q + 2) := by
    rw [diagonalAdjacentSuffixRawBlock_eq_windowDiscrepancy_add_terminal]
  have hpos : (0 : ℤ) < (4 : ℤ) ^ q := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hraw]
    exact diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_even ha
  · rw [actualOddHalfCenteredLift, hraw]
    exact actualCenteredLift_modEq _ _
  · exact (centeredLift_range (A := diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2)
      hpos).1
  · exact (centeredLift_range (A := diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2)
      hpos).2

/-- **An exact endpoint formula.**  If `z ∈ ℤ` and `z = Ω_a`, then
`2u_{a,q} = δ_{2^a}(2q+2) - c_{H,H,z}(2q+1)`. -/
theorem endpoint_identity {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    {z : ℤ}
    (hz : (z : ℝ) = totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) :
    2 * actualOddHalfCenteredLift a q =
      diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
        carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) := by
  have h := two_mul_actualOddHalfCenteredLift_eq_terminal_sub_trueCarry
    (a := a) (q := q) ha (by omega) hfit (z := z) hz
  rw [show 2 * q + 1 + 1 = 2 * q + 2 from by ring] at h
  exact h

/-- **The estimate that makes the identity decisive.**  Under integrality the
recurrence equals a positive tail difference strictly smaller than
`2H + 2q + 3`: `0 < c_{H,H,z}(2q+1) < 2H + 2q + 3`. -/
theorem integral_carry_strictly_between {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    {z : ℤ}
    (hz : (z : ℝ) = totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) :
    0 < carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) ∧
      carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) <
        ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ) := by
  have hz' : (z : ℝ) =
      totientTail (periodLcm (2 ^ a) + periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) := by
    rw [hz, two_mul]
  have htrack := carryOrbit_eq_tail_diff hz' (2 * q + 1)
  have hpos := actualLcmTailDiff_shift_pos (a := a) (J := 2 * q + 1) ha (by omega)
  have hupper :=
    (tail_diff_directed_bounds (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + (2 * q + 1))).2
  rw [← htrack] at hupper
  constructor
  · have hR : (0 : ℝ) <
        (carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) : ℝ) := by
      rw [htrack, show periodLcm (2 ^ a) + (2 * q + 1) + periodLcm (2 ^ a)
        = 2 * periodLcm (2 ^ a) + (2 * q + 1) from by omega]
      exact hpos
    exact_mod_cast hR
  · have hR : (carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) : ℝ) <
        ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) := by
      push_cast at hupper ⊢
      linarith
    exact_mod_cast hR

/-- **Either inequality is sufficient for `Ω_a ∉ ℤ`.** -/
theorem endpoint_criterion_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hesc : 2 * actualOddHalfCenteredLift a q ≤
          diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
            ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ) ∨
        diagonalWindowIncrement (2 ^ a) (2 * q + 2) ≤
          2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) ∉
      Set.range ((↑) : ℤ → ℝ) := by
  have hcast : ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ) =
      ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ) := by push_cast; ring
  have hesc' : 2 * actualOddHalfCenteredLift a q ≤
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
          ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ) ∨
      diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
        2 * actualOddHalfCenteredLift a q := by
    rw [show 2 * q + 1 + 1 = 2 * q + 2 from by ring, hcast]
    exact hesc
  exact actualLcmTailOrbit_notMem_int_of_actualTerminalCarryCorridorEscape
    ha (by omega) hfit hesc'

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.upper_endpoint_condition_iff
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.upper_endpoint_gap_nonintegral
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.integral_tail_forces_upper_endpoint_residue
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.integral_carry_strictly_between
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_upper_endpoint_gap_supply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.te_chain_relations
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.centeredLift_range
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.oddHalfCenteredLift_spec
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.endpoint_identity
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.endpoint_criterion_nonintegral
