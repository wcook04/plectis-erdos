import Erdos249257.HalfDivisorUnitDrop
import Erdos249257.RewindSeamOperationalBridge

/-!
# Half-divisor boundary pair to operational rewind seam

This module isolates the exact remaining object-level identification: the two
adjacent rewind ancestors restrict to opposite terminal extensions of one
common half-depth parent. That identification supplies the unit coefficient
drop required by the operational seam consumer.
-/

namespace Erdos249257.RewindHalfDivisorAdapter

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.FixedCoeffRewind
open Erdos249257.HalfDivisorUnitDrop
open Erdos249257.RewindSeamOperationalBridge

/-- Restricting a depth-`M` word through the half divisor `K+1` preserves its
coefficient at row `2(K+1)`, provided `M` is still below that row. Every
proper divisor of `2(K+1)` is at most `K+1`; the only larger divisor is the
row itself, which is absent from both finite words. -/
theorem supportCoeff_eq_of_restriction_at_halfDivisor
    {K M : ℕ} (hKM : K + 1 ≤ M) (hMlt : M < 2 * (K + 1))
    (w : HalfWord M) (b : HalfWord (K + 1))
    (hrestrict : restrictWord hKM w = b) :
    supportCoeff (wordSupport w) (2 * (K + 1)) =
      supportCoeff (wordSupport b) (2 * (K + 1)) := by
  apply supportCoeff_eq_of_divisorAgreement
  intro e hediv
  by_cases heK : e ≤ K + 1
  · have hset := congrArg wordSupport hrestrict
    rw [wordSupport_restrictWord] at hset
    have hmem :
        e ∈ wordSupport w ∩ Set.Iic (K + 1) ↔ e ∈ wordSupport b := by
      rw [hset]
    simpa [heK] using hmem
  · have hwAbsent : e ∉ wordSupport w := by
      intro hew
      rcases hew with ⟨helt, -⟩
      have heM : e ≤ M := Nat.le_of_lt_succ helt
      have hdvd : e ∣ 2 * (K + 1) := Nat.dvd_of_mem_divisors hediv
      obtain ⟨q, hq⟩ := hdvd
      have hq0 : q ≠ 0 := by
        intro hzero
        subst q
        simp at hq
      have hq1 : q ≠ 1 := by
        intro hone
        subst q
        simp at hq
        omega
      have hq2 : 2 ≤ q := by omega
      have hmul : e * 2 ≤ 2 * (K + 1) := by
        rw [hq]
        exact Nat.mul_le_mul_left e hq2
      exact heK (by omega)
    have hbAbsent : e ∉ wordSupport b := by
      intro heb
      rcases heb with ⟨helt, -⟩
      exact heK (by omega)
    simp [hwAbsent, hbAbsent]

/-- The two adjacent rewind ancestors may live at any base depth `M` between
the half divisor `K+1` and the produced row. Their restrictions through
`K+1` are the two opposite terminal children of one common depth-`K` word.
The proof witnesses also certify that both indices lie in the base window. -/
def RewindBaseHalfDivisorBoundaryPairAt
    {K M R₀ : ℕ} (W₀ : SelectedHalfWindow M R₀)
    (hKM : K + 1 ≤ M) (cs : List ℕ) (a : HalfWord K) : Prop :=
  ∃ (hleftPos : 1 ≤ rewind cs 1)
      (hleftBound : rewind cs 1 ≤ R₀)
      (hrightPos : 1 ≤ rewind cs 1 + 1)
      (hrightBound : rewind cs 1 + 1 ≤ R₀),
    restrictWord hKM (W₀.word (rewind cs 1) hleftPos hleftBound) =
        extendHalfWord a true ∧
      restrictWord hKM
          (W₀.word (rewind cs 1 + 1) hrightPos hrightBound) =
        extendHalfWord a false

/-- A literal half-divisor boundary pair supplies exactly the operational
unit-drop profile at the doubled row inspected by that half divisor. -/
theorem rewindBaseUnitDropAt_of_halfDivisorBoundaryPair
    {K M R₀ : ℕ} (W₀ : SelectedHalfWindow M R₀)
    (hKM : K + 1 ≤ M) (hMlt : M < 2 * (K + 1))
    (cs : List ℕ) (a : HalfWord K)
    (hpair : RewindBaseHalfDivisorBoundaryPairAt W₀ hKM cs a) :
    RewindBaseUnitDropAt W₀ (2 * (K + 1)) cs
      (supportCoeff (wordSupport (extendHalfWord a false)) (2 * (K + 1))) := by
  rcases hpair with
    ⟨hleftPos, hleftBound, hrightPos, hrightBound, hleft, hright⟩
  intro r hr hrR
  constructor
  · intro hreql
    have hrestrict :
        restrictWord hKM (W₀.word r hr hrR) = extendHalfWord a true := by
      rw [W₀.word_eq_of_index_eq hreql hr hrR hleftPos hleftBound]
      exact hleft
    calc
      supportCoeff (wordSupport (W₀.word r hr hrR)) (2 * (K + 1)) =
          supportCoeff (wordSupport (extendHalfWord a true)) (2 * (K + 1)) :=
        supportCoeff_eq_of_restriction_at_halfDivisor
          hKM hMlt (W₀.word r hr hrR) (extendHalfWord a true) hrestrict
      _ = supportCoeff (wordSupport (extendHalfWord a false)) (2 * (K + 1)) + 1 :=
        supportCoeff_extend_true_eq_false_add_one_at_double a
  · intro hreqr
    have hrestrict :
        restrictWord hKM (W₀.word r hr hrR) = extendHalfWord a false := by
      rw [W₀.word_eq_of_index_eq hreqr hr hrR hrightPos hrightBound]
      exact hright
    exact supportCoeff_eq_of_restriction_at_halfDivisor
      hKM hMlt (W₀.word r hr hrR) (extendHalfWord a false) hrestrict

/-- Full operational fan-in. If the produced row is exactly twice the marked
half divisor, the boundary pair discharges the only extra semantic hypothesis
of the rewind-seam realization theorem. -/
theorem protectedEvenSeamRealizedAt_succ_of_rewindHalfDivisorBoundaryPair
    {K M N R₀ R S : ℕ}
    (W₀ : SelectedHalfWindow M R₀) (W : SelectedHalfWindow N R)
    (hKM : K + 1 ≤ M) (hMlt : M < 2 * (K + 1))
    (hMN : M ≤ N) (hhalf : (N + 1) / 2 ≤ M)
    (hrow : N + 1 = 2 * (K + 1)) (cs : List ℕ) (a : HalfWord K)
    (hN : 1 ≤ N) (hwidth : R ≤ denom cs)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs)
    (hseam : IsSeamPair cs R)
    (hSstrip : S ≤ halfStripBound (N + 1)) (h27 : 27 ≤ S)
    (hbuffer :
      S +
          (supportCoeff (wordSupport (extendHalfWord a false)) (N + 1) + 1) ≤
        2 * R)
    (hpair : RewindBaseHalfDivisorBoundaryPairAt W₀ hKM cs a) :
    ProtectedEvenSeamRealizedAt (N + 1) (seamCut cs : ℤ)
      (supportCoeff (wordSupport (extendHalfWord a false)) (N + 1) : ℤ) := by
  let c := supportCoeff (wordSupport (extendHalfWord a false)) (N + 1)
  apply protectedEvenSeamRealizedAt_succ_of_rewindSeam
    W₀ W hMN hhalf cs hN hwidth hprov hseam hSstrip h27
      (c := c) hbuffer
  simpa [c, hrow] using
    (rewindBaseUnitDropAt_of_halfDivisorBoundaryPair
      W₀ hKM hMlt cs a hpair)

/-- Full-strip specialization. The existing divisor envelope supplies the
buffer once the literal half-divisor boundary pair is identified. -/
theorem protectedEvenSeamRealizedAt_succ_of_fullStrip_rewindHalfDivisorBoundaryPair
    {K M N R₀ : ℕ}
    (W₀ : SelectedHalfWindow M R₀)
    (W : SelectedHalfWindow N (halfStripBound N))
    (hKM : K + 1 ≤ M) (hMlt : M < 2 * (K + 1))
    (hMN : M ≤ N) (hhalf : (N + 1) / 2 ≤ M)
    (hrow : N + 1 = 2 * (K + 1)) (cs : List ℕ) (a : HalfWord K)
    (hN : 1 ≤ N) (hwidth : halfStripBound N ≤ denom cs)
    (hprov : W.HasRewindRestrictionAt W₀ hMN cs)
    (hseam : IsSeamPair cs (halfStripBound N))
    (h27 : 27 ≤ halfStripBound (N + 1))
    (hpair : RewindBaseHalfDivisorBoundaryPairAt W₀ hKM cs a) :
    ProtectedEvenSeamRealizedAt (N + 1) (seamCut cs : ℤ)
      (supportCoeff (wordSupport (extendHalfWord a false)) (N + 1) : ℤ) := by
  let c := supportCoeff (wordSupport (extendHalfWord a false)) (N + 1)
  apply protectedEvenSeamRealizedAt_succ_of_fullStrip_rewindSeam
    W₀ W hMN hhalf cs hN hwidth hprov hseam h27 (c := c)
  simpa [c, hrow] using
    (rewindBaseUnitDropAt_of_halfDivisorBoundaryPair
      W₀ hKM hMlt cs a hpair)

#print axioms supportCoeff_eq_of_restriction_at_halfDivisor
#print axioms rewindBaseUnitDropAt_of_halfDivisorBoundaryPair
#print axioms protectedEvenSeamRealizedAt_succ_of_rewindHalfDivisorBoundaryPair
#print axioms protectedEvenSeamRealizedAt_succ_of_fullStrip_rewindHalfDivisorBoundaryPair

end Erdos249257.RewindHalfDivisorAdapter
