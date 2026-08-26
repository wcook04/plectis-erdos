import Erdos249257.BooleanMobiusExactRowSeed
import Erdos249257.BooleanMobiusExactRowDoubling
import Erdos249257.BooleanMobiusExactRowCrossing
import Erdos249257.BooleanMobiusExactTransition
import Erdos249257.BooleanMobiusSkippedCoreCriticalCapacity
import Erdos249257.HalfCylinderFiniteShadow

/-!
# Cofinal exact rows from critical skipped-core capacity

This module packages the protected-core induction behind the sharp
skipped-core capacity route.  It proves that one explicit arithmetic supply
condition is sufficient for cofinally many exact Boolean--Möbius rows.  The
supply condition itself remains an assumption here; consequently the final
membership theorem in this file is a conditional reduction, not an
unconditional proof of Erdős problem 257.
-/

namespace Erdos249257

open HalfCarryReachability HalfCylinderFiniteShadow

/-- The remaining arithmetic socket in the protected-core construction.
Whenever a below-half core is crossed by rank `c`, adjoining `c` must already
reach the integral half target at endpoint `2c-2`.

By `localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff`, this is exactly
the sharp `c-2`-bit capacity needed by the strict-upper skipped-core fill.
The deficit hypothesis records that `c` is a genuine crossing rank. -/
def SkippedCoreCriticalQuotientSupply : Prop :=
  ∀ (D : Finset ℕ) (c : ℕ),
    4 ≤ c →
    (∀ d ∈ D, 2 ≤ d ∧ d < c) →
    localMersennePrefixValue D < (1 / 2 : ℚ) →
    (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient (insert c D) (2 * c - 2)

/-! ## The crossing core is the canonical half-greedy prefix -/

/-- A below-half core whose deficit is smaller than the next Mersenne weight
is forced to be the canonical half-greedy prefix through rank `c - 1`.

Indeed, after casting to `ℝ` the core is a half-straddling word at depth
`c - 1`: its value is below one half, while the full unresolved tail is at
least the crossing weight `w_c`.  Strict superincreasingness, packaged by
`IsStraddlePrefix.half_agrees_greedy`, fixes every bit of the word; the
primitive-prefix bridge then identifies those bits with the exact rational
greedy prefix. -/
theorem eq_halfGreedyPrefixSupport_of_critical_crossing
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    D = halfGreedyPrefixSupport (c - 1) := by
  classical
  have hvalue :
      positiveMersenneSupportValue (↑D : Set ℕ) =
        ((localMersennePrefixValue D : ℚ) : ℝ) := by
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum,
      localMersennePrefixValue_eq_finiteErdosSum]
  have hbelowR :
      ((localMersennePrefixValue D : ℚ) : ℝ) < (1 / 2 : ℝ) := by
    simpa using (Rat.cast_lt (K := ℝ)).2 hbelow
  have hcrossCast :
      ((((1 / 2 : ℚ) - localMersennePrefixValue D : ℚ)) : ℝ) <
        ((mersenneWeightRat c : ℚ) : ℝ) := by
    exact_mod_cast hcross
  have hcrossR :
      (1 / 2 : ℝ) - ((localMersennePrefixValue D : ℚ) : ℝ) <
        mersenneWeight c := by
    simpa using hcrossCast
  have htail : mersenneWeight c ≤ mersenneTail (c - 1) := by
    have hrec := mersenneTail_eq_weight_add (c - 1)
    have hidx : c - 1 + 1 = c := by omega
    rw [hidx] at hrec
    rw [hrec]
    exact le_add_of_nonneg_right (mersenneTail_nonneg c)
  have hstraddle : IsStraddlePrefix (1 / 2 : ℝ) D (c - 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro d hd
      have hdData := hD d hd
      exact ⟨by omega, by omega⟩
    · rw [hvalue]
      exact hbelowR.le
    · rw [hvalue]
      linarith
  have hagree := hstraddle.half_agrees_greedy
  have hDprefix :
      (↑D : Set ℕ) =
        primitivePrefix (greedyMersenneSupport (1 / 2 : ℝ)) (c - 1) := by
    ext d
    simp only [primitivePrefix, Set.mem_inter_iff, Set.mem_Iic,
      Finset.mem_coe]
    constructor
    · intro hd
      have hdData := hD d hd
      exact ⟨(hagree d (by omega) (by omega)).mp hd, by omega⟩
    · rintro ⟨hdGreedy, hdLe⟩
      have hdPos : 0 < d := by
        by_contra hnot
        have hdZero : d = 0 := by omega
        subst d
        exact (zero_not_mem_greedyMersenneSupport (1 / 2 : ℝ)) hdGreedy
      exact (hagree d hdPos hdLe).mpr hdGreedy
  have hgreedyPrefix :
      primitivePrefix (greedyMersenneSupport (1 / 2 : ℝ)) (c - 1) =
        (↑(halfGreedyPrefixSupport (c - 1)) : Set ℕ) := by
    simpa [halfGreedyPrefixSupport] using
      (primitivePrefix_greedyMersenneSupport_eq_prefixRat
        (1 / 2 : ℚ) (c - 1))
  apply Finset.ext
  intro d
  simpa using Set.ext_iff.mp (hDprefix.trans hgreedyPrefix) d

/-- Every rank in the canonical half-greedy prefix through `c - 1` lies in
the admissible skipped-core range `[2,c)`. -/
theorem halfGreedyPrefixSupport_bounds_before
    {c : ℕ} (hc : 4 ≤ c) :
    ∀ d ∈ halfGreedyPrefixSupport (c - 1), 2 ≤ d ∧ d < c := by
  classical
  intro d hd
  have hdOne : d ≠ 1 := by
    intro hdEq
    subst d
    exact one_not_mem_halfGreedyPrefixSupport (c - 1) hd
  unfold halfGreedyPrefixSupport greedyMersennePrefixRat at hd
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
  have hkLt := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  constructor <;> omega

/-- Every finite rational half-greedy prefix is strictly below one half.
Nonnegativity of the greedy remainder gives the weak inequality; equality is
excluded because a finite positive Mersenne sum has odd reduced denominator,
whereas one half has denominator two. -/
theorem localMersennePrefixValue_halfGreedy_lt_half (n : ℕ) :
    localMersennePrefixValue (halfGreedyPrefixSupport n) <
      (1 / 2 : ℚ) := by
  have hle :
      localMersennePrefixValue (halfGreedyPrefixSupport n) ≤
        (1 / 2 : ℚ) := by
    simpa [halfGreedyPrefixRat, halfGreedyPrefixSupport] using
      halfGreedyPrefixRat_le_half n
  apply lt_of_le_of_ne hle
  intro heq
  have heq' :
      localMersennePrefixValue (halfGreedyPrefixSupport n) =
        (1 / 2 : ℚ) := heq
  have hzero : 0 ∉ halfGreedyPrefixSupport n := by
    simp [halfGreedyPrefixSupport]
  have hodd := finiteErdosSum_den_odd
    (halfGreedyPrefixSupport n) hzero
  rw [← localMersennePrefixValue_eq_finiteErdosSum, heq'] at hodd
  obtain ⟨k, hk⟩ := hodd
  norm_num at hk
  omega

/-- The canonical form of the critical quotient socket.  The arbitrary
finite core has disappeared: only the actual half-greedy prefix at the
crossing rank remains. -/
def HalfGreedyCriticalQuotientSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    localMersennePrefixValue (halfGreedyPrefixSupport (c - 1)) <
      (1 / 2 : ℚ) →
    (1 / 2 : ℚ) -
        localMersennePrefixValue (halfGreedyPrefixSupport (c - 1)) <
      mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient
        (insert c (halfGreedyPrefixSupport (c - 1))) (2 * c - 2)

/-- The minimal actual-orbit form of the socket: the quotient lower bound is
required only when rank `c` is genuinely skipped by the rational half-greedy
orbit. -/
def HalfGreedySkippedCriticalQuotientSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient
        (insert c (halfGreedyPrefixSupport (c - 1))) (2 * c - 2)

/-- A one-row-earlier form of the actual skipped-rank socket.  At endpoint
`2c-3` the relevant binary suffix has half the critical capacity. -/
def HalfGreedySkippedPrecriticalSuffixSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)

/-- The genuinely residual part of the predecessor supply: only a skipped
rank immediately before an actual take is exposed.  Consecutive skipped
ranks admit a uniform finite-lookahead proof below. -/
def HalfGreedyPreTakePrecriticalSuffixSupply : Prop :=
  ∀ c : ℕ,
    6 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    mersenneWeightRat (c + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) c →
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)

/-! ## Carry form of the predecessor-endpoint socket -/

/-- A below-half finite support has integral quotient below the endpoint
target.  This is the admissibility needed to identify the natural-valued
binary suffix with the signed endpoint defect. -/
theorem localPrefixQuotient_le_halfEndpointTarget_of_value_below
    {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M)
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localPrefixQuotient D M ≤ halfEndpointTarget M := by
  have hscale := scaled_localMersennePrefixValue
    (D := D) (M := M) hD
  have hpowPos : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
  have hscaledBelow := mul_lt_mul_of_pos_left hbelow hpowPos
  rw [hscale] at hscaledBelow
  have hfractionNonneg : 0 ≤ localFractionMass D M := by
    unfold localFractionMass
    exact Finset.sum_nonneg fun d hd ↦
      (localMersenneFraction_pos (M := M) (hD d hd)).le
  have hhalf :
      (2 : ℚ) ^ M * (1 / 2 : ℚ) = (2 : ℚ) ^ (M - 1) := by
    calc
      (2 : ℚ) ^ M * (1 / 2 : ℚ) =
          2 ^ ((M - 1) + 1) * (1 / 2 : ℚ) := by congr 2 <;> omega
      _ = (2 : ℚ) ^ (M - 1) := by rw [pow_succ]; ring
  rw [hhalf] at hscaledBelow
  have hquotRat :
      (localPrefixQuotient D M : ℚ) < (2 : ℚ) ^ (M - 1) := by
    linarith
  have hquotNat : localPrefixQuotient D M < 2 ^ (M - 1) := by
    exact_mod_cast hquotRat
  unfold halfEndpointTarget
  omega

/-- The Möbius-centred carry of a finite support is exactly its signed local
endpoint defect.  Index `N` in the carry corresponds to endpoint `N+1`. -/
theorem mobiusCenteredHalfCarry_coe_finset_eq_localEndpointDefect
    {D : Finset ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) (N : ℕ) :
    mobiusCenteredHalfCarry (↑D : Set ℕ) N =
      localEndpointDefect D (N + 1) := by
  induction N with
  | zero =>
      have hquot : localPrefixQuotient D 1 = 0 := by
        unfold localPrefixQuotient
        apply Finset.sum_eq_zero
        intro d hd
        unfold localMersenneQuotient
        apply Nat.div_eq_of_lt
        have hpow : 2 ^ 2 ≤ 2 ^ d :=
          Nat.pow_le_pow_right (by norm_num) (hD d hd)
        norm_num at hpow ⊢
        omega
      simp [localEndpointDefect, halfEndpointTarget, hquot]
  | succ N ih =>
      rw [mobiusCenteredHalfCarry_succ, ih,
        localEndpointDefect_succ (M := N + 1) (by omega) hD,
        endpointDivisorContribution_eq_supportCoeff
          (D := D) (n := N + 2) (by omega)]

/-- For a below-half finite support, the natural binary suffix is literally
the Möbius-centred carry one row before its endpoint. -/
theorem localBinarySuffix_cast_eq_mobiusCenteredHalfCarry
    {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M)
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    (localBinarySuffix D 1 M : ℤ) =
      mobiusCenteredHalfCarry (↑D : Set ℕ) (M - 1) := by
  have hadm : localPrefixQuotient D M ≤ halfEndpointTarget M :=
    localPrefixQuotient_le_halfEndpointTarget_of_value_below hM hD hbelow
  have hsuffix :
      localBinarySuffix D 1 M =
        halfEndpointTarget M - localPrefixQuotient D M := by
    unfold localBinarySuffix halfEndpointTarget
    omega
  have hbridge :=
    mobiusCenteredHalfCarry_coe_finset_eq_localEndpointDefect
      (D := D) hD (M - 1)
  have hindex : M - 1 + 1 = M := by omega
  rw [hindex] at hbridge
  calc
    (localBinarySuffix D 1 M : ℤ) =
        (halfEndpointTarget M : ℤ) -
          (localPrefixQuotient D M : ℤ) := by
            rw [hsuffix, Nat.cast_sub hadm]
    _ = localEndpointDefect D M := rfl
    _ = mobiusCenteredHalfCarry (↑D : Set ℕ) (M - 1) := hbridge.symm

/-! ## Crossing-overshoot form of the predecessor socket -/

/-- One row before the usual critical endpoint, the crossing rank contributes
exactly the `c-3`-bit capacity. -/
theorem localMersenneQuotient_two_mul_sub_three_self
    {c : ℕ} (hc : 4 ≤ c) :
    localMersenneQuotient (2 * c - 3) c = 2 ^ (c - 3) := by
  have h := localMersenneQuotient_eq_two_pow_sub_of_half_lt
    (M := 2 * c - 3) (d := c) (by omega) (by omega) (by omega)
  simpa only [show 2 * c - 3 - c = c - 3 by omega] using h

/-- Exact accounting identity at the predecessor endpoint.  The available
`c-3`-bit capacity minus the local suffix is the scaled amount by which
adjoining the crossing rank exceeds one half, after subtracting the local
fractional-residue tax above one unit. -/
theorem precriticalCapacityGap_eq_crossingOvershoot_sub_fractionTax
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    ((2 ^ (c - 3) : ℕ) : ℚ) -
          (localBinarySuffix D 1 (2 * c - 3) : ℚ) =
      (2 : ℚ) ^ (2 * c - 3) *
          (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ)) -
        (localFractionMass (insert c D) (2 * c - 3) - 1) := by
  classical
  let M := 2 * c - 3
  let P := 2 ^ (c - 3)
  have hM : 1 ≤ M := by
    dsimp [M]
    omega
  have hcNotD : c ∉ D := by
    intro hcD
    have := (hD c hcD).2
    omega
  have hDtwo : ∀ d ∈ D, 2 ≤ d := fun d hd ↦ (hD d hd).1
  have hE : ∀ d ∈ insert c D, 2 ≤ d := by
    intro d hd
    rw [Finset.mem_insert] at hd
    rcases hd with rfl | hd
    · omega
    · exact hDtwo d hd
  have hadm : localPrefixQuotient D M ≤ halfEndpointTarget M :=
    localPrefixQuotient_le_halfEndpointTarget_of_value_below hM hDtwo hbelow
  have hsuffixNat :
      localBinarySuffix D 1 M =
        halfEndpointTarget M - localPrefixQuotient D M := by
    unfold localBinarySuffix halfEndpointTarget
    omega
  have hsuffixQ :
      (localBinarySuffix D 1 M : ℚ) =
        (halfEndpointTarget M : ℚ) - (localPrefixQuotient D M : ℚ) := by
    rw [hsuffixNat, Nat.cast_sub hadm]
  have htargetOne : 1 ≤ 2 ^ (M - 1) := Nat.one_le_pow _ _ (by norm_num)
  have htargetCast :
      (halfEndpointTarget M : ℚ) = (2 : ℚ) ^ (M - 1) - 1 := by
    unfold halfEndpointTarget
    rw [Nat.cast_sub htargetOne]
    norm_num
  have hinsert :
      localPrefixQuotient (insert c D) M =
        localMersenneQuotient M c + localPrefixQuotient D M := by
    unfold localPrefixQuotient
    rw [Finset.sum_insert hcNotD]
  have hcQuotient : localMersenneQuotient M c = P := by
    simpa [M, P] using localMersenneQuotient_two_mul_sub_three_self hc
  have hscale := scaled_localMersennePrefixValue
    (D := insert c D) (M := M) hE
  have hhalf :
      (2 : ℚ) ^ M * (1 / 2 : ℚ) = (2 : ℚ) ^ (M - 1) := by
    calc
      (2 : ℚ) ^ M * (1 / 2 : ℚ) =
          2 ^ ((M - 1) + 1) * (1 / 2 : ℚ) := by congr 2 <;> omega
      _ = (2 : ℚ) ^ (M - 1) := by rw [pow_succ]; ring
  have hid :
      (P : ℚ) - (localBinarySuffix D 1 M : ℚ) =
        (2 : ℚ) ^ M *
            (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ)) -
          (localFractionMass (insert c D) M - 1) := by
    calc
      (P : ℚ) - (localBinarySuffix D 1 M : ℚ) =
          (localPrefixQuotient D M : ℚ) + (P : ℚ) -
            ((2 : ℚ) ^ (M - 1) - 1) := by
              rw [hsuffixQ, htargetCast]
              ring
      _ = (localPrefixQuotient (insert c D) M : ℚ) -
            ((2 : ℚ) ^ (M - 1) - 1) := by
              rw [hinsert, hcQuotient]
              push_cast
              ring
      _ = (2 : ℚ) ^ M *
              (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ)) -
            (localFractionMass (insert c D) M - 1) := by
              rw [mul_sub, hhalf]
              linarith [hscale]
  simpa [M, P] using hid

/-- Sharp predecessor-capacity criterion: the crossing overshoot must exceed
the fractional-residue tax.  This is an equivalence, not a sufficient bound
with hidden slack. -/
theorem localBinarySuffix_two_mul_sub_three_lt_iff_crossingTax
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 3) < 2 ^ (c - 3) ↔
      localFractionMass (insert c D) (2 * c - 3) - 1 <
        (2 : ℚ) ^ (2 * c - 3) *
          (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ)) := by
  have hid := precriticalCapacityGap_eq_crossingOvershoot_sub_fractionTax
    hc hD hbelow
  constructor
  · intro hlt
    have hltQ :
        (localBinarySuffix D 1 (2 * c - 3) : ℚ) <
          ((2 ^ (c - 3) : ℕ) : ℚ) := by
      exact_mod_cast hlt
    have hpos := sub_pos.mpr hltQ
    rw [hid] at hpos
    linarith
  · intro htax
    have hpos :
        0 < (2 : ℚ) ^ (2 * c - 3) *
              (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ)) -
            (localFractionMass (insert c D) (2 * c - 3) - 1) := by
      linarith
    rw [← hid] at hpos
    have hltQ := sub_pos.mp hpos
    exact_mod_cast hltQ

/-- From rank six onward, one bit of future lookahead leaves enough dyadic
room to pay the crude cardinality bound for the lower support. -/
theorem sub_two_le_two_pow_sub_four
    {c : ℕ} (hc : 6 ≤ c) :
    c - 2 ≤ 2 ^ (c - 4) := by
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ c hc ih =>
      rw [show c + 1 - 4 = (c - 4) + 1 by omega, pow_succ]
      omega

/-- Exact rational remainder after a consecutive block of selected ranks. -/
theorem greedyMersenneRemainderRat_add_eq_sub_sum_of_taken
    (x : ℚ) (m J : ℕ)
    (htake : ∀ j ∈ Finset.range J,
      mersenneWeightRat (m + j + 1) ≤
        greedyMersenneRemainderRat x (m + j)) :
    greedyMersenneRemainderRat x (m + J) =
      greedyMersenneRemainderRat x m -
        ∑ j ∈ Finset.range J, mersenneWeightRat (m + j + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
      have hprev : ∀ j ∈ Finset.range J,
          mersenneWeightRat (m + j + 1) ≤
            greedyMersenneRemainderRat x (m + j) := by
        intro j hj
        apply htake j
        rw [Finset.mem_range] at hj ⊢
        omega
      have hlast := htake J (by simp)
      rw [show m + (J + 1) = (m + J) + 1 by omega,
        greedyMersenneRemainderRat_succ,
        if_pos (by simpa only [Nat.add_assoc] using hlast),
        ih hprev, Finset.sum_range_succ]
      ring

/-- A quantitative finite-lookahead certificate for the crossing-tax socket.
If the current half deficit lies below the next `t` Mersenne weights, then
the crossing overshoot dominates the dyadic gap left after those weights.
The elementary room bound makes that gap large enough to pay every local
fractional residue in the lower support. -/
theorem precriticalCrossingTax_of_futureThreshold
    {D : Finset ℕ} {c t : ℕ}
    (hc : 4 ≤ c)
    (ht : t ≤ c - 3)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hres :
      (1 / 2 : ℚ) - localMersennePrefixValue D <
        ∑ j ∈ Finset.range t, mersenneWeightRat (c + j + 1))
    (hroom : c - 2 ≤ 2 ^ (c - t - 3)) :
    localFractionMass (insert c D) (2 * c - 3) - 1 <
      (2 : ℚ) ^ (2 * c - 3) *
        (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ)) := by
  classical
  have hcNotD : c ∉ D := by
    intro hcD
    have := (hD c hcD).2
    omega
  have hE : ∀ d ∈ insert c D, 2 ≤ d := by
    intro d hd
    rw [Finset.mem_insert] at hd
    rcases hd with rfl | hd
    · omega
    · exact (hD d hd).1
  have hfraction := localFractionMass_le_card_skippedCore
    (D := insert c D) (M := 2 * c - 3) hE
  have hfractionCard :
      localFractionMass (insert c D) (2 * c - 3) - 1 ≤
        (D.card : ℚ) := by
    rw [Finset.card_insert_of_notMem hcNotD] at hfraction
    push_cast at hfraction
    linarith
  have hcard := card_le_sub_two_of_mem_lt hD
  have hcardQ : (D.card : ℚ) ≤ ((c - 2 : ℕ) : ℚ) := by
    exact_mod_cast hcard
  have htail : mersenneTail c < mersenneWeight c :=
    mersenneTail_lt_weight (by omega)
  have hgapReal := dyadic_lt_forcedBlock_of_tail_lt
    (m := c) (J := t) (r := mersenneWeight c) htail
  have hgapCast :
      (((1 / 2 : ℚ) ^ (c + t) : ℚ) : ℝ) <
        ((mersenneWeightRat c -
          ∑ j ∈ Finset.range t, mersenneWeightRat (c + j + 1) : ℚ) : ℝ) := by
    push_cast
    simpa only [cast_mersenneWeightRat] using hgapReal
  have hgap :
      (1 / 2 : ℚ) ^ (c + t) <
        mersenneWeightRat c -
          ∑ j ∈ Finset.range t, mersenneWeightRat (c + j + 1) :=
    (Rat.cast_lt (K := ℝ)).mp hgapCast
  have hinsert :
      localMersennePrefixValue (insert c D) =
        mersenneWeightRat c + localMersennePrefixValue D := by
    unfold localMersennePrefixValue
    rw [Finset.sum_insert hcNotD]
  have hover :
      (1 / 2 : ℚ) ^ (c + t) <
        localMersennePrefixValue (insert c D) - (1 / 2 : ℚ) := by
    rw [hinsert]
    linarith [hgap, hres]
  have hsplit :
      2 * c - 3 = (c - t - 3) + (c + t) := by
    omega
  have hscale :
      (2 : ℚ) ^ (2 * c - 3) * (1 / 2 : ℚ) ^ (c + t) =
        (2 : ℚ) ^ (c - t - 3) := by
    rw [hsplit, pow_add, mul_assoc, ← mul_pow]
    norm_num
  have hroomQ :
      ((c - 2 : ℕ) : ℚ) ≤ (2 : ℚ) ^ (c - t - 3) := by
    exact_mod_cast hroom
  have hscaledGap :
      (2 : ℚ) ^ (2 * c - 3) * (1 / 2 : ℚ) ^ (c + t) <
        (2 : ℚ) ^ (2 * c - 3) *
          (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ)) :=
    mul_lt_mul_of_pos_left hover (by positivity)
  calc
    localFractionMass (insert c D) (2 * c - 3) - 1 ≤
        (D.card : ℚ) := hfractionCard
    _ ≤ ((c - 2 : ℕ) : ℚ) := hcardQ
    _ ≤ (2 : ℚ) ^ (c - t - 3) := hroomQ
    _ = (2 : ℚ) ^ (2 * c - 3) * (1 / 2 : ℚ) ^ (c + t) := hscale.symm
    _ < (2 : ℚ) ^ (2 * c - 3) *
          (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ)) := hscaledGap

/-- Actual half-greedy specialization of the exact crossing-tax criterion.
The crossing overshoot is the next Mersenne weight minus the current greedy
remainder; no denominator estimate has yet been imposed. -/
theorem halfGreedy_precriticalSuffix_lt_iff_crossingTax
    {c : ℕ} (hc : 4 ≤ c) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
        2 ^ (c - 3) ↔
      localFractionMass
            (insert c (halfGreedyPrefixSupport (c - 1))) (2 * c - 3) - 1 <
        (2 : ℚ) ^ (2 * c - 3) *
          (mersenneWeightRat c -
            greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1)) := by
  let D := halfGreedyPrefixSupport (c - 1)
  have hD : ∀ d ∈ D, 2 ≤ d ∧ d < c :=
    halfGreedyPrefixSupport_bounds_before hc
  have hbelow : localMersennePrefixValue D < (1 / 2 : ℚ) := by
    simpa [D] using localMersennePrefixValue_halfGreedy_lt_half (c - 1)
  have hiff := localBinarySuffix_two_mul_sub_three_lt_iff_crossingTax
    (D := D) hc hD hbelow
  have hrem :
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) =
        (1 / 2 : ℚ) - localMersennePrefixValue D := by
    simpa [D, halfGreedyPrefixSupport] using
      (greedyMersenneRemainderRat_eq_sub_finiteErdosSum
        (1 / 2 : ℚ) (c - 1))
  have hcNotD : c ∉ D := by
    intro hcD
    have := (hD c hcD).2
    omega
  have hinsert :
      localMersennePrefixValue (insert c D) =
        mersenneWeightRat c + localMersennePrefixValue D := by
    unfold localMersennePrefixValue
    rw [Finset.sum_insert hcNotD]
  have hvalue :
      localMersennePrefixValue (insert c D) - (1 / 2 : ℚ) =
        mersenneWeightRat c -
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) := by
    rw [hinsert, hrem]
    ring
  rw [hvalue] at hiff
  simpa [D] using hiff

/-- A later skipped rank closes the predecessor socket when all intervening
ranks are selected and the finite lookahead still has enough dyadic room.
Here `t = 1` is the consecutive-skip case, while larger `t` consumes a short
actual take block. -/
theorem halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock
    {c t : ℕ} (hc : 4 ≤ c) (htPos : 0 < t) (ht : t ≤ c - 3)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c)
    (htake : ∀ j ∈ Finset.range (t - 1),
      mersenneWeightRat (c + j + 1) ≤
        greedyMersenneRemainderRat (1 / 2 : ℚ) (c + j))
    (hfuture : greedyMersenneRemainderRat (1 / 2 : ℚ) (c + t - 1) <
      mersenneWeightRat (c + t))
    (hroom : c - 2 ≤ 2 ^ (c - t - 3)) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3) := by
  let D := halfGreedyPrefixSupport (c - 1)
  have hD : ∀ d ∈ D, 2 ≤ d ∧ d < c :=
    halfGreedyPrefixSupport_bounds_before hc
  have hbelow : localMersennePrefixValue D < (1 / 2 : ℚ) := by
    simpa [D] using localMersennePrefixValue_halfGreedy_lt_half (c - 1)
  have hrem :
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) =
        (1 / 2 : ℚ) - localMersennePrefixValue D := by
    simpa [D, halfGreedyPrefixSupport] using
      (greedyMersenneRemainderRat_eq_sub_finiteErdosSum
        (1 / 2 : ℚ) (c - 1))
  have hnot :
      ¬ mersenneWeightRat c ≤
        greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) :=
    not_le.mpr hskip
  have hfreeze :
      greedyMersenneRemainderRat (1 / 2 : ℚ) c =
        greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) := by
    calc
      greedyMersenneRemainderRat (1 / 2 : ℚ) c =
          greedyMersenneRemainderRat (1 / 2 : ℚ) ((c - 1) + 1) := by
            congr 1
            omega
      _ = greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) := by
        rw [greedyMersenneRemainderRat_succ,
          if_neg (by
            simpa only [show c - 1 + 1 = c by omega] using hnot)]
  have hblock := greedyMersenneRemainderRat_add_eq_sub_sum_of_taken
    (1 / 2 : ℚ) c (t - 1) htake
  have hstate :
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c + t - 1) =
        greedyMersenneRemainderRat (1 / 2 : ℚ) c -
          ∑ j ∈ Finset.range (t - 1),
            mersenneWeightRat (c + j + 1) := by
    rw [show c + t - 1 = c + (t - 1) by omega]
    exact hblock
  rw [hstate, hfreeze] at hfuture
  have hsum :
      (∑ j ∈ Finset.range t, mersenneWeightRat (c + j + 1)) =
        (∑ j ∈ Finset.range (t - 1),
          mersenneWeightRat (c + j + 1)) + mersenneWeightRat (c + t) := by
    calc
      (∑ j ∈ Finset.range t, mersenneWeightRat (c + j + 1)) =
          ∑ j ∈ Finset.range ((t - 1) + 1),
            mersenneWeightRat (c + j + 1) := by
              congr 2
              omega
      _ = (∑ j ∈ Finset.range (t - 1),
            mersenneWeightRat (c + j + 1)) +
          mersenneWeightRat (c + (t - 1) + 1) := by
            rw [Finset.sum_range_succ]
      _ = (∑ j ∈ Finset.range (t - 1),
            mersenneWeightRat (c + j + 1)) + mersenneWeightRat (c + t) := by
            rw [show c + (t - 1) + 1 = c + t by omega]
  have hres :
      (1 / 2 : ℚ) - localMersennePrefixValue D <
        ∑ j ∈ Finset.range t, mersenneWeightRat (c + j + 1) := by
    rw [← hrem, hsum]
    linarith
  have htax := precriticalCrossingTax_of_futureThreshold
    (D := D) (c := c) (t := t) hc ht hD hres hroom
  exact (localBinarySuffix_two_mul_sub_three_lt_iff_crossingTax
    (D := D) (c := c) hc hD hbelow).2 htax

/-- Two consecutive actual skipped ranks close the predecessor socket at the
first rank.  The next skipped decision supplies `t = 1` in the quantitative
future-threshold theorem, while `c ≥ 6` supplies the required dyadic room. -/
theorem halfGreedy_precriticalSuffix_lt_of_next_skip
    {c : ℕ} (hc : 6 ≤ c)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c)
    (hnext : greedyMersenneRemainderRat (1 / 2 : ℚ) c <
      mersenneWeightRat (c + 1)) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3) := by
  apply halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock
    (c := c) (t := 1) (by omega) (by omega) (by omega) hskip
  · simp
  · simpa using hnext
  · simpa only [show c - 1 - 3 = c - 4 by omega] using
      (sub_two_le_two_pow_sub_four hc)

/-- Remaining actual-orbit separation socket in crossing coordinates: at
every skipped rank, the scaled crossing overshoot pays the exact local
fractional-residue tax. -/
def HalfGreedySkippedPrecriticalCrossingTaxSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c →
    localFractionMass
          (insert c (halfGreedyPrefixSupport (c - 1))) (2 * c - 3) - 1 <
      (2 : ℚ) ^ (2 * c - 3) *
        (mersenneWeightRat c -
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1))

/-- Global exact reduction of the predecessor supply to the crossing
overshoot/fractional-tax separation statement. -/
theorem halfGreedySkippedPrecriticalSuffixSupply_iff_crossingTax :
    HalfGreedySkippedPrecriticalSuffixSupply ↔
      HalfGreedySkippedPrecriticalCrossingTaxSupply := by
  constructor
  · intro hpre c hc hskip
    exact (halfGreedy_precriticalSuffix_lt_iff_crossingTax hc).1
      (hpre c hc hskip)
  · intro htax c hc hskip
    exact (halfGreedy_precriticalSuffix_lt_iff_crossingTax hc).2
      (htax c hc hskip)

/-- The complete predecessor supply reduces to the last skipped rank before
each actual take.  Ranks four and five are exact finite base cases; above
them, a failed next-take decision is precisely a second consecutive skip and
is discharged by `halfGreedy_precriticalSuffix_lt_of_next_skip`. -/
theorem halfGreedySkippedPrecriticalSuffixSupply_of_preTake
    (hpre : HalfGreedyPreTakePrecriticalSuffixSupply) :
    HalfGreedySkippedPrecriticalSuffixSupply := by
  intro c hc hskip
  by_cases hcSix : 6 ≤ c
  · by_cases htake :
        mersenneWeightRat (c + 1) ≤
          greedyMersenneRemainderRat (1 / 2 : ℚ) c
    · exact hpre c hcSix hskip htake
    · exact halfGreedy_precriticalSuffix_lt_of_next_skip hcSix hskip
        (lt_of_not_ge htake)
  · have hcSmall : c = 4 ∨ c = 5 := by omega
    rcases hcSmall with rfl | rfl
    · have hprefix :
          halfGreedyPrefixSupport (4 - 1) = ({2, 3} : Finset ℕ) := by
        decide
      rw [hprefix]
      norm_num [localBinarySuffix, localPrefixQuotient,
        localMersenneQuotient]
    · have hprefix :
          halfGreedyPrefixSupport (5 - 1) = ({2, 3} : Finset ℕ) := by
        decide
      rw [hprefix]
      norm_num [localBinarySuffix, localPrefixQuotient,
        localMersenneQuotient]

/-- Exact fan-in boundary for the new reduction: the only remaining rows are
skips immediately followed by takes. -/
theorem halfGreedySkippedPrecriticalSuffixSupply_iff_preTake :
    HalfGreedySkippedPrecriticalSuffixSupply ↔
      HalfGreedyPreTakePrecriticalSuffixSupply := by
  constructor
  · intro h c hc hskip _htake
    exact h c (by omega) hskip
  · exact halfGreedySkippedPrecriticalSuffixSupply_of_preTake

/-- The frozen-margin normalization has an exact complementary-carry
identity.  The accumulated `+1` baseline is the full binary word
`2^J-1`; hence a predecessor suffix fits in `J` bits exactly when the frozen
margin is nonnegative. -/
theorem halfGreedyPrefix_centeredCarry_add_frozenMargin
    (k J : ℕ) :
    mobiusCenteredHalfCarry
          (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + J) +
        greedyHalfFrozenMargin k J =
      (2 : ℤ) ^ J - 1 := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [show k + (J + 1) = k + J + 1 by omega,
        mobiusCenteredHalfCarry_succ,
        greedyHalfFrozenMargin_succ, pow_succ]
      linear_combination 2 * ih

/-- Pointwise exact reformulation of the precritical suffix bound as
nonnegativity of the finite frozen-margin recurrence. -/
theorem halfGreedy_precriticalSuffix_lt_iff_frozenMargin_nonneg
    {c : ℕ} (hc : 4 ≤ c) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
        2 ^ (c - 3) ↔
      0 ≤ greedyHalfFrozenMargin (c - 1) (c - 3) := by
  let D := halfGreedyPrefixSupport (c - 1)
  have hD : ∀ d ∈ D, 2 ≤ d :=
    fun d hd ↦ (halfGreedyPrefixSupport_bounds_before hc d hd).1
  have hbelow : localMersennePrefixValue D < (1 / 2 : ℚ) := by
    simpa [D] using localMersennePrefixValue_halfGreedy_lt_half (c - 1)
  have hsuffix := localBinarySuffix_cast_eq_mobiusCenteredHalfCarry
    (D := D) (M := 2 * c - 3) (by omega) hD hbelow
  have hbalance :=
    halfGreedyPrefix_centeredCarry_add_frozenMargin (c - 1) (c - 3)
  have hindex : (c - 1) + (c - 3) = (2 * c - 3) - 1 := by omega
  rw [hindex] at hbalance
  have hbalance' :
      (localBinarySuffix D 1 (2 * c - 3) : ℤ) +
          greedyHalfFrozenMargin (c - 1) (c - 3) =
        (2 : ℤ) ^ (c - 3) - 1 := by
    rw [hsuffix]
    simpa [D] using hbalance
  constructor
  · intro hlt
    have hltZ :
        (localBinarySuffix D 1 (2 * c - 3) : ℤ) <
          (2 : ℤ) ^ (c - 3) := by
      exact_mod_cast hlt
    omega
  · intro hmargin
    have hltZ :
        (localBinarySuffix D 1 (2 * c - 3) : ℤ) <
          (2 : ℤ) ^ (c - 3) := by
      omega
    exact_mod_cast hltZ

/-- The fixed precritical horizon is stronger than eventual frozen-margin
first passage: whenever it succeeds, the actual skipped-state dyadic excess
is already strictly negative. -/
theorem halfGreedy_precriticalSuffix_excess_neg
    {c : ℕ} (hc : 4 ≤ c)
    (hpre :
      localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
        2 ^ (c - 3)) :
    halfGreedyNextDyadicExcessNumerator (c - 1) < 0 := by
  apply (exists_greedyHalfFrozenMargin_nonneg_iff_excess_neg
    (c - 1) (by omega)).1
  exact ⟨c - 3,
    (halfGreedy_precriticalSuffix_lt_iff_frozenMargin_nonneg hc).1 hpre⟩

/-- Consequently a genuinely dyadically unsafe half-greedy state cannot
satisfy the precritical suffix bound.  The remaining pre-take producer must
first exclude this exact unsafe sliver; the following take supplies no
independent escape from it. -/
theorem not_halfGreedy_precriticalSuffix_lt_of_unsafe
    {c : ℕ} (hc : 4 ≤ c)
    (hunsafe : halfDyadicCap c <
      greedyMersenneRemainder (1 / 2 : ℝ) (c - 1)) :
    ¬ localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
        2 ^ (c - 3) := by
  intro hpre
  have hneg := halfGreedy_precriticalSuffix_excess_neg hc hpre
  have hpos : 0 < halfGreedyNextDyadicExcessNumerator (c - 1) := by
    apply (nextDyadic_lt_greedyHalfRemainder_iff_excess_pos (c - 1)).1
    simpa only [show c - 1 + 1 = c by omega] using hunsafe
  omega

/-- The actual-orbit version of the same socket: at a skipped rank, the
future skipped bits in the governed first-shell horizon cover the terminal
Möbius-centred carry. -/
def HalfGreedySkippedPrecriticalFutureSkipCoverageSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c →
    mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) (2 * c - 4) ≤
      (futureSkipCapacity
        (greedyMersenneSupport (1 / 2 : ℝ)) c (c - 3) : ℤ)

/-- At one skipped rank, the predecessor suffix bound is exactly actual
future-skip coverage.  No asymptotic or analytic remainder is hidden in this
reformulation. -/
theorem halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage
    {c : ℕ} (hc : 4 ≤ c)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
        2 ^ (c - 3) ↔
      mobiusCenteredHalfCarry
          (greedyMersenneSupport (1 / 2 : ℝ)) (2 * c - 4) ≤
        (futureSkipCapacity
          (greedyMersenneSupport (1 / 2 : ℝ)) c (c - 3) : ℤ) := by
  rw [halfGreedy_precriticalSuffix_lt_iff_frozenMargin_nonneg hc]
  have hskipCast := (Rat.cast_lt (K := ℝ)).2 hskip
  have hskipReal :
      ¬ mersenneWeight c ≤ greedyMersenneRemainder (1 / 2 : ℝ) (c - 1) := by
    rw [not_le]
    simpa using hskipCast
  have hbase : c - 1 + 1 = c := by omega
  have hskipReal' :
      ¬ mersenneWeight (c - 1 + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (c - 1) := by
    simpa [hbase] using hskipReal
  have hmargin := greedyHalfFrozenMargin_eq_actual_skip_margin
    (c - 1) (c - 3) hskipReal' (by omega)
  have hterminal : c - 1 + (c - 3) = 2 * c - 4 := by omega
  rw [hbase, hterminal] at hmargin
  rw [hmargin, sub_nonneg]

/-- Global exact reduction: the precritical suffix supply is neither stronger
nor weaker than first-shell future-skip coverage on the actual half-greedy
orbit. -/
theorem halfGreedySkippedPrecriticalSuffixSupply_iff_futureSkipCoverage :
    HalfGreedySkippedPrecriticalSuffixSupply ↔
      HalfGreedySkippedPrecriticalFutureSkipCoverageSupply := by
  constructor
  · intro hpre c hc hskip
    exact (halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage hc hskip).1
      (hpre c hc hskip)
  · intro hcover c hc hskip
    exact (halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage hc hskip).2
      (hcover c hc hskip)

/-- The analytic-looking crossing-tax socket and the combinatorial
future-skip coverage socket are exactly the same actual-orbit obligation. -/
theorem halfGreedySkippedPrecriticalCrossingTaxSupply_iff_futureSkipCoverage :
    HalfGreedySkippedPrecriticalCrossingTaxSupply ↔
      HalfGreedySkippedPrecriticalFutureSkipCoverageSupply :=
  halfGreedySkippedPrecriticalSuffixSupply_iff_crossingTax.symm.trans
    halfGreedySkippedPrecriticalSuffixSupply_iff_futureSkipCoverage

/-- The predecessor-endpoint suffix bound implies the critical quotient
socket.  Advancing from endpoint `2c-3` to `2c-2` at most doubles the binary
defect and adds one, while the available capacity doubles exactly. -/
theorem halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix
    (hpre : HalfGreedySkippedPrecriticalSuffixSupply) :
    HalfGreedySkippedCriticalQuotientSupply := by
  intro c hc hskip
  let D := halfGreedyPrefixSupport (c - 1)
  have hD := halfGreedyPrefixSupport_bounds_before hc
  have hbelow := localMersennePrefixValue_halfGreedy_lt_half (c - 1)
  apply (localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff
    hc hD hbelow).1
  change localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)
  have hprev : localBinarySuffix D 1 (2 * c - 3) < 2 ^ (c - 3) := by
    simpa [D] using hpre c hc hskip
  have hsucc := localPrefixQuotient_succ
    (D := D) (M := 2 * c - 3) (fun d hd ↦ (hD d hd).1)
  have hindex : 2 * c - 3 + 1 = 2 * c - 2 := by omega
  rw [hindex] at hsucc
  have htarget :
      2 ^ ((2 * c - 2) - 1) =
        2 * 2 ^ ((2 * c - 3) - 1) := by
    rw [show (2 * c - 2) - 1 = ((2 * c - 3) - 1) + 1 by omega,
      pow_succ']
  have hcapacity : 2 ^ (c - 2) = 2 * 2 ^ (c - 3) := by
    rw [show c - 2 = (c - 3) + 1 by omega, pow_succ']
  unfold localBinarySuffix at hprev ⊢
  rw [hsucc, htarget, hcapacity]
  omega

/-- The canonical crossing socket has no hidden analytic hypotheses: it is
exactly the quotient inequality at each actual skipped half-greedy rank. -/
theorem halfGreedyCriticalQuotientSupply_iff_skipped :
    HalfGreedyCriticalQuotientSupply ↔
      HalfGreedySkippedCriticalQuotientSupply := by
  have hrem (c : ℕ) :
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) =
        (1 / 2 : ℚ) -
          localMersennePrefixValue (halfGreedyPrefixSupport (c - 1)) := by
    simpa [halfGreedyPrefixSupport] using
      (greedyMersenneRemainderRat_eq_sub_finiteErdosSum
        (1 / 2 : ℚ) (c - 1))
  constructor
  · intro hcap c hc hskip
    apply hcap c hc (localMersennePrefixValue_halfGreedy_lt_half (c - 1))
    rw [← hrem c]
    exact hskip
  · intro hcap c hc _hbelow hcross
    apply hcap c hc
    rw [hrem c]
    exact hcross

/-- The universal skipped-core quotient socket is exactly its canonical
half-greedy specialization. -/
theorem skippedCoreCriticalQuotientSupply_iff_halfGreedy :
    SkippedCoreCriticalQuotientSupply ↔
      HalfGreedyCriticalQuotientSupply := by
  constructor
  · intro hcap c hc hbelow hcross
    exact hcap (halfGreedyPrefixSupport (c - 1)) c hc
      (halfGreedyPrefixSupport_bounds_before hc) hbelow hcross
  · intro hgreedy D c hc hD hbelow hcross
    have hEq := eq_halfGreedyPrefixSupport_of_critical_crossing
      hc hD hbelow hcross
    subst D
    exact hgreedy c hc hbelow hcross

/-- Final quantifier reduction: the original universal finite-core supply is
equivalent to one explicit integral inequality at each actual skipped rank of
the half-greedy orbit. -/
theorem skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped :
    SkippedCoreCriticalQuotientSupply ↔
      HalfGreedySkippedCriticalQuotientSupply :=
  skippedCoreCriticalQuotientSupply_iff_halfGreedy.trans
    halfGreedyCriticalQuotientSupply_iff_skipped

/-- A pre-take predecessor supply feeds the original universal critical
quotient socket. -/
theorem skippedCoreCriticalQuotientSupply_of_preTake
    (hpre : HalfGreedyPreTakePrecriticalSuffixSupply) :
    SkippedCoreCriticalQuotientSupply := by
  apply skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped.mpr
  apply halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix
  exact halfGreedySkippedPrecriticalSuffixSupply_of_preTake hpre

/-- An exact row together with a protected below-half core.  Every support
rank outside the core lies strictly above `cutoff`, and the current endpoint
lies below `2 * cutoff`.  These two inequalities force the next first
crossing to occur late enough to give strict endpoint progress. -/
structure ProtectedExactLocalMersenneRow where
  endpoint : ℕ
  cutoff : ℕ
  support : Finset ℕ
  core : Finset ℕ
  endpoint_six : 6 ≤ endpoint
  cutoff_four : 4 ≤ cutoff
  core_subset : core ⊆ support
  new_above_cutoff : ∀ d ∈ support, d ∉ core → cutoff < d
  core_bounds : ∀ d ∈ core, 2 ≤ d ∧ d ≤ cutoff
  support_bounds : ∀ d ∈ support, 2 ≤ d ∧ d ≤ endpoint
  exact_quotient :
    localPrefixQuotient support endpoint = 2 ^ (endpoint - 1) - 1
  core_below_half : localMersennePrefixValue core < (1 / 2 : ℚ)
  two_mem_core : 2 ∈ core
  endpoint_lt_twice_cutoff : endpoint < 2 * cutoff

/-- The concrete endpoint-six row is the initial protected state. -/
def protectedExactLocalMersenneRowSeed : ProtectedExactLocalMersenneRow where
  endpoint := 6
  cutoff := 6
  support := exactRowSixSupport
  core := exactRowSixSupport
  endpoint_six := by omega
  cutoff_four := by omega
  core_subset := by
    intro d hd
    exact hd
  new_above_cutoff := by
    intro d hd hdnot
    exact (hdnot hd).elim
  core_bounds := exactRowSixSupport_bounds
  support_bounds := exactRowSixSupport_bounds
  exact_quotient := exactRowSixSupport_quotient
  core_below_half := exactRowSixSupport_value_lt_half
  two_mem_core := by simp [exactRowSixSupport]
  endpoint_lt_twice_cutoff := by omega

/-- Forgetting protection leaves an ordinary exact local row. -/
theorem ProtectedExactLocalMersenneRow.exactRow
    (s : ProtectedExactLocalMersenneRow) :
    ExactLocalMersenneHalfRow s.endpoint := by
  exact ⟨s.support, s.support_bounds, s.exact_quotient⟩

/-- Under the critical quotient supply, every protected exact row has a
strictly later protected successor.

If the current support is below one half, the literal doubling window makes
the whole support the next protected core.  If it is above one half, its first
crossing lies strictly beyond the old cutoff: otherwise the inclusive crossing
prefix would be contained in the protected below-half core.  The critical
supply then gives a strict-upper skipped-core fill at that later crossing. -/
theorem exists_laterProtectedExactLocalMersenneRow
    (hcap : SkippedCoreCriticalQuotientSupply)
    (s : ProtectedExactLocalMersenneRow) :
    ∃ t : ProtectedExactLocalMersenneRow, s.endpoint < t.endpoint := by
  classical
  by_cases hbelow : localMersennePrefixValue s.support < (1 / 2 : ℚ)
  · have hn := s.endpoint_six
    have htwoSupport : 2 ∈ s.support := s.core_subset s.two_mem_core
    obtain ⟨E, hsub, hnew, _htwo, hE, hquot⟩ :=
      exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below
        s.endpoint_six s.support_bounds htwoSupport s.exact_quotient hbelow
    refine ⟨{
      endpoint := 2 * s.endpoint - 1
      cutoff := s.endpoint
      support := E
      core := s.support
      endpoint_six := by omega
      cutoff_four := by omega
      core_subset := hsub
      new_above_cutoff := hnew
      core_bounds := s.support_bounds
      support_bounds := hE
      exact_quotient := hquot
      core_below_half := hbelow
      two_mem_core := htwoSupport
      endpoint_lt_twice_cutoff := by omega
    }, by
      change s.endpoint < 2 * s.endpoint - 1
      omega⟩
  · have hzero : 0 ∉ s.support := by
      intro hzero
      have := (s.support_bounds 0 hzero).1
      omega
    have hne : localMersennePrefixValue s.support ≠ (1 / 2 : ℚ) := by
      intro heq
      have hodd := finiteErdosSum_den_odd s.support hzero
      rw [← localMersennePrefixValue_eq_finiteErdosSum, heq] at hodd
      obtain ⟨k, hk⟩ := hodd
      norm_num at hk
      omega
    have habove : (1 / 2 : ℚ) < localMersennePrefixValue s.support := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (hbelow hlt).elim
      · exact hgt
    obtain ⟨e, heSupport, heFour, hePrefixBelow, heCross⟩ :=
      exists_first_localMersenne_crossing
        (fun d hd ↦ (s.support_bounds d hd).1) habove
    have heLater : s.cutoff < e := by
      by_contra hnot
      have heLe : e ≤ s.cutoff := by omega
      let F := insert e (s.support.filter fun d ↦ d < e)
      have hFsub : F ⊆ s.core := by
        intro d hdF
        simp only [F, Finset.mem_insert, Finset.mem_filter] at hdF
        rcases hdF with hdeq | ⟨hdSupport, hde⟩
        · have heCore : e ∈ s.core := by
            by_contra heNotCore
            have := s.new_above_cutoff e heSupport heNotCore
            omega
          simpa [hdeq] using heCore
        · by_contra hdCore
          have := s.new_above_cutoff d hdSupport hdCore
          omega
      have hFle :
          localMersennePrefixValue F ≤ localMersennePrefixValue s.core := by
        unfold localMersennePrefixValue
        apply Finset.sum_le_sum_of_subset_of_nonneg hFsub
        intro d hdCore _hdF
        have hdTwo : 2 ≤ d := (s.core_bounds d hdCore).1
        exact (mersenneWeightRat_pos (n := d) (by omega)).le
      have hFabove : (1 / 2 : ℚ) < localMersennePrefixValue F := by
        simpa [F] using heCross
      have hcoreBelow := s.core_below_half
      linarith
    let D := s.support.filter fun d ↦ d < e
    have hD : ∀ d ∈ D, 2 ≤ d ∧ d < e := by
      intro d hd
      have hdData := Finset.mem_filter.mp hd
      exact ⟨(s.support_bounds d hdData.1).1, hdData.2⟩
    have heNotD : e ∉ D := by simp [D]
    have hinsert :
        localMersennePrefixValue (insert e D) =
          localMersennePrefixValue D + mersenneWeightRat e := by
      unfold localMersennePrefixValue
      rw [Finset.sum_insert heNotD]
      ring
    have hskip :
        (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat e := by
      have hcrossD :
          (1 / 2 : ℚ) < localMersennePrefixValue (insert e D) := by
        simpa [D] using heCross
      rw [hinsert] at hcrossD
      linarith
    have hprefixBelow : localMersennePrefixValue D < (1 / 2 : ℚ) := by
      simpa [D] using hePrefixBelow
    have hcritical :
        2 ^ ((2 * e - 2) - 1) ≤
          localPrefixQuotient (insert e D) (2 * e - 2) :=
      hcap D e heFour hD hprefixBelow hskip
    have hsharp : localBinarySuffix D 1 (2 * e - 2) < 2 ^ (e - 2) :=
      (localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff
        heFour hD hprefixBelow).2 hcritical
    obtain ⟨E, hsub, hnew, hE, hquot⟩ :=
      exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity
        heFour hD hprefixBelow hsharp
    have htwoD : 2 ∈ D := by
      apply Finset.mem_filter.mpr
      exact ⟨s.core_subset s.two_mem_core, by omega⟩
    refine ⟨{
      endpoint := 2 * e - 2
      cutoff := e
      support := E
      core := D
      endpoint_six := by omega
      cutoff_four := heFour
      core_subset := hsub
      new_above_cutoff := hnew
      core_bounds := by
        intro d hd
        exact ⟨(hD d hd).1, (hD d hd).2.le⟩
      support_bounds := hE
      exact_quotient := hquot
      core_below_half := hprefixBelow
      two_mem_core := htwoD
      endpoint_lt_twice_cutoff := by omega
    }, by
      change s.endpoint < 2 * e - 2
      have hold := s.endpoint_lt_twice_cutoff
      omega⟩

/-- A chosen protected successor. -/
noncomputable def protectedExactLocalMersenneRowNext
    (hcap : SkippedCoreCriticalQuotientSupply)
    (s : ProtectedExactLocalMersenneRow) : ProtectedExactLocalMersenneRow :=
  Classical.choose (exists_laterProtectedExactLocalMersenneRow hcap s)

theorem protectedExactLocalMersenneRow_endpoint_lt_next
    (hcap : SkippedCoreCriticalQuotientSupply)
    (s : ProtectedExactLocalMersenneRow) :
    s.endpoint < (protectedExactLocalMersenneRowNext hcap s).endpoint := by
  exact Classical.choose_spec (exists_laterProtectedExactLocalMersenneRow hcap s)

/-- Iteration of the protected successor from the endpoint-six seed. -/
noncomputable def protectedExactLocalMersenneRowOrbit
    (hcap : SkippedCoreCriticalQuotientSupply) :
    ℕ → ProtectedExactLocalMersenneRow
  | 0 => protectedExactLocalMersenneRowSeed
  | n + 1 => protectedExactLocalMersenneRowNext hcap
      (protectedExactLocalMersenneRowOrbit hcap n)

theorem protectedExactLocalMersenneRowOrbit_endpoint_lt_succ
    (hcap : SkippedCoreCriticalQuotientSupply) (n : ℕ) :
    (protectedExactLocalMersenneRowOrbit hcap n).endpoint <
      (protectedExactLocalMersenneRowOrbit hcap (n + 1)).endpoint := by
  simpa [protectedExactLocalMersenneRowOrbit] using
    protectedExactLocalMersenneRow_endpoint_lt_next hcap
      (protectedExactLocalMersenneRowOrbit hcap n)

theorem index_le_protectedExactLocalMersenneRowOrbit_endpoint
    (hcap : SkippedCoreCriticalQuotientSupply) (n : ℕ) :
    n ≤ (protectedExactLocalMersenneRowOrbit hcap n).endpoint := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hstep :=
        protectedExactLocalMersenneRowOrbit_endpoint_lt_succ hcap n
      omega

/-- The critical quotient supply produces exact rows at cofinally many
endpoints. -/
theorem cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    CofinalExactLocalMersenneHalfRows := by
  intro N
  let s := protectedExactLocalMersenneRowOrbit hcap N
  refine ⟨s.endpoint, ?_, ?_⟩
  · simpa [s] using
      index_le_protectedExactLocalMersenneRowOrbit_endpoint hcap N
  · exact s.exactRow

/-- Conditional #257 endpoint: the critical quotient supply is sufficient to
place one half in the Mersenne achievement set. -/
theorem half_mem_mersenneAchievementSet_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_cofinalExactLocalRows
    (cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply hcap)

/-- Conditional #257 endpoint with every consecutive-skip row removed: it is
enough to prove the predecessor bound only at a skipped rank whose successor
is actually selected. -/
theorem half_mem_mersenneAchievementSet_of_preTakePrecriticalSuffixSupply
    (hpre : HalfGreedyPreTakePrecriticalSuffixSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_criticalQuotientSupply
    (skippedCoreCriticalQuotientSupply_of_preTake hpre)

#print axioms exists_laterProtectedExactLocalMersenneRow
#print axioms cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply
#print axioms half_mem_mersenneAchievementSet_of_criticalQuotientSupply
#print axioms eq_halfGreedyPrefixSupport_of_critical_crossing
#print axioms skippedCoreCriticalQuotientSupply_iff_halfGreedy
#print axioms localMersennePrefixValue_halfGreedy_lt_half
#print axioms halfGreedyCriticalQuotientSupply_iff_skipped
#print axioms skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped
#print axioms localBinarySuffix_cast_eq_mobiusCenteredHalfCarry
#print axioms precriticalCapacityGap_eq_crossingOvershoot_sub_fractionTax
#print axioms localBinarySuffix_two_mul_sub_three_lt_iff_crossingTax
#print axioms sub_two_le_two_pow_sub_four
#print axioms greedyMersenneRemainderRat_add_eq_sub_sum_of_taken
#print axioms precriticalCrossingTax_of_futureThreshold
#print axioms halfGreedy_precriticalSuffix_lt_iff_crossingTax
#print axioms halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock
#print axioms halfGreedy_precriticalSuffix_lt_of_next_skip
#print axioms halfGreedySkippedPrecriticalSuffixSupply_iff_crossingTax
#print axioms halfGreedySkippedPrecriticalSuffixSupply_iff_preTake
#print axioms halfGreedyPrefix_centeredCarry_add_frozenMargin
#print axioms halfGreedy_precriticalSuffix_excess_neg
#print axioms not_halfGreedy_precriticalSuffix_lt_of_unsafe
#print axioms halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage
#print axioms halfGreedySkippedPrecriticalSuffixSupply_iff_futureSkipCoverage
#print axioms halfGreedySkippedPrecriticalCrossingTaxSupply_iff_futureSkipCoverage
#print axioms halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix
#print axioms skippedCoreCriticalQuotientSupply_of_preTake
#print axioms half_mem_mersenneAchievementSet_of_preTakePrecriticalSuffixSupply

end Erdos249257
