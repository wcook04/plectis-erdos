import Erdos257PeriodNoncollapse.BooleanMobiusLocalRepair
import Erdos257PeriodNoncollapse.HalfCarryReachability

/-!
# Global Boolean--Möbius repair limit

This module is the compactness/limit consumer for the endpoint construction in
`BooleanMobiusLocalRepair`.

At endpoint `n`, a repair row keeps every bit through `floor (n / 2)` and
rewrites the strict upper half `(floor (n / 2), n]`.  The rewritten word has
dyadic value

`H = 2 A + 1 - S`,

where `A` is `localBinarySuffix` and `S` is
`endpointDivisorContribution`.  Once these finite rows exist at every
endpoint, no further compactness assumption is needed:

* a coordinate `d` is frozen from row `2d` onward;
* the diagonal frozen word is Boolean;
* exact endpoint quotient `2^(n-1)-1` makes the row value tend to `1/2`;
* agreement through `floor (n/2)` makes the row values tend to the frozen
  support value;
* uniqueness of limits gives an infinite support of value `1/2`.

The genuinely unresolved producer is kept visible as
`GlobalEndpointExponentialBound`.  It is the uniform inequality

`2^(S-1)-1 <= A`

on the lower support occurring in every row.  The larger predicate
`GlobalBooleanMobiusRepairFeasible` also records the mechanical word,
capacity, and quotient receipts needed by this consumer.  Nothing in this
file proves that predicate, and therefore nothing here by itself settles
Erdos #257.
-/

namespace Erdos257PeriodNoncollapse

open Filter Set
open scoped BigOperators

/-! ## Endpoint rows and the frozen diagonal -/

/-- The finite Boolean support displayed by row `n`.  Coordinates zero and
one are normalized away at the definition boundary. -/
def globalRepairStageSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun d ↦ bit n d = true

@[simp] theorem mem_globalRepairStageSupport
    {bit : ℕ → ℕ → Bool} {n d : ℕ} :
    d ∈ globalRepairStageSupport bit n ↔
      2 ≤ d ∧ d ≤ n ∧ bit n d = true := by
  simp [globalRepairStageSupport, and_assoc]

/-- The part of row `n` which is already frozen before its upper-half
rewrite. -/
def globalRepairLowerSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (globalRepairStageSupport bit n).filter fun d ↦ d ≤ n / 2

@[simp] theorem mem_globalRepairLowerSupport
    {bit : ℕ → ℕ → Bool} {n d : ℕ} :
    d ∈ globalRepairLowerSupport bit n ↔
      2 ≤ d ∧ d ≤ n / 2 ∧ bit n d = true := by
  rw [globalRepairLowerSupport, Finset.mem_filter,
    mem_globalRepairStageSupport]
  constructor
  · rintro ⟨⟨h2, _hdn, hbit⟩, hhalf⟩
    exact ⟨h2, hhalf, hbit⟩
  · rintro ⟨h2, hhalf, hbit⟩
    exact ⟨⟨h2, hhalf.trans (Nat.div_le_self n 2), hbit⟩, hhalf⟩

/-- Structural part of an endpoint-by-endpoint repair trajectory.  The
arithmetic producer receipts are separated into
`GlobalBooleanMobiusRepairFeasible` below. -/
structure BooleanMobiusGlobalRepairTrajectory where
  bit : ℕ → ℕ → Bool
  frozen_step : ∀ {n d : ℕ}, 2 * d ≤ n → bit (n + 1) d = bit n d

/-- Once endpoint `2d` has been reached, coordinate `d` never changes. -/
theorem BooleanMobiusGlobalRepairTrajectory.bit_stable
    (T : BooleanMobiusGlobalRepairTrajectory) {d n : ℕ}
    (hdn : 2 * d ≤ n) :
    T.bit n d = T.bit (2 * d) d := by
  induction n, hdn using Nat.le_induction with
  | base => rfl
  | succ n hdn ih =>
      rw [T.frozen_step hdn, ih]

/-- The diagonal limit bit: inspect coordinate `d` at the first row after
which the upper-half rewrites can no longer touch it. -/
def globalRepairLimitBit
    (T : BooleanMobiusGlobalRepairTrajectory) (d : ℕ) : Bool :=
  T.bit (2 * d) d

/-- The positive frozen support selected by the diagonal limit word. -/
def globalRepairLimitSupport
    (T : BooleanMobiusGlobalRepairTrajectory) : Set ℕ :=
  {d : ℕ | 2 ≤ d ∧ globalRepairLimitBit T d = true}

@[simp] theorem mem_globalRepairLimitSupport
    {T : BooleanMobiusGlobalRepairTrajectory} {d : ℕ} :
    d ∈ globalRepairLimitSupport T ↔
      2 ≤ d ∧ T.bit (2 * d) d = true := by
  rfl

theorem zero_not_mem_globalRepairLimitSupport
    (T : BooleanMobiusGlobalRepairTrajectory) :
    0 ∉ globalRepairLimitSupport T := by
  simp

theorem one_not_mem_globalRepairLimitSupport
    (T : BooleanMobiusGlobalRepairTrajectory) :
    1 ∉ globalRepairLimitSupport T := by
  simp

/-- A row and the diagonal limit agree through that row's frozen half. -/
theorem globalRepairStageSupport_agrees_limit_of_le_half
    (T : BooleanMobiusGlobalRepairTrajectory) {n d : ℕ}
    (hd : d ≤ n / 2) :
    d ∈ globalRepairStageSupport T.bit n ↔
      d ∈ globalRepairLimitSupport T := by
  have hstable : T.bit n d = T.bit (2 * d) d :=
    T.bit_stable (by omega)
  simp only [mem_globalRepairStageSupport,
    mem_globalRepairLimitSupport]
  constructor
  · rintro ⟨hd2, hdn, hbit⟩
    exact ⟨hd2, hstable ▸ hbit⟩
  · rintro ⟨hd2, hbit⟩
    exact ⟨hd2, by omega, hstable.symm ▸ hbit⟩

/-! ## The explicit finite producer hypothesis -/

/-- The empirically observed endpoint inequality which makes every repair
integer nonnegative.  This is a named open producer, not a conclusion of the
global limit argument. -/
def GlobalEndpointExponentialBound
    (T : BooleanMobiusGlobalRepairTrajectory) : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    let D := globalRepairLowerSupport T.bit n
    2 ^ (endpointDivisorContribution D n - 1) - 1 ≤
      localBinarySuffix D 1 (n - 1)

/-- The upper-half row, read from endpoint `n` downwards as a natural
least-significant-digit-first word. -/
def globalRepairUpperWord
    (T : BooleanMobiusGlobalRepairTrajectory) (n : ℕ) : List ℕ :=
  upperSuffixWord
    (fun d ↦ if T.bit n d = true then 1 else 0) (n / 2) n

theorem globalRepairUpperWord_length
    (T : BooleanMobiusGlobalRepairTrajectory) (n : ℕ) :
    (globalRepairUpperWord T n).length = upperHalfRepairLength n := by
  simp [globalRepairUpperWord, upperHalfRepairLength]

theorem globalRepairUpperWord_boolean
    (T : BooleanMobiusGlobalRepairTrajectory) (n : ℕ) :
    ∀ b ∈ globalRepairUpperWord T n, b = 0 ∨ b = 1 := by
  intro b hb
  rw [globalRepairUpperWord, upperSuffixWord, List.mem_map] at hb
  obtain ⟨i, _hi, rfl⟩ := hb
  split_ifs <;> omega

/-- Full finite receipt for the endpoint process.  Of its four clauses, the
exponential bound is the genuine arithmetic producer.  Word realization,
capacity, and the quotient equality are finite algebraic audit clauses kept
here so the limit theorem cannot silently assume them.

The quotient clause says that the row has consumed precisely every binary
integer below the target `1/2` at scale `2^n`; the missing unit is carried by
the sum of the Mersenne fractional parts. -/
def GlobalBooleanMobiusRepairFeasible
    (T : BooleanMobiusGlobalRepairTrajectory) : Prop :=
  GlobalEndpointExponentialBound T ∧
  (∀ n : ℕ, 2 ≤ n →
    let D := globalRepairLowerSupport T.bit n
    signedDyadicValue
        (List.map (fun b : ℕ ↦ (b : ℤ)) (globalRepairUpperWord T n)) =
      localRepairInteger D 1 n) ∧
  (∀ n : ℕ, 2 ≤ n →
    let D := globalRepairLowerSupport T.bit n
    localRepairInteger D 1 n < (2 ^ upperHalfRepairLength n : ℕ)) ∧
  (∀ n : ℕ, 2 ≤ n →
    localPrefixQuotient (globalRepairStageSupport T.bit n) n =
      2 ^ (n - 1) - 1)

/-- The named exponential producer discharges endpoint nonnegativity through
the local theorem. -/
theorem globalRepairInteger_nonneg
    (T : BooleanMobiusGlobalRepairTrajectory)
    (hbound : GlobalEndpointExponentialBound T)
    {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ localRepairInteger
      (globalRepairLowerSupport T.bit n) 1 n := by
  exact localRepairInteger_nonneg_of_exponential_endpoint_bound
    (hbound n hn)

/-! ## Quantitative endpoint approximation -/

theorem localMersenneFraction_lt_one
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneFraction M d < 1 := by
  unfold localMersenneFraction
  have hrlt : M % d < d := Nat.mod_lt _ (by omega)
  have hrle : M % d ≤ d - 1 := by omega
  have hpowle : 2 ^ (M % d) ≤ 2 ^ (d - 1) :=
    Nat.pow_le_pow_right (by norm_num) hrle
  have hsplit : 2 ^ d = 2 ^ (d - 1) * 2 := by
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (d - 1) * 2 := by rw [pow_succ]
  have hhalf : 2 ≤ 2 ^ (d - 1) := by
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ d - 1))
  have hltNat : 2 ^ (M % d) < 2 ^ d - 1 := by omega
  rw [div_lt_one]
  · exact_mod_cast hltNat
  · exact_mod_cast (Nat.sub_pos_of_lt
      (one_lt_pow₀ (by omega) (by omega) : 1 < 2 ^ d))

theorem localFractionMass_nonneg
    {D : Finset ℕ} {M : ℕ} (hD : ∀ d ∈ D, 2 ≤ d) :
    0 ≤ localFractionMass D M := by
  unfold localFractionMass
  exact Finset.sum_nonneg fun d hd ↦
    (localMersenneFraction_pos (M := M) (hD d hd)).le

theorem localFractionMass_le_card
    {D : Finset ℕ} {M : ℕ} (hD : ∀ d ∈ D, 2 ≤ d) :
    localFractionMass D M ≤ (D.card : ℚ) := by
  unfold localFractionMass
  calc
    (∑ d ∈ D, localMersenneFraction M d)
        ≤ ∑ _d ∈ D, (1 : ℚ) := by
          exact Finset.sum_le_sum fun d hd ↦
            (localMersenneFraction_lt_one (M := M) (hD d hd)).le
    _ = (D.card : ℚ) := by simp

/-- Exact quotient at row `n` gives an `O(n/2^n)` approximation to one
half.  The proof uses no monotonicity: a row may overshoot or undershoot. -/
theorem abs_localMersennePrefixValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    |((localMersennePrefixValue D : ℚ) : ℝ) - (1 : ℝ) / 2| ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  have hscale := scaled_localMersennePrefixValue
    (D := D) (M := n) (fun d hd ↦ (hD d hd).1)
  rw [hquot] at hscale
  have hFnonneg := localFractionMass_nonneg
    (D := D) (M := n) (fun d hd ↦ (hD d hd).1)
  have hFcard := localFractionMass_le_card
    (D := D) (M := n) (fun d hd ↦ (hD d hd).1)
  have hcard : D.card ≤ n + 1 := by
    have hsubset : D ⊆ Finset.range (n + 1) := by
      intro d hd
      have hdle := (hD d hd).2
      exact Finset.mem_range.mpr (by omega)
    calc
      D.card ≤ (Finset.range (n + 1)).card :=
        Finset.card_le_card hsubset
      _ = n + 1 := by simp
  have hFupper : localFractionMass D n ≤ (n + 1 : ℕ) := by
    exact hFcard.trans (by exact_mod_cast hcard)
  have hpow : (2 : ℚ) ^ n = 2 * (2 : ℚ) ^ (n - 1) := by
    calc
      (2 : ℚ) ^ n = 2 ^ ((n - 1) + 1) := by congr 1 <;> omega
      _ = 2 * (2 : ℚ) ^ (n - 1) := by rw [pow_succ]; ring
  have hscale' :
      localMersennePrefixValue D * (2 : ℚ) ^ n =
        ((2 ^ (n - 1) - 1 : ℕ) : ℚ) + localFractionMass D n := by
    simpa [mul_comm] using hscale
  have hcastQ : ((2 ^ (n - 1) - 1 : ℕ) : ℚ) =
      (2 : ℚ) ^ (n - 1) - 1 := by
    have hone : 1 ≤ 2 ^ (n - 1) :=
      Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.cast_sub hone]
    norm_num
  have hidQ :
      localMersennePrefixValue D - (1 : ℚ) / 2 =
        (localFractionMass D n - 1) / (2 : ℚ) ^ n := by
    rw [eq_div_iff (by positivity : (2 : ℚ) ^ n ≠ 0)]
    rw [sub_mul, hscale', hcastQ, hpow]
    ring
  have habsQ :
      |localMersennePrefixValue D - (1 : ℚ) / 2| ≤
        ((n + 1 : ℕ) : ℚ) / (2 : ℚ) ^ n := by
    rw [hidQ, abs_div, abs_pow, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply (abs_le).2
    constructor
    · have honebound : (1 : ℚ) ≤ ((n + 1 : ℕ) : ℚ) := by
        exact_mod_cast (show 1 ≤ n + 1 by omega)
      linarith
    · linarith
  have habsR :
      (((|localMersennePrefixValue D - (1 : ℚ) / 2| : ℚ) : ℝ)) ≤
        ((((n + 1 : ℕ) : ℚ) / (2 : ℚ) ^ n : ℚ) : ℝ) := by
    exact_mod_cast habsQ
  simpa using habsR

/-- Real value of one finite endpoint row. -/
noncomputable def globalRepairStageValue
    (T : BooleanMobiusGlobalRepairTrajectory) (n : ℕ) : ℝ :=
  ((localMersennePrefixValue
    (globalRepairStageSupport T.bit n) : ℚ) : ℝ)

theorem abs_globalRepairStageValue_sub_half_le
    (T : BooleanMobiusGlobalRepairTrajectory)
    (hfeas : GlobalBooleanMobiusRepairFeasible T)
    {n : ℕ} (hn : 2 ≤ n) :
    |globalRepairStageValue T n - (1 : ℝ) / 2| ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  apply abs_localMersennePrefixValue_sub_half_le hn
  · intro d hd
    exact ⟨(mem_globalRepairStageSupport.mp hd).1,
      (mem_globalRepairStageSupport.mp hd).2.1⟩
  · exact hfeas.2.2.2 n hn

theorem tendsto_nat_succ_div_two_pow_zero :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n)
      atTop (nhds 0) := by
  have hN := tendsto_pow_const_div_const_pow_of_one_lt 1
    (by norm_num : (1 : ℝ) < 2)
  have hOne := tendsto_pow_const_div_const_pow_of_one_lt 0
    (by norm_num : (1 : ℝ) < 2)
  have hsum := hN.add hOne
  have hfun :
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) =
        (fun n : ℕ ↦ (n : ℝ) ^ 1 / (2 : ℝ) ^ n +
          (n : ℝ) ^ 0 / (2 : ℝ) ^ n) := by
    funext n
    push_cast
    simp only [pow_one, pow_zero]
    ring
  rw [hfun]
  simpa using hsum

theorem globalRepairStageValue_tendsto_half
    (T : BooleanMobiusGlobalRepairTrajectory)
    (hfeas : GlobalBooleanMobiusRepairFeasible T) :
    Tendsto (globalRepairStageValue T) atTop (nhds ((1 : ℝ) / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have habs : Tendsto
      (fun n : ℕ ↦ |globalRepairStageValue T n - (1 : ℝ) / 2|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n ↦ abs_nonneg _
    · filter_upwards [eventually_ge_atTop 2] with n hn
      exact abs_globalRepairStageValue_sub_half_le T hfeas hn
    · exact tendsto_nat_succ_div_two_pow_zero
  simpa [Real.norm_eq_abs] using habs

/-! ## The row limit is the frozen support value -/

theorem globalRepair_prefix_indicator_eq
    (T : BooleanMobiusGlobalRepairTrajectory) {n R : ℕ}
    (hR : R ≤ n / 2) :
    (∑ k ∈ Finset.range R,
        Set.indicator (globalRepairLimitSupport T) mersenneWeight (k + 1)) =
      ∑ k ∈ Finset.range R,
        Set.indicator
          (↑(globalRepairStageSupport T.bit n) : Set ℕ)
          mersenneWeight (k + 1) := by
  apply Finset.sum_congr rfl
  intro k hk
  have hkR : k + 1 ≤ R := by
    have := Finset.mem_range.mp hk
    omega
  have hagree := globalRepairStageSupport_agrees_limit_of_le_half
    T (n := n) (d := k + 1) (hkR.trans hR)
  by_cases hmem : k + 1 ∈ globalRepairLimitSupport T
  · have hstage : k + 1 ∈ globalRepairStageSupport T.bit n :=
      hagree.mpr hmem
    simp [hmem, hstage]
  · have hstage : k + 1 ∉ globalRepairStageSupport T.bit n := by
      exact fun hs ↦ hmem (hagree.mp hs)
    simp [hmem, hstage]

/-- Coordinate agreement through `R` bounds the discrepancy of the two
support values by two complete Mersenne tails. -/
theorem abs_globalRepairLimitValue_sub_stageValue_le_tail
    (T : BooleanMobiusGlobalRepairTrajectory) {n R : ℕ}
    (hR : R ≤ n / 2) :
    |positiveMersenneSupportValue (globalRepairLimitSupport T) -
        globalRepairStageValue T n| ≤ 2 * mersenneTail R := by
  let F := globalRepairStageSupport T.bit n
  have hstageValue :
      positiveMersenneSupportValue (↑F : Set ℕ) =
        globalRepairStageValue T n := by
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    simp [globalRepairStageValue, F,
      localMersennePrefixValue_eq_finiteErdosSum]
  rw [← hstageValue,
    positiveMersenneSupportValue_eq_prefix_add_suffix
      (globalRepairLimitSupport T) R,
    positiveMersenneSupportValue_eq_prefix_add_suffix (↑F : Set ℕ) R]
  rw [globalRepair_prefix_indicator_eq T hR]
  have hlimNonneg := positiveMersenneSupportSuffix_nonneg
    (globalRepairLimitSupport T) R
  have hfinNonneg := positiveMersenneSupportSuffix_nonneg (↑F : Set ℕ) R
  calc
    |(∑ k ∈ Finset.range R,
          Set.indicator (↑F : Set ℕ) mersenneWeight (k + 1) +
          positiveMersenneSupportSuffix (globalRepairLimitSupport T) R) -
        ((∑ k ∈ Finset.range R,
          Set.indicator (↑F : Set ℕ) mersenneWeight (k + 1)) +
          positiveMersenneSupportSuffix (↑F : Set ℕ) R)| =
        |positiveMersenneSupportSuffix (globalRepairLimitSupport T) R -
          positiveMersenneSupportSuffix (↑F : Set ℕ) R| := by ring_nf
    _ ≤ |positiveMersenneSupportSuffix (globalRepairLimitSupport T) R| +
          |positiveMersenneSupportSuffix (↑F : Set ℕ) R| := abs_sub _ _
    _ = positiveMersenneSupportSuffix (globalRepairLimitSupport T) R +
          positiveMersenneSupportSuffix (↑F : Set ℕ) R := by
          rw [abs_of_nonneg hlimNonneg, abs_of_nonneg hfinNonneg]
    _ ≤ mersenneTail R + mersenneTail R :=
      add_le_add
        (positiveMersenneSupportSuffix_le_tail
          (globalRepairLimitSupport T) R)
        (positiveMersenneSupportSuffix_le_tail (↑F : Set ℕ) R)
    _ = 2 * mersenneTail R := by ring

theorem globalRepairEvenStageValue_tendsto_limit
    (T : BooleanMobiusGlobalRepairTrajectory) :
    Tendsto (fun R : ℕ ↦ globalRepairStageValue T (2 * R))
      atTop (nhds (positiveMersenneSupportValue
        (globalRepairLimitSupport T))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have habs : Tendsto
      (fun R : ℕ ↦
        |globalRepairStageValue T (2 * R) -
          positiveMersenneSupportValue (globalRepairLimitSupport T)|)
      atTop (nhds 0) := by
    have hnonneg : ∀ᶠ R : ℕ in atTop,
        0 ≤ |globalRepairStageValue T (2 * R) -
          positiveMersenneSupportValue (globalRepairLimitSupport T)| :=
      Filter.Eventually.of_forall fun R ↦ abs_nonneg _
    have hbound : ∀ᶠ R : ℕ in atTop,
        |globalRepairStageValue T (2 * R) -
          positiveMersenneSupportValue (globalRepairLimitSupport T)| ≤
            2 * mersenneTail R :=
      Filter.Eventually.of_forall fun R ↦ by
        simpa [abs_sub_comm] using
          (abs_globalRepairLimitValue_sub_stageValue_le_tail
            T (n := 2 * R) (R := R) (by omega))
    exact squeeze_zero' hnonneg hbound
      (by simpa using tendsto_mersenneTail_zero.const_mul 2)
  simpa [Real.norm_eq_abs] using habs

/-! ## Conditional counterexample endpoint -/

/-- A globally feasible endpoint repair trajectory produces an infinite
Mersenne support of exact value `1/2`.  This is a conditional counterexample
to the universal assertion in Erdős #257; the hypothesis remains open. -/
theorem infinite_support_half_of_globalBooleanMobiusRepair
    (T : BooleanMobiusGlobalRepairTrajectory)
    (hfeas : GlobalBooleanMobiusRepairFeasible T) :
    (globalRepairLimitSupport T).Infinite ∧
      erdosSupportSeries 2 (globalRepairLimitSupport T) = (1 : ℝ) / 2 := by
  have hhalfStages :=
    (globalRepairStageValue_tendsto_half T hfeas).comp (by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop b] with R hR
      omega : Tendsto (fun R : ℕ ↦ 2 * R) atTop atTop)
  have hlimitStages := globalRepairEvenStageValue_tendsto_limit T
  have hvalue : positiveMersenneSupportValue
      (globalRepairLimitSupport T) = (1 : ℝ) / 2 :=
    tendsto_nhds_unique hlimitStages hhalfStages
  have hseries : erdosSupportSeries 2 (globalRepairLimitSupport T) =
      (1 : ℝ) / 2 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue
  refine ⟨?_, hseries⟩
  intro hfinite
  exact HalfCarryReachability.finite_boolSupport_ne_half
    (globalRepairLimitSupport T) hfinite
    (zero_not_mem_globalRepairLimitSupport T) hseries

end Erdos257PeriodNoncollapse
