import ErdosProblems.Erdos68.PrimeZeroBranch
import ErdosProblems.Erdos68.GapScalarNormalForm

/-!
# Erdős #68: the conditional odd-threshold producer interface

The eventual odd-index threshold below is a conjectural hypothesis.  This file
does not assert it or record a finite computation as evidence for an eventual
statement.  It kernel-checks the exact target composition and separates the
two arithmetic obligations hidden by the rounding digit notation:

* the carry is at least one (equivalently the digit `D_m = carry - 1` is not
  `-1`), and
* at a unit carry, the successor predecessor-gap is at least `2 / m`.

The second clause is essential: excluding `D_m = -1` alone does not control
the thin `D_m = 0` threshold boundary.
-/

namespace ErdosProblems.Erdos68

/-- A positive carry meets the tail-free threshold automatically unless it is
exactly one; in that boundary case the displayed successor-gap estimate is
the precise remaining input supplied by the affine gap recurrence. -/
theorem predecessorGap_threshold_of_carry_ge_one_and_unit_successor_gap
    {m : ℕ} (hm : 3 ≤ m)
    (hcarry : (1 : ℤ) ≤ factorialGapStepCarry m)
    (hunit : factorialGapStepCarry m = 1 →
      2 / (m : ℝ) ≤ factorialGapPredecessorGap (m + 1)) :
    1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
      (m : ℝ) * factorialGapPredecessorGap m := by
  have hrec := predGap_succ_eq m (by omega)
  by_cases hc : factorialGapStepCarry m = 1
  · have hnext := hunit hc
    rw [hc] at hrec
    push_cast at hrec
    linarith
  · have hcTwo : (2 : ℤ) ≤ factorialGapStepCarry m := by omega
    have hcTwoR : (2 : ℝ) ≤ (factorialGapStepCarry m : ℝ) := by
      exact_mod_cast hcTwo
    have hnextPos := (factorialGapPredecessorGap_pos_le_one (m + 1)).1
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 2 ≤ m by omega)
    have hmPos : (0 : ℝ) < (m : ℝ) := by positivity
    have hdiv : 2 / (m : ℝ) ≤ 1 := (div_le_one hmPos).2 hmR
    linarith

/-- A purely discrete sufficient version of the preceding lemma.  At a unit
carry, a next carry of at least three forces the required successor-gap
margin. -/
theorem predecessorGap_threshold_of_carry_ge_one_and_unit_next_carry_ge_three
    {m : ℕ} (hm : 3 ≤ m)
    (hcarry : (1 : ℤ) ≤ factorialGapStepCarry m)
    (hnext : factorialGapStepCarry m = 1 →
      (3 : ℤ) ≤ factorialGapStepCarry (m + 1)) :
    1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
      (m : ℝ) * factorialGapPredecessorGap m := by
  apply predecessorGap_threshold_of_carry_ge_one_and_unit_successor_gap
    hm hcarry
  intro hunit
  have hnextThree := hnext hunit
  have hnextThreeR :
      (3 : ℝ) ≤ (factorialGapStepCarry (m + 1) : ℝ) := by
    exact_mod_cast hnextThree
  have hsplit := predGap_split (m + 1) (by omega)
  have hdenPos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hepsPos :
      0 < 1 / (((m + 1).factorial : ℝ) - 1) := by
    have hfac : (1 : ℝ) < ((m + 1).factorial : ℕ) := by
      exact_mod_cast Nat.one_lt_factorial.mpr (show 2 ≤ m + 1 by omega)
    exact one_div_pos.mpr (sub_pos.mpr hfac)
  have htailPos := (factorialGapPredecessorGap_pos_le_one (m + 2)).1
  have hfirst :
      3 / ((m + 1 : ℕ) : ℝ) ≤
        ((factorialGapStepCarry (m + 1) : ℝ) +
            1 / (((m + 1).factorial : ℝ) - 1)) /
          ((m + 1 : ℕ) : ℝ) := by
    apply (div_le_div_iff_of_pos_right hdenPos).2
    linarith
  have hgap :
      3 / ((m + 1 : ℕ) : ℝ) ≤
        factorialGapPredecessorGap (m + 1) := by
    rw [hsplit]
    have htailNonneg :
        0 ≤ factorialGapPredecessorGap (m + 2) / ((m + 1 : ℕ) : ℝ) := by
      positivity
    linarith
  have hmPos : (0 : ℝ) < (m : ℝ) := by positivity
  have hm1Pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hratio :
      2 / (m : ℝ) ≤ 3 / ((m + 1 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hmPos hm1Pos]
    have hmThreeR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    push_cast
    nlinarith
  exact hratio.trans hgap

/-- The combined odd-index threshold conjecture is already a complete
irrationality producer.  No prime-number theorem or Euclid step is needed:
odd indices themselves are cofinal. -/
theorem irrational_factorialGapSeries_of_eventual_odd_threshold
    (hodd : ∀ m : ℕ, 25 ≤ m → Odd m →
      1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
        (m : ℝ) * factorialGapPredecessorGap m) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply irrational_factorialGapSeries_of_cofinal_predecessorGap_threshold
  intro B
  let k := max (B + 1) 25
  let m := 2 * k + 1
  refine ⟨m, by omega, by omega, hodd m (by omega) ?_⟩
  exact ⟨k, rfl⟩

/-- Two-obligation form of the computationally suggested producer: an
eventual positive carry at odd indices, plus control of every unit-carry
successor gap there, proves Erdős #68. -/
theorem irrational_factorialGapSeries_of_eventual_odd_carry_margin
    (hcarry : ∀ m : ℕ, 25 ≤ m → Odd m →
      (1 : ℤ) ≤ factorialGapStepCarry m)
    (hunit : ∀ m : ℕ, 25 ≤ m → Odd m →
      factorialGapStepCarry m = 1 →
        2 / (m : ℝ) ≤ factorialGapPredecessorGap (m + 1)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply irrational_factorialGapSeries_of_eventual_odd_threshold
  intro m hm hmodd
  exact predecessorGap_threshold_of_carry_ge_one_and_unit_successor_gap
    (by omega) (hcarry m hm hmodd) (hunit m hm hmodd)

/-- Fully integer-valued adjacent-carry producer suggested by the computation.
It is stronger than necessary but removes the remaining real margin. -/
theorem irrational_factorialGapSeries_of_eventual_odd_two_carry_pattern
    (hcarry : ∀ m : ℕ, 25 ≤ m → Odd m →
      (1 : ℤ) ≤ factorialGapStepCarry m)
    (hnext : ∀ m : ℕ, 25 ≤ m → Odd m →
      factorialGapStepCarry m = 1 →
        (3 : ℤ) ≤ factorialGapStepCarry (m + 1)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply irrational_factorialGapSeries_of_eventual_odd_threshold
  intro m hm hmodd
  exact
    predecessorGap_threshold_of_carry_ge_one_and_unit_next_carry_ge_three
      (by omega) (hcarry m hm hmodd) (hnext m hm hmodd)

/-- **Target-aligned adjacent-carry producer.**  The positive-carry clause in
the preceding threshold route is unnecessary for irrationality itself.  At
each sufficiently large odd index, a non-unit current carry is already a
frontier miss; if the current carry is unit, it is enough that the successor
carry is non-unit.  Thus eventual exclusion of adjacent unit carries on odd
starts directly proves Erdős #68. -/
theorem irrational_factorialGapSeries_of_eventual_odd_unit_carry_break
    (hbreak : ∀ m : ℕ, 25 ≤ m → Odd m →
      factorialGapStepCarry m = 1 →
        factorialGapStepCarry (m + 1) ≠ 1) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  rw [irrational_factorialGapSeries_iff_cofinal_nonunit_carries]
  intro B
  let k := max (B + 1) 25
  let m := 2 * k + 1
  have hm25 : 25 ≤ m := by dsimp [m, k]; omega
  have hmB : B < m := by dsimp [m, k]; omega
  have hmodd : Odd m := ⟨k, rfl⟩
  by_cases hunit : factorialGapStepCarry m = 1
  · exact ⟨m + 1, by omega, hbreak m hm25 hmodd hunit⟩
  · exact ⟨m, hmB, hunit⟩

/-- **Exact sparse odd-pair characterization.**  Uniform exclusion at every
large odd start is stronger than necessary.  Erdős #68 is equivalent to
cofinally many odd-start pairs in which at least one of the two carries is
non-unit.  Thus a proof may select a sparse arithmetic subsequence of odd
starts instead of controlling all odd indices. -/
theorem irrational_factorialGapSeries_iff_cofinal_odd_unit_carry_break :
    Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧ Odd m ∧
          (factorialGapStepCarry m ≠ 1 ∨
            factorialGapStepCarry (m + 1) ≠ 1) := by
  rw [irrational_factorialGapSeries_iff_cofinal_nonunit_carries]
  constructor
  · intro h B
    obtain ⟨k, hkLarge, hkNonunit⟩ := h (B + 2)
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hjPos : 0 < j := by omega
      let m := 2 * (j - 1) + 1
      have hmSucc : m + 1 = k := by dsimp [m]; omega
      refine ⟨m, by dsimp [m]; omega, ⟨j - 1, rfl⟩, ?_⟩
      exact Or.inr (by simpa [hmSucc] using hkNonunit)
    · refine ⟨k, by omega, ⟨j, hj⟩, Or.inl hkNonunit⟩
  · intro h B
    obtain ⟨m, hmLarge, hmOdd, hbreak⟩ := h B
    rcases hbreak with hmNonunit | hnextNonunit
    · exact ⟨m, hmLarge, hmNonunit⟩
    · exact ⟨m + 1, by omega, hnextNonunit⟩

/-- Two adjacent unit carries are a single product-divisibility event at the
later strict successor.  This is the arithmetic form of the no-repeat target:
one must rule out divisibility by `m(m+1)`, rather than separately reason
about two rounding windows. -/
theorem consecutive_unit_carries_iff_mul_dvd_strictSuccessor
    {m : ℕ} (hm : 3 ≤ m) :
    (factorialGapStepCarry m = 1 ∧
        factorialGapStepCarry (m + 1) = 1) ↔
      ((m : ℤ) * (m + 1 : ℤ)) ∣
        strictFacTopRat (factorialGapPrefix (m + 1)) (m + 1) := by
  have hmNext : 3 ≤ m + 1 := by omega
  have hrec := strictFacTop_factorialGapPrefix_step
    (m := m + 1) (show 2 ≤ m + 1 by omega)
  rw [strictFacTop_ratCast, strictFacTop_ratCast] at hrec
  simp only [Nat.add_sub_cancel] at hrec
  push_cast at hrec
  constructor
  · rintro ⟨hunit, hnextUnit⟩
    have hmDvd :=
      (factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat hm).mp hunit
    obtain ⟨z, hz⟩ := hmDvd
    refine ⟨z, ?_⟩
    rw [hnextUnit] at hrec
    rw [hrec, hz]
    ring
  · intro hprod
    obtain ⟨z, hz⟩ := hprod
    have hnextDvd : (m + 1 : ℤ) ∣
        strictFacTopRat (factorialGapPrefix (m + 1)) (m + 1) := by
      refine ⟨(m : ℤ) * z, ?_⟩
      rw [hz]
      ring
    have hnextUnit :=
      (factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat hmNext).mpr
        hnextDvd
    have hrecUnit := hrec
    rw [hnextUnit] at hrecUnit
    norm_num at hrecUnit
    have hcancel :
        (m + 1 : ℤ) *
            strictFacTopRat (factorialGapPrefix m) m =
          (m + 1 : ℤ) * ((m : ℤ) * z) := by
      calc
        (m + 1 : ℤ) * strictFacTopRat (factorialGapPrefix m) m =
            strictFacTopRat (factorialGapPrefix (m + 1)) (m + 1) :=
          hrecUnit.symm
        _ = (m : ℤ) * (m + 1 : ℤ) * z := hz
        _ = (m + 1 : ℤ) * ((m : ℤ) * z) := by ring
    have hnonzero : (m + 1 : ℤ) ≠ 0 := by positivity
    have hmEq : strictFacTopRat (factorialGapPrefix m) m =
        (m : ℤ) * z := mul_left_cancel₀ hnonzero hcancel
    have hmDvd : (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m :=
      ⟨z, hmEq⟩
    exact ⟨(factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat hm).mpr hmDvd,
      hnextUnit⟩

/-- **Exact adjacent-unit ultra-cylinder classification.**  Two consecutive
unit carries force the single earlier canonical remainder into one of two
endpoint cylinders of width on the order of `m⁻³`.  The lower cylinder is
pulled back from zero through two factorial digits, while the upper cylinder
is its maximal-digit reflection. -/
theorem consecutive_unit_carries_iff_ultra_endpoint_cylinders
    {m : ℕ} (hm : 3 ≤ m) :
    (factorialGapStepCarry m = 1 ∧
        factorialGapStepCarry (m + 1) = 1) ↔
      ((m : ℝ) * (m + 1 : ℝ) *
            canonicalRemainder
              _root_.Erdos68.factorialGapSeries (m - 1) <
          factorialGapScaledTail (m + 1)) ∨
        ((m : ℝ) * (m + 1 : ℝ) - 1 +
              factorialGapScaledTail (m + 1) ≤
            (m : ℝ) * (m + 1 : ℝ) *
              canonicalRemainder
                _root_.Erdos68.factorialGapSeries (m - 1)) := by
  let S : ℝ := _root_.Erdos68.factorialGapSeries
  have hsucc : m - 1 + 1 = m := by omega
  have hcastSucc : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    exact_mod_cast hsucc
  have hrecM := canonicalRemainder_recurrence S (m - 1)
  rw [hsucc, hcastSucc] at hrecM
  have hrecNext := canonicalRemainder_recurrence S m
  dsimp [S] at hrecM hrecNext
  constructor
  · rintro ⟨hmUnit, hnextUnit⟩
    have hmBranch :=
      (factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch hm).mp
        hmUnit
    have hnextBranch :=
      (factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch
        (m := m + 1) (by omega)).mp hnextUnit
    simp only [Nat.add_sub_cancel] at hnextBranch
    rcases hmBranch with hmZero | hmMax
    · rcases hmZero with ⟨hdm, _hprev, hmFlag⟩
      rcases hnextBranch with hnextZero | hnextMax
      · left
        rcases hnextZero with ⟨hdnext, _hmFlag, hnextFlag⟩
        have hnextLt :=
          (factorialGapEndpointFlag_eq_zero_iff (m + 1)).mp hnextFlag
        rw [hdm] at hrecM
        norm_num at hrecM
        rw [hdnext] at hrecNext
        norm_num at hrecNext
        nlinarith
      · exact (by rcases hnextMax with ⟨_, hcontra, _⟩; omega)
    · rcases hmMax with ⟨hdm, _hprev, hmFlag⟩
      rcases hnextBranch with hnextZero | hnextMax
      · exact (by rcases hnextZero with ⟨_, hcontra, _⟩; omega)
      · right
        rcases hnextMax with ⟨hdnext, _hmFlag, hnextFlag⟩
        have hnextGe :=
          (factorialGapEndpointFlag_eq_one_iff (m + 1)).mp hnextFlag
        rw [hdm] at hrecM
        push_cast at hrecM
        rw [hdnext] at hrecNext
        push_cast at hrecNext
        nlinarith
  · intro hcyl
    have htailRec :=
      factorialGapScaledTail_pred_recurrence (m := m + 1) (by omega)
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at htailRec
    rcases hcyl with hlower | hupper
    · have htailLt :
          factorialGapScaledTail (m + 1) <
            (m + 1 : ℝ) * factorialGapScaledTail m := by
        have hepsPos :
            0 < 1 / (((m + 1).factorial : ℝ) - 1) := by
          apply one_div_pos.mpr
          have hfacOne : (1 : ℝ) < ((m + 1).factorial : ℝ) := by
            exact_mod_cast Nat.one_lt_factorial.mpr (by omega : 2 ≤ m + 1)
          linarith
        linarith
      have hfirstLower :
          (m : ℝ) * canonicalRemainder
              _root_.Erdos68.factorialGapSeries (m - 1) <
            factorialGapScaledTail m := by
        have hm1Pos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
        nlinarith
      have hmZero :=
        (factorialGap_zero_branch_iff_lower_endpoint_cylinder hm).mpr
          hfirstLower
      have hnextLower :
          (m + 1 : ℝ) * canonicalRemainder
              _root_.Erdos68.factorialGapSeries m <
            factorialGapScaledTail (m + 1) := by
        rw [hmZero.1] at hrecM
        norm_num at hrecM
        nlinarith
      exact
        ⟨(factorialGapStepCarry_eq_one_iff_endpoint_cylinders hm).mpr
            (Or.inl hfirstLower),
          (factorialGapStepCarry_eq_one_iff_endpoint_cylinders
            (m := m + 1) (by omega)).mpr
              (Or.inl (by
                simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
                  using hnextLower))⟩
    · have hfacGt :
          (2 : ℝ) < ((m + 1).factorial : ℝ) := by
        exact_mod_cast
          (show 2 < (m + 1).factorial by
            have : 6 ≤ (m + 1).factorial := by
              calc
                6 = (3 : ℕ).factorial := by norm_num
                _ ≤ (m + 1).factorial := Nat.factorial_le (by omega)
            omega)
      have hepsLt :
          1 / (((m + 1).factorial : ℝ) - 1) < 1 := by
        apply (div_lt_one (by linarith)).2
        linarith
      have hfirstUpper :
          ((m : ℝ) - 1) + factorialGapScaledTail m ≤
            (m : ℝ) * canonicalRemainder
              _root_.Erdos68.factorialGapSeries (m - 1) := by
        by_contra hnot
        have hbad :
            (m : ℝ) * canonicalRemainder
                _root_.Erdos68.factorialGapSeries (m - 1) <
              ((m : ℝ) - 1) + factorialGapScaledTail m :=
          lt_of_not_ge hnot
        have hm1Pos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
        have hscaledBad := mul_lt_mul_of_pos_left hbad hm1Pos
        have hscaledRhs :
            (m + 1 : ℝ) *
                (((m : ℝ) - 1) + factorialGapScaledTail m) =
              (m : ℝ) * (m : ℝ) +
                1 / (((m + 1).factorial : ℝ) - 1) +
                factorialGapScaledTail (m + 1) := by
          rw [mul_add, htailRec]
          ring
        rw [hscaledRhs] at hscaledBad
        have hmReal : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith
      have hmMax :=
        (factorialGap_maximal_branch_iff_upper_endpoint_cylinder hm).mpr
          hfirstUpper
      have hnextUpper :
          ((m + 1 : ℝ) - 1) + factorialGapScaledTail (m + 1) ≤
            (m + 1 : ℝ) * canonicalRemainder
              _root_.Erdos68.factorialGapSeries m := by
        rw [hmMax.1] at hrecM
        push_cast at hrecM
        nlinarith
      exact
        ⟨(factorialGapStepCarry_eq_one_iff_endpoint_cylinders hm).mpr
            (Or.inr hfirstUpper),
          (factorialGapStepCarry_eq_one_iff_endpoint_cylinders
            (m := m + 1) (by omega)).mpr
              (Or.inr (by
                simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
                  using hnextUpper))⟩

/-- **Exact shrinking-target characterization of Erdős #68.**  Irrationality
is equivalent to cofinal escape, along odd starting indices, from the two
adjacent-unit ultra-cylinders.  This is an exact replacement of the carry
predicate by a two-sided shrinking target for one canonical remainder; it
does not assert that the distinguished orbit escapes. -/
theorem irrational_factorialGapSeries_iff_cofinal_odd_ultra_endpoint_escape :
    Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧ Odd m ∧
          ¬(((m : ℝ) * (m + 1 : ℝ) *
                canonicalRemainder
                  _root_.Erdos68.factorialGapSeries (m - 1) <
              factorialGapScaledTail (m + 1)) ∨
            ((m : ℝ) * (m + 1 : ℝ) - 1 +
                  factorialGapScaledTail (m + 1) ≤
                (m : ℝ) * (m + 1 : ℝ) *
                  canonicalRemainder
                    _root_.Erdos68.factorialGapSeries (m - 1))) := by
  rw [irrational_factorialGapSeries_iff_cofinal_odd_unit_carry_break]
  constructor
  · intro h B
    obtain ⟨m, hmLarge, hmOdd, hbreak⟩ := h (max B 3)
    have hm3 : 3 ≤ m := by omega
    refine ⟨m, by omega, hmOdd, ?_⟩
    intro hcyl
    have hpair :=
      (consecutive_unit_carries_iff_ultra_endpoint_cylinders hm3).mpr
        hcyl
    rcases hbreak with hmNonunit | hnextNonunit
    · exact hmNonunit hpair.1
    · exact hnextNonunit hpair.2
  · intro h B
    obtain ⟨m, hmLarge, hmOdd, hescape⟩ := h (max B 3)
    have hm3 : 3 ≤ m := by omega
    refine ⟨m, by omega, hmOdd, ?_⟩
    by_cases hmUnit : factorialGapStepCarry m = 1
    · right
      intro hnextUnit
      apply hescape
      exact
        (consecutive_unit_carries_iff_ultra_endpoint_cylinders hm3).mp
          ⟨hmUnit, hnextUnit⟩
    · exact Or.inl hmUnit

/-- **Finite rational width-one criterion for an adjacent unit pair.**
After the predecessor-gap recurrence is substituted, the two carry windows
collapse to one interval of exact width one.  Every displayed quantity is
computed from the finite rational prefix through `m - 1`; the full series,
canonical remainder, and infinite tail have disappeared. -/
theorem consecutive_unit_carries_iff_predecessorGap_width_one_window
    {m : ℕ} (hm : 3 ≤ m) :
    (factorialGapStepCarry m = 1 ∧
        factorialGapStepCarry (m + 1) = 1) ↔
      (m : ℝ) + 2 +
            (m + 1 : ℝ) / ((m.factorial : ℝ) - 1) +
            1 / (((m + 1).factorial : ℝ) - 1) <
          (m : ℝ) * (m + 1 : ℝ) *
            factorialGapPredecessorGap m ∧
        (m : ℝ) * (m + 1 : ℝ) *
              factorialGapPredecessorGap m ≤
          (m : ℝ) + 3 +
            (m + 1 : ℝ) / ((m.factorial : ℝ) - 1) +
            1 / (((m + 1).factorial : ℝ) - 1) := by
  have hrec := predGap_succ_eq m (by omega)
  have hmNext : 3 ≤ m + 1 := by omega
  let e : ℝ := 1 / ((m.factorial : ℝ) - 1)
  let enext : ℝ := 1 / (((m + 1).factorial : ℝ) - 1)
  have hquot :
      (m + 1 : ℝ) / ((m.factorial : ℝ) - 1) =
        (m + 1 : ℝ) * e := by
    dsimp [e]
    ring
  rw [hquot]
  change
    (factorialGapStepCarry m = 1 ∧
        factorialGapStepCarry (m + 1) = 1) ↔
      (m : ℝ) + 2 + (m + 1 : ℝ) * e + enext <
          (m : ℝ) * (m + 1 : ℝ) *
            factorialGapPredecessorGap m ∧
        (m : ℝ) * (m + 1 : ℝ) *
              factorialGapPredecessorGap m ≤
          (m : ℝ) + 3 + (m + 1 : ℝ) * e + enext
  change
    factorialGapPredecessorGap (m + 1) =
      (m : ℝ) * factorialGapPredecessorGap m -
        (factorialGapStepCarry m : ℝ) - e at hrec
  constructor
  · rintro ⟨hmUnit, hnextUnit⟩
    have hmWindow :=
      (factorialGapStepCarry_eq_one_iff_scaled_gap m hm).mp hmUnit
    have hnextWindow :=
      (factorialGapStepCarry_eq_one_iff_scaled_gap (m + 1) hmNext).mp
        hnextUnit
    change
      1 + e < (m : ℝ) * factorialGapPredecessorGap m ∧
        (m : ℝ) * factorialGapPredecessorGap m ≤ 2 + e at hmWindow
    simp only [Nat.cast_add, Nat.cast_one] at hnextWindow
    change
      1 + enext < (m + 1 : ℝ) *
          factorialGapPredecessorGap (m + 1) ∧
        (m + 1 : ℝ) * factorialGapPredecessorGap (m + 1) ≤
          2 + enext at hnextWindow
    rw [hmUnit] at hrec
    push_cast at hrec
    constructor <;> nlinarith [hnextWindow.1, hnextWindow.2]
  · rintro ⟨hlower, hupper⟩
    have hfacM : (1 : ℝ) < (m.factorial : ℝ) := by
      exact_mod_cast Nat.one_lt_factorial.mpr (by omega : 2 ≤ m)
    have hfacNext : (2 : ℝ) < ((m + 1).factorial : ℝ) := by
      exact_mod_cast
        (show 2 < (m + 1).factorial by
          have : 6 ≤ (m + 1).factorial := by
            calc
              6 = (3 : ℕ).factorial := by norm_num
              _ ≤ (m + 1).factorial := Nat.factorial_le (by omega)
          omega)
    have hepsMPos : 0 < e := by
      dsimp [e]
      exact one_div_pos.mpr (by linarith)
    have hepsNextPos : 0 < enext := by
      dsimp [enext]
      exact one_div_pos.mpr (by linarith)
    have hepsNextLt : enext < 1 := by
      dsimp [enext]
      apply (div_lt_one (by linarith)).2
      linarith
    have hmReal : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmLower :
        1 + e <
          (m : ℝ) * factorialGapPredecessorGap m := by
      nlinarith [hepsNextPos]
    have hmUpper :
        (m : ℝ) * factorialGapPredecessorGap m ≤
          2 + e := by
      nlinarith [hepsNextLt]
    have hmUnit :=
      (factorialGapStepCarry_eq_one_iff_scaled_gap m hm).mpr
        (by
          change
            1 + e < (m : ℝ) * factorialGapPredecessorGap m ∧
              (m : ℝ) * factorialGapPredecessorGap m ≤ 2 + e
          exact ⟨hmLower, hmUpper⟩)
    have hrecUnit := hrec
    rw [hmUnit] at hrecUnit
    push_cast at hrecUnit
    have hnextLower :
        1 + enext <
          (m + 1 : ℝ) * factorialGapPredecessorGap (m + 1) := by
      nlinarith
    have hnextUpper :
        (m + 1 : ℝ) * factorialGapPredecessorGap (m + 1) ≤
          2 + enext := by
      nlinarith
    exact
      ⟨hmUnit,
        (factorialGapStepCarry_eq_one_iff_scaled_gap (m + 1) hmNext).mpr
          (by
            simp only [Nat.cast_add, Nat.cast_one]
            change
              1 + enext < (m + 1 : ℝ) *
                    factorialGapPredecessorGap (m + 1) ∧
                (m + 1 : ℝ) * factorialGapPredecessorGap (m + 1) ≤
                  2 + enext
            exact ⟨hnextLower, hnextUpper⟩)⟩

/-- **Exact sparse product-divisibility characterization.**  Combining the
odd-pair characterization with the adjacent-carry arithmetic packages the
whole problem as cofinal failure of one explicit product divisibility along
a freely chosen sparse sequence of odd indices. -/
theorem irrational_factorialGapSeries_iff_cofinal_odd_mul_not_dvd :
    Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧ Odd m ∧
          ¬((m : ℤ) * (m + 1 : ℤ)) ∣
            strictFacTopRat (factorialGapPrefix (m + 1)) (m + 1) := by
  rw [irrational_factorialGapSeries_iff_cofinal_odd_unit_carry_break]
  constructor
  · intro h B
    obtain ⟨m, hmLarge, hmOdd, hbreak⟩ := h (max B 3)
    have hm3 : 3 ≤ m := by omega
    refine ⟨m, by omega, hmOdd, ?_⟩
    intro hdvd
    have hpair :=
      (consecutive_unit_carries_iff_mul_dvd_strictSuccessor hm3).mpr hdvd
    rcases hbreak with hmNonunit | hnextNonunit
    · exact hmNonunit hpair.1
    · exact hnextNonunit hpair.2
  · intro h B
    obtain ⟨m, hmLarge, hmOdd, hnotDvd⟩ := h (max B 3)
    have hm3 : 3 ≤ m := by omega
    refine ⟨m, by omega, hmOdd, ?_⟩
    by_cases hmUnit : factorialGapStepCarry m = 1
    · right
      intro hnextUnit
      apply hnotDvd
      exact
        (consecutive_unit_carries_iff_mul_dvd_strictSuccessor hm3).mp
          ⟨hmUnit, hnextUnit⟩
    · exact Or.inl hmUnit

/-- Endpoint consumer aligned with the existing prime block `[p,2p]`:
cofinally many product misses at the odd starts `2p-1` already prove the
problem.  This lets the private-prime/tailored-block machinery target only
the final two carries of each selected block. -/
theorem irrational_factorialGapSeries_of_cofinal_doublePrimeEndpoint_mul_not_dvd
    (hmiss : ∀ B : ℕ, ∃ p : ℕ,
      p.Prime ∧ B < p ∧
        ¬(((2 * p - 1 : ℕ) : ℤ) * ((2 * p : ℕ) : ℤ)) ∣
          strictFacTopRat (factorialGapPrefix (2 * p)) (2 * p)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  rw [irrational_factorialGapSeries_iff_cofinal_odd_mul_not_dvd]
  intro B
  obtain ⟨p, hp, hpLarge, hpMiss⟩ := hmiss B
  let m := 2 * p - 1
  have hpPos : 0 < p := hp.pos
  have hmSucc : m + 1 = 2 * p := by dsimp [m]; omega
  have hmSuccZ : (m : ℤ) + 1 = ((2 * p : ℕ) : ℤ) := by
    exact_mod_cast hmSucc
  refine ⟨m, by dsimp [m]; omega, ?_, ?_⟩
  · refine ⟨p - 1, ?_⟩
    dsimp [m]
    omega
  · rw [hmSucc, hmSuccZ]
    simpa [m] using hpMiss

end ErdosProblems.Erdos68
