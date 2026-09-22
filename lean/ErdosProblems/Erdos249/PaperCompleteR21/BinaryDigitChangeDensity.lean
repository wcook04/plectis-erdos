import ErdosProblems.Erdos249.TotientStrictPrimeEscape

/-! Paper-form restatement of `cor:digitform`, the digit version of the
analytic condition for Erdős #249.

With `α_h = (2^h-1)S` and `ρ_h(X)` the proportion of `N ∈ [X,2X)` whose phase
`2^N α_h` is at distance at least `1/4` from every integer:

* if for every `h ≥ 1` there are cofinally many `X` with `ρ_h(X) ≥ 11/100`,
  then `S` is irrational;
* for nondyadic `α_h`, the condition counted by `ρ_h(X)` is exactly a change
  between binary digits `N+1` and `N+2` of `α_h`;
* hence the same hypothesis asks for at least `11X/100` such digit changes on
  arbitrarily large blocks `X ≤ N < 2X`, for every `h`. -/
open scoped Classical

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller

/-- `α_h = (2^h - 1) S`. -/
noncomputable def totientAlphaShift (h : ℕ) : ℝ :=
  ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)

/-- `‖x‖_{ℝ/ℤ} ≥ 1/4`, written as: every integer is at distance at least
`1/4` from `x`. -/
def QuarterFarFromInt (x : ℝ) : Prop := ∀ k : ℤ, (1 / 4 : ℝ) ≤ |x - (k : ℝ)|

/-- `x` is nondyadic. -/
def NotDyadicRational (x : ℝ) : Prop := ∀ (m : ℤ) (j : ℕ), x ≠ (m : ℝ) / 2 ^ j

/-- The `k`-th binary digit of `x`. -/
noncomputable def binaryDigitAt (x : ℝ) (k : ℕ) : ℤ := ⌊(2 : ℝ) ^ k * x⌋ % 2

/-- The number of `N ∈ [X, 2X)` with `‖2^N α_h‖_{ℝ/ℤ} ≥ 1/4`. -/
noncomputable def quarterFarPhaseCount (h X : ℕ) : ℕ :=
  ((Finset.Ico X (2 * X)).filter fun N => QuarterFarFromInt ((2 : ℝ) ^ N * totientAlphaShift h)).card

/-- `ρ_h(X)`: the proportion of `N ∈ [X,2X)` with `‖2^N α_h‖_{ℝ/ℤ} ≥ 1/4`. -/
noncomputable def quarterFarPhaseProportion (h X : ℕ) : ℝ := (quarterFarPhaseCount h X : ℝ) / (X : ℝ)

/-! ### The distance condition in terms of the fractional part -/

theorem quarterFarFromInt_iff_floor_bounds (x : ℝ) :
    QuarterFarFromInt x ↔ (1 / 4 : ℝ) ≤ x - (⌊x⌋ : ℝ) ∧ x - (⌊x⌋ : ℝ) ≤ 3 / 4 := by
  have hfl := Int.floor_le x
  have hfl2 := Int.lt_floor_add_one x
  constructor
  · intro hx
    have h1 := hx ⌊x⌋
    have h2 := hx (⌊x⌋ + 1)
    rw [abs_of_nonneg (by linarith)] at h1
    have hcast : (((⌊x⌋ + 1 : ℤ)) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) + 1 := by push_cast; ring
    rw [hcast, abs_of_nonpos (by linarith)] at h2
    exact ⟨h1, by linarith⟩
  · rintro ⟨ha, hb⟩ k
    by_cases hk : k ≤ ⌊x⌋
    · have hkR : ((k : ℤ) : ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast hk
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hkR : ((⌊x⌋ : ℤ) : ℝ) + 1 ≤ ((k : ℤ) : ℝ) := by
        have hstep : (⌊x⌋ : ℤ) + 1 ≤ k := by omega
        exact_mod_cast hstep
      rw [abs_of_nonpos (by linarith)]
      linarith

/-- A phase at distance at least `1/4` from every integer has nonpositive
cosine. -/
theorem cos_nonpos_of_quarterFarFromInt {x : ℝ} (hx : QuarterFarFromInt x) :
    Real.cos (2 * Real.pi * x) ≤ 0 := by
  obtain ⟨ha, hb⟩ := (quarterFarFromInt_iff_floor_bounds x).mp hx
  have hsplit : 2 * Real.pi * x
      = 2 * Real.pi * (x - ((⌊x⌋ : ℤ) : ℝ)) + ((⌊x⌋ : ℤ) : ℝ) * (2 * Real.pi) := by ring
  rw [hsplit, Real.cos_add_int_mul_two_pi]
  refine Real.cos_nonpos_of_pi_div_two_le_of_le ?_ ?_
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- The real part of the tail-orbit phase is the cosine of the scaled orbit. -/
theorem tailOrbitFirstExp_re_eq (h N : ℕ) :
    (tailOrbitFirstExp h N).re = Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * totientAlphaShift h)) := by
  rw [tailOrbitFirstExp_eq_scaledTotientSeriesFirstExp, scaledTotientSeriesFirstExp,
    Complex.exp_ofReal_mul_I_re]
  congr 1
  unfold totientAlphaShift
  ring

/-! ### `cor:digitform`, the analytic half -/

/-- **A digit version of the analytic condition (count form).**  If for every
`h ≥ 1` there are cofinally many `X` with at least `11X/100` indices
`N ∈ [X,2X)` whose phase `2^N α_h` is `1/4`-far from `ℤ`, then `S` is
irrational. -/
theorem irrational_totientSeries_of_quarterFarPhase_count
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤ (quarterFarPhaseCount h X : ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply ErdosProblems.Erdos249.irrational_totient_series_of_tailOrbitBlockGap
  apply ErdosProblems.Erdos249.tailOrbitBlockGap_of_nonpositiveBlockDensity
  intro h hh X₀
  obtain ⟨X, hX, hcount⟩ := hdense h hh X₀
  refine ⟨X, hX, ?_⟩
  have hsubset :
      ((Finset.Ico X (2 * X)).filter fun N => QuarterFarFromInt ((2 : ℝ) ^ N * totientAlphaShift h))
        ⊆ ((Finset.Ico X (2 * X)).filter fun N => (tailOrbitFirstExp h N).re ≤ 0) := by
    intro N hN
    rw [Finset.mem_filter] at hN ⊢
    refine ⟨hN.1, ?_⟩
    rw [tailOrbitFirstExp_re_eq]
    exact cos_nonpos_of_quarterFarFromInt hN.2
  have hcard := Finset.card_le_card hsubset
  have hcardR : (quarterFarPhaseCount h X : ℝ)
      ≤ ((((Finset.Ico X (2 * X)).filter fun N => (tailOrbitFirstExp h N).re ≤ 0).card : ℕ) : ℝ) := by
    unfold quarterFarPhaseCount
    exact Nat.cast_le.mpr hcard
  linarith

/-- **A digit version of the analytic condition.**  If for every `h ≥ 1` there
are cofinally many `X` with `ρ_h(X) ≥ 11/100`, then `S` is irrational. -/
theorem irrational_totientSeries_of_quarterFarPhase_proportion
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) ≤ quarterFarPhaseProportion h X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totientSeries_of_quarterFarPhase_count
  intro h hh X₀
  obtain ⟨X, hX, hr⟩ := hdense h hh X₀
  refine ⟨X, hX, ?_⟩
  have hXpos : 0 < X :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right X₀ 1) hX)
  have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXR
  have h1 : (11 / 100 : ℝ) * X ≤ quarterFarPhaseProportion h X * X :=
    mul_le_mul_of_nonneg_right hr (le_of_lt hXR)
  have h2 : quarterFarPhaseProportion h X * X = (quarterFarPhaseCount h X : ℝ) := by
    unfold quarterFarPhaseProportion
    field_simp
  rw [h2] at h1
  exact h1

/-! ### `cor:digitform`, the digit half -/

/-- **The `1/4`-far condition is a binary digit change.**  For nondyadic `α`,
`‖2^N α‖_{ℝ/ℤ} ≥ 1/4` holds exactly when the binary digits `N+1` and `N+2` of
`α` differ. -/
theorem quarterFarFromInt_iff_binaryDigitAt_change {α : ℝ} (hnd : NotDyadicRational α) (N : ℕ) :
    QuarterFarFromInt ((2 : ℝ) ^ N * α) ↔ binaryDigitAt α (N + 1) ≠ binaryDigitAt α (N + 2) := by
  set y : ℝ := (2 : ℝ) ^ N * α with hy
  set n : ℤ := ⌊y⌋ with hn
  set f : ℝ := y - (n : ℝ) with hf
  have hf0 : 0 ≤ f := by rw [hf, hn]; linarith [Int.floor_le y]
  have hf1 : f < 1 := by rw [hf, hn]; linarith [Int.lt_floor_add_one y]
  have hd1 : binaryDigitAt α (N + 1) = ⌊2 * f⌋ % 2 := by
    have hp : (2 : ℝ) ^ (N + 1) * α = 2 * f + ((2 * n : ℤ) : ℝ) := by
      rw [hf, hy]; push_cast; ring
    simp only [binaryDigitAt]
    rw [hp, Int.floor_add_intCast]
    omega
  have hd2 : binaryDigitAt α (N + 2) = ⌊4 * f⌋ % 2 := by
    have hp : (2 : ℝ) ^ (N + 2) * α = 4 * f + ((4 * n : ℤ) : ℝ) := by
      rw [hf, hy]; push_cast; ring
    simp only [binaryDigitAt]
    rw [hp, Int.floor_add_intCast]
    omega
  have hfract : QuarterFarFromInt y ↔ (1 / 4 : ℝ) ≤ f ∧ f ≤ 3 / 4 := by
    have hbase := quarterFarFromInt_iff_floor_bounds y
    rw [← hn, ← hf] at hbase
    exact hbase
  have hne34 : f ≠ 3 / 4 := by
    intro h34
    have h' : y - (n : ℝ) = 3 / 4 := by rw [← hf]; exact h34
    rw [hy] at h'
    have hyval : (2 : ℝ) ^ N * α = (n : ℝ) + 3 / 4 := by linarith
    apply hnd (4 * n + 3) (N + 2)
    have hne : ((2 : ℝ) ^ (N + 2)) ≠ 0 := by positivity
    rw [eq_div_iff hne]
    push_cast
    have hpow : ((2 : ℝ) ^ (N + 2)) = 4 * (2 : ℝ) ^ N := by ring
    rw [hpow]
    linear_combination 4 * hyval
  rw [hd1, hd2, hfract]
  constructor
  · rintro ⟨ha, hb⟩
    have hblt : f < 3 / 4 := lt_of_le_of_ne hb hne34
    by_cases hc : f < 1 / 2
    · have e1 : ⌊2 * f⌋ = 0 := by
        rw [Int.floor_eq_iff]
        exact ⟨by push_cast; linarith, by push_cast; linarith⟩
      have e2 : ⌊4 * f⌋ = 1 := by
        rw [Int.floor_eq_iff]
        exact ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [e1, e2]
      decide
    · have hc' : 1 / 2 ≤ f := not_lt.mp hc
      have e1 : ⌊2 * f⌋ = 1 := by
        rw [Int.floor_eq_iff]
        exact ⟨by push_cast; linarith, by push_cast; linarith⟩
      have e2 : ⌊4 * f⌋ = 2 := by
        rw [Int.floor_eq_iff]
        exact ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [e1, e2]
      decide
  · intro hne
    by_contra hcon
    rw [not_and_or, not_le, not_le] at hcon
    by_cases hc : f < 1 / 4
    · have e1 : ⌊2 * f⌋ = 0 := by
        rw [Int.floor_eq_iff]
        exact ⟨by push_cast; linarith, by push_cast; linarith⟩
      have e2 : ⌊4 * f⌋ = 0 := by
        rw [Int.floor_eq_iff]
        exact ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [e1, e2] at hne
      exact hne rfl
    · have hge : 1 / 4 ≤ f := not_lt.mp hc
      have hgt : 3 / 4 < f := by
        rcases hcon with hbad | hgood
        · exact absurd hbad hc
        · exact hgood
      have e1 : ⌊2 * f⌋ = 1 := by
        rw [Int.floor_eq_iff]
        exact ⟨by push_cast; linarith, by push_cast; linarith⟩
      have e2 : ⌊4 * f⌋ = 3 := by
        rw [Int.floor_eq_iff]
        exact ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [e1, e2] at hne
      exact hne (by decide)

/-- **The hypothesis read as a digit-change count.**  When every `α_h` is
nondyadic, at least `11X/100` binary digit changes between positions `N+1` and
`N+2`, counted over `X ≤ N < 2X` on arbitrarily large blocks and for every
`h ≥ 1`, implies that `S` is irrational. -/
theorem irrational_totientSeries_of_digitChange_count
    (hnd : ∀ h : ℕ, 1 ≤ h → NotDyadicRational (totientAlphaShift h))
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤
        ((((Finset.Ico X (2 * X)).filter
            fun N => binaryDigitAt (totientAlphaShift h) (N + 1)
              ≠ binaryDigitAt (totientAlphaShift h) (N + 2)).card : ℕ) : ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totientSeries_of_quarterFarPhase_count
  intro h hh X₀
  obtain ⟨X, hX, hcount⟩ := hdense h hh X₀
  refine ⟨X, hX, ?_⟩
  have hfilter :
      ((Finset.Ico X (2 * X)).filter fun N => QuarterFarFromInt ((2 : ℝ) ^ N * totientAlphaShift h))
        = ((Finset.Ico X (2 * X)).filter
            fun N => binaryDigitAt (totientAlphaShift h) (N + 1) ≠ binaryDigitAt (totientAlphaShift h) (N + 2)) := by
    apply Finset.filter_congr
    intro N _
    exact quarterFarFromInt_iff_binaryDigitAt_change (hnd h hh) N
  unfold quarterFarPhaseCount
  rw [hfilter]
  exact hcount

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.quarterFarFromInt_iff_floor_bounds
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.cos_nonpos_of_quarterFarFromInt
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.tailOrbitFirstExp_re_eq
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_count
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_proportion
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.quarterFarFromInt_iff_binaryDigitAt_change
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_digitChange_count
