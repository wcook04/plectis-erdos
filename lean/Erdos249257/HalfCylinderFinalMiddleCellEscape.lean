import Erdos249257.HalfCylinderFatalGapRightTail
import Erdos249257.HalfCylinderProducerLowerBound

/-!
# The first final-middle cell cannot feed an all-right tail

The final-middle socket has three exceptional integer cells.  This module
isolates the first one.  After completing every rank strictly above the last
false rank, that cell puts the Mobius-centred half carry at zero.  Two more
cofinite coefficient rows are already fatal: the first contains its own
rank, while the second contains both its own rank and its half.  Hence the
centred carry becomes strictly negative, contradicting the analytic
nonnegativity forced by a support value below `1 / 2`.

The first section records the exact two-row recurrence and its finite closed
form.  It is also the natural bookkeeping surface for the two surviving
cells: their future paired incidence charge must stay below the initial
charge `1` or `2` at every finite horizon.
-/

namespace Erdos249257

open Set
open HalfCarryReachability
open HalfCylinderIntegerGreedy
open scoped BigOperators

noncomputable section

/-! ## Paired centred-carry recurrence -/

/-- The two fresh coefficient rows, measured relative to the three units
contributed by the centred recurrence itself. -/
def pairedCenteredForcing (A : Set ℕ) (N : ℕ) : ℤ :=
  2 * (supportCoeff A (N + 2) : ℤ) +
    (supportCoeff A (N + 3) : ℤ) - 3

/-- Two centred half-carry steps combine into one base-four step. -/
theorem mobiusCenteredHalfCarry_add_two
    (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N := by
  rw [show N + 2 = (N + 1) + 1 by omega,
    mobiusCenteredHalfCarry_succ, mobiusCenteredHalfCarry_succ]
  unfold pairedCenteredForcing
  ring

/-- Closed form of the paired recurrence over any finite horizon. -/
theorem mobiusCenteredHalfCarry_add_two_mul
    (A : Set ℕ) (N k : ℕ) :
    mobiusCenteredHalfCarry A (N + 2 * k) =
      (4 : ℤ) ^ k * mobiusCenteredHalfCarry A N -
        ∑ j ∈ Finset.range k,
          (4 : ℤ) ^ (k - 1 - j) * pairedCenteredForcing A (N + 2 * j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show N + 2 * (k + 1) = (N + 2 * k) + 2 by omega,
        mobiusCenteredHalfCarry_add_two, ih, Finset.sum_range_succ,
        pow_succ]
      have hscale :
          4 * (∑ j ∈ Finset.range k,
              (4 : ℤ) ^ (k - 1 - j) *
                pairedCenteredForcing A (N + 2 * j)) =
            ∑ j ∈ Finset.range k,
              (4 : ℤ) ^ (k - j) *
                pairedCenteredForcing A (N + 2 * j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        rw [show k - j = (k - 1 - j) + 1 by omega, pow_succ]
        ring
      have hprefix :
          (∑ j ∈ Finset.range k,
              (4 : ℤ) ^ (k + 1 - 1 - j) *
                pairedCenteredForcing A (N + 2 * j)) =
            4 * (∑ j ∈ Finset.range k,
              (4 : ℤ) ^ (k - 1 - j) *
                pairedCenteredForcing A (N + 2 * j)) := by
        rw [hscale]
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
      rw [hprefix]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      ring

/-! ## Analytic nonnegativity below one half -/

/-- Any support strictly below one half has nonnegative Mobius-centred carry
at every finite level.  The strict support gap makes the integer carry
positive even without a separate positive-tail hypothesis. -/
theorem mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
    (A : Set ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry A N := by
  have hid := integerHalfCarry_eq_scaled_residual_add_tail A hone N
  have hscaled :
      0 < (2 : ℝ) ^ (N + 1) *
        ((1 : ℝ) / 2 - erdosSupportSeries 2 A) := by
    exact mul_pos (by positivity) (sub_pos.mpr hseries)
  have htail :
      0 ≤ binaryCoeffTail (supportCoeff A) (N + 1) :=
    binaryCoeffTail_nonneg _ _
  have hcarryReal : (0 : ℝ) < (integerHalfCarry A N : ℝ) := by
    rw [hid]
    linarith
  have hcarryInt : (0 : ℤ) < integerHalfCarry A N := by
    exact_mod_cast hcarryReal
  unfold mobiusCenteredHalfCarry
  omega

/-! ## The lazy-tail swap at a final false rank

The last-producer argument compares two supports which look unrelated if
they are kept on separate surfaces.  The finite competitor selects `D` and
stops, whereas the lazy endpoint skips `D` and selects every later rank.
At the producer-aligned row these two changes cancel almost completely:
the integer carry changes by exactly four, hence the centred carry changes
by exactly three.  Thus the three middle cells `-3,-2,-1` become the lazy
endpoint charges `0,1,2` respectively.
-/

/-- Divisor membership is the complete local input needed to compare two
support coefficients. -/
private theorem supportCoeff_eq_of_divisorAgreement_local
    (A B : Set ℕ) (n : ℕ)
    (hagree : ∀ d : ℕ, d ∈ n.divisors → (d ∈ A ↔ d ∈ B)) :
    supportCoeff A n = supportCoeff B n := by
  classical
  rw [supportCoeff_eq_card_filter, supportCoeff_eq_card_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter]
  exact and_congr_right fun hd => hagree d hd

/-- Below the last possible double divisor, the only divisor of `n` lying
strictly above `D` is `n` itself. -/
private theorem supportCoeff_union_Ioi_eq_add_one
    (U : Set ℕ) (D n : ℕ) (hD3 : 3 ≤ D)
    (hU : U ⊆ Set.Iio D) (hDn : D < n) (hn : n < 2 * D + 2) :
    supportCoeff (U ∪ Set.Ioi D) n = supportCoeff U n + 1 := by
  have hnU : n ∉ U := by
    intro hmem
    have hlt := hU hmem
    change n < D at hlt
    omega
  rw [supportCoeff_eq_of_divisorAgreement_local
    (U ∪ Set.Ioi D) (insert n U) n]
  · rw [supportCoeff_insert_eq_add_indicator U hnU]
    have hdiv : n ∈ n.divisors :=
      Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
    simp [hdiv]
  · intro d hd
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hnpos : 0 < n := by omega
    constructor
    · intro hmem
      rcases hmem with hdU | hdD
      · exact Set.mem_insert_iff.mpr (Or.inr hdU)
      · have hdgt : D < d := hdD
        have hdeq : d = n := by
          by_contra hne
          have hdlt : d < n := lt_of_le_of_ne (Nat.le_of_dvd hnpos hdn) hne
          rcases hdn with ⟨k, hk⟩
          have hk2 : 2 ≤ k := by
            have hkpos : 0 < k := by
              by_contra hk0
              simp at hk0
              simp [hk0] at hk
              omega
            by_contra hknot
            have hk1 : k = 1 := by omega
            subst k
            simp at hk
            omega
          have htwod : 2 * d ≤ n := by
            calc
              2 * d ≤ k * d := Nat.mul_le_mul_right d hk2
              _ = n := by simpa [Nat.mul_comm] using hk.symm
          omega
        exact Set.mem_insert_iff.mpr (Or.inl hdeq)
    · intro hmem
      rcases Set.mem_insert_iff.mp hmem with rfl | hdU
      · exact Or.inr (Set.mem_Ioi.mpr hDn)
      · exact Or.inl hdU

/-- At row `2D+2`, the lazy tail contributes exactly two new divisors:
`D+1` and the row itself. -/
private theorem supportCoeff_union_Ioi_two_mul_add_two
    (U : Set ℕ) (D : ℕ) (hD3 : 3 ≤ D)
    (hU : U ⊆ Set.Iio D) :
    supportCoeff (U ∪ Set.Ioi D) (2 * D + 2) =
      supportCoeff U (2 * D + 2) + 2 := by
  let H := 2 * D + 2
  have hDU : D + 1 ∉ U := by
    intro hmem
    have hlt := hU hmem
    change D + 1 < D at hlt
    omega
  have hHU : H ∉ insert (D + 1) U := by
    intro hmem
    rcases Set.mem_insert_iff.mp hmem with h | h
    · dsimp [H] at h
      omega
    · have hlt := hU h
      change H < D at hlt
      dsimp [H] at hlt
      omega
  rw [supportCoeff_eq_of_divisorAgreement_local
    (U ∪ Set.Ioi D) (insert H (insert (D + 1) U)) H]
  · rw [supportCoeff_insert_eq_add_indicator _ hHU,
      supportCoeff_insert_eq_add_indicator U hDU]
    have hHpos : 0 < H := by dsimp [H]; omega
    have hDdiv : D + 1 ∈ H.divisors := by
      apply Nat.mem_divisors.mpr
      refine ⟨?_, by omega⟩
      refine ⟨2, ?_⟩
      dsimp [H]
      omega
    have hHdiv : H ∈ H.divisors :=
      Nat.mem_divisors.mpr ⟨dvd_rfl, Nat.ne_of_gt hHpos⟩
    simpa [H, hDdiv, hHdiv]
  · intro d hd
    have hdH : d ∣ H := (Nat.mem_divisors.mp hd).1
    have hHpos : 0 < H := by dsimp [H]; omega
    constructor
    · intro hmem
      rcases hmem with hdU | hdD
      · exact Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_insert_iff.mpr (Or.inr hdU)))
      · have hdgt : D < d := hdD
        have hdle : d ≤ H := Nat.le_of_dvd hHpos hdH
        by_cases hdeq : d = H
        · exact Set.mem_insert_iff.mpr (Or.inl hdeq)
        · have hdlt : d < H := lt_of_le_of_ne hdle hdeq
          rcases hdH with ⟨k, hk⟩
          have hk2 : 2 ≤ k := by
            have hkpos : 0 < k := by
              by_contra hk0
              simp at hk0
              simp [hk0] at hk
            by_contra hknot
            have hk1 : k = 1 := by omega
            subst k
            simp at hk
            omega
          have htwod : 2 * d ≤ H := by
            calc
              2 * d ≤ k * d := Nat.mul_le_mul_right d hk2
              _ = H := by simpa [Nat.mul_comm] using hk.symm
          have hdEq : d = D + 1 := by
            dsimp [H] at hdlt htwod ⊢
            omega
          exact Set.mem_insert_iff.mpr
            (Or.inr (Set.mem_insert_iff.mpr (Or.inl hdEq)))
    · intro hmem
      rcases Set.mem_insert_iff.mp hmem with rfl | hmem
      · exact Or.inr (Set.mem_Ioi.mpr (by dsimp [H]; omega))
      · rcases Set.mem_insert_iff.mp hmem with rfl | hdU
        · exact Or.inr (Set.mem_Ioi.mpr (by omega))
        · exact Or.inl hdU

/-- Replacing the selected last rank `D` by the complete open right tail
changes the producer-aligned integer carry by exactly four.  This is the
local routing bridge from the three finite middle cells to the cofinite
centred-carry endpoint. -/
theorem integerHalfCarry_union_Ioi_eq_producerCarry_add_four
    (U : Set ℕ) (D : ℕ) (hD3 : 3 ≤ D)
    (hU : U ⊆ Set.Iio D) :
    integerHalfCarry (U ∪ Set.Ioi D) (2 * D + 1) =
      producerCarry (insert D U) D + 4 := by
  let B : Set ℕ := U ∪ Set.Ioi D
  let A : Set ℕ := insert D U
  have hDU : D ∉ U := by
    intro hmem
    exact (Nat.lt_irrefl D) (hU hmem)
  have hprefixB :
      integerHalfCarry B (D - 2) =
        integerHalfCarry (B ∩ Set.Iic (D - 1)) (D - 2) := by
    symm
    exact integerHalfCarry_inter_Iic_eq_of_succ_le B (D - 1)
      (D - 2) (by omega)
  have hprefixA :
      integerHalfCarry A (D - 2) =
        integerHalfCarry (A ∩ Set.Iic (D - 1)) (D - 2) := by
    symm
    exact integerHalfCarry_inter_Iic_eq_of_succ_le A (D - 1)
      (D - 2) (by omega)
  have hrestrictB : B ∩ Set.Iic (D - 1) = U := by
    ext d
    simp only [B, Set.mem_inter_iff, Set.mem_union, Set.mem_Ioi,
      Set.mem_Iic]
    constructor
    · rintro ⟨hdU | hdD, hdle⟩
      · exact hdU
      · change D < d at hdD
        omega
    · intro hdU
      have hlt := hU hdU
      change d < D at hlt
      exact ⟨Or.inl hdU, by omega⟩
  have hrestrictA : A ∩ Set.Iic (D - 1) = U := by
    ext d
    simp only [A, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_Iic]
    constructor
    · rintro ⟨rfl | hdU, hdle⟩
      · omega
      · exact hdU
    · intro hdU
      have hlt := hU hdU
      change d < D at hlt
      exact ⟨Or.inr hdU, by omega⟩
  have hstart : integerHalfCarry B (D - 2) =
      integerHalfCarry A (D - 2) := by
    rw [hprefixB, hprefixA, hrestrictB, hrestrictA]
  have hBD : supportCoeff B D = supportCoeff U D := by
    apply supportCoeff_eq_of_divisorAgreement_local
    intro d hd
    have hdle := Nat.le_of_dvd (by omega : 0 < D)
      (Nat.mem_divisors.mp hd).1
    simp only [B, Set.mem_union, Set.mem_Ioi]
    constructor
    · rintro (hdU | hdD)
      · exact hdU
      · change D < d at hdD
        omega
    · exact fun hdU => Or.inl hdU
  have hAD : supportCoeff A D = supportCoeff U D + 1 := by
    dsimp [A]
    rw [supportCoeff_insert_eq_add_indicator U hDU]
    have hdiv : D ∈ D.divisors :=
      Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
    simp [hdiv]
  have hfirst : integerHalfCarry B (D - 1) =
      integerHalfCarry A (D - 1) + 1 := by
    rw [show D - 1 = (D - 2) + 1 by omega,
      integerHalfCarry_succ, integerHalfCarry_succ,
      show D - 2 + 2 = D by omega, hBD, hAD, hstart]
    omega
  have hrun : ∀ k : ℕ, k ≤ D - 1 →
      integerHalfCarry B (D - 1 + k) =
        integerHalfCarry A (D - 1 + k) + 1 := by
    intro k hk
    induction k with
    | zero => simpa using hfirst
    | succ k ih =>
        have hk' : k ≤ D - 1 := by omega
        have hkD2 : k ≤ D - 2 := by omega
        have hnlo : D < D + k + 1 := by omega
        have hnhi : D + k + 1 < 2 * D + 2 := by omega
        have hBcoeff := supportCoeff_union_Ioi_eq_add_one
          U D (D + k + 1) hD3 hU hnlo hnhi
        have hnotdiv : D ∉ (D + k + 1).divisors := by
          intro hdiv
          have hdvd := (Nat.mem_divisors.mp hdiv).1
          rcases hdvd with ⟨q, hq⟩
          have hqpos : 0 < q := by
            by_contra hq0
            simp at hq0
            simp [hq0] at hq
          have hq1 : q = 1 := by
            by_contra hqne
            have hq2 : 2 ≤ q := by omega
            have htwo : 2 * D ≤ D + k + 1 := by
              calc
                2 * D ≤ q * D := Nat.mul_le_mul_right D hq2
                _ = D + k + 1 := by simpa [Nat.mul_comm] using hq.symm
            omega
          subst q
          simp at hq
          omega
        have hAcoeff : supportCoeff A (D + k + 1) =
            supportCoeff U (D + k + 1) := by
          dsimp [A]
          rw [supportCoeff_insert_eq_add_indicator U hDU]
          simp [hnotdiv]
        rw [show D - 1 + (k + 1) = (D - 1 + k) + 1 by omega,
          integerHalfCarry_succ, integerHalfCarry_succ,
          show D - 1 + k + 2 = D + k + 1 by omega,
          hBcoeff, hAcoeff, ih hk']
        omega
  have hbeforeTwoD : integerHalfCarry B (2 * D - 2) =
      integerHalfCarry A (2 * D - 2) + 1 := by
    have hrun' := hrun (D - 1) le_rfl
    simpa only [show D - 1 + (D - 1) = 2 * D - 2 by omega] using hrun'
  have hBtwoD := supportCoeff_union_Ioi_eq_add_one
    U D (2 * D) hD3 hU (by omega) (by omega)
  have hAtwoD : supportCoeff A (2 * D) = supportCoeff U (2 * D) + 1 := by
    dsimp [A]
    rw [supportCoeff_insert_eq_add_indicator U hDU]
    have hdiv : D ∈ (2 * D).divisors := by
      exact Nat.mem_divisors.mpr ⟨⟨2, by omega⟩, by omega⟩
    simp [hdiv]
  have htwoD : integerHalfCarry B (2 * D - 1) =
      integerHalfCarry A (2 * D - 1) + 2 := by
    rw [show 2 * D - 1 = (2 * D - 2) + 1 by omega,
      integerHalfCarry_succ, integerHalfCarry_succ,
      show 2 * D - 2 + 2 = 2 * D by omega,
      hBtwoD, hAtwoD, hbeforeTwoD]
    omega
  have hBtwoDOne := supportCoeff_union_Ioi_eq_add_one
    U D (2 * D + 1) hD3 hU (by omega) (by omega)
  have hnotdivOne : D ∉ (2 * D + 1).divisors := by
    intro hdiv
    rcases (Nat.mem_divisors.mp hdiv).1 with ⟨q, hq⟩
    have hqpos : 0 < q := by
      by_contra hq0
      simp at hq0
      simp [hq0] at hq
    have hqle : q ≤ 2 := by
      by_contra hqnot
      have hq3 : 3 ≤ q := by omega
      have hthree : 3 * D ≤ 2 * D + 1 := by
        calc
          3 * D ≤ q * D := Nat.mul_le_mul_right D hq3
          _ = 2 * D + 1 := by simpa [Nat.mul_comm] using hq.symm
      omega
    interval_cases q <;> omega
  have hAtwoDOne : supportCoeff A (2 * D + 1) =
      supportCoeff U (2 * D + 1) := by
    dsimp [A]
    rw [supportCoeff_insert_eq_add_indicator U hDU]
    simp [hnotdivOne]
  have htwoDOne : integerHalfCarry B (2 * D) =
      integerHalfCarry A (2 * D) + 3 := by
    rw [show 2 * D = (2 * D - 1) + 1 by omega,
      integerHalfCarry_succ, integerHalfCarry_succ,
      show 2 * D - 1 + 2 = 2 * D + 1 by omega,
      hBtwoDOne, hAtwoDOne, htwoD]
    omega
  have hBfinal := supportCoeff_union_Ioi_two_mul_add_two U D hD3 hU
  have hnotdivFinal : D ∉ (2 * D + 2).divisors := by
    intro hdiv
    have hdvd := (Nat.mem_divisors.mp hdiv).1
    rcases hdvd with ⟨q, hq⟩
    have hqpos : 0 < q := by
      by_contra hq0
      simp at hq0
      simp [hq0] at hq
    have hqle : q ≤ 2 := by
      by_contra hqnot
      have hq3 : 3 ≤ q := by omega
      have hthree : 3 * D ≤ 2 * D + 2 := by
        calc
          3 * D ≤ q * D := Nat.mul_le_mul_right D hq3
          _ = 2 * D + 2 := by simpa [Nat.mul_comm] using hq.symm
      omega
    interval_cases q <;> omega
  have hAfinal : supportCoeff A (2 * D + 2) =
      supportCoeff U (2 * D + 2) := by
    dsimp [A]
    rw [supportCoeff_insert_eq_add_indicator U hDU]
    simp [hnotdivFinal]
  have hfinal : integerHalfCarry B (2 * D + 1) =
      integerHalfCarry A (2 * D + 1) + 4 := by
    rw [show 2 * D + 1 = (2 * D) + 1 by omega,
      integerHalfCarry_succ, integerHalfCarry_succ,
      show 2 * D + 2 = 2 * D + 2 by rfl,
      hBfinal, hAfinal, htwoDOne]
    omega
  simpa [B, A, producerCarry] using hfinal

/-- Centring subtracts the common Möbius baseline unit, so the carry-four
swap becomes the promised three-cell translation. -/
theorem mobiusCenteredHalfCarry_union_Ioi_eq_producerCarry_add_three
    (U : Set ℕ) (D : ℕ) (hD3 : 3 ≤ D)
    (hU : U ⊆ Set.Iio D) :
    mobiusCenteredHalfCarry (U ∪ Set.Ioi D) (2 * D + 1) =
      producerCarry (insert D U) D + 3 := by
  rw [mobiusCenteredHalfCarry,
    integerHalfCarry_union_Ioi_eq_producerCarry_add_four U D hD3 hU]
  omega

/-- The lazy support really is the finite lower word followed by the full
Mersenne tail.  Keeping this identity next to the carry-three translation
makes both halves of the final-cell route locally visible. -/
theorem positiveMersenneSupportValue_union_Ioi_eq_add_tail
    (u : Finset ℕ) (D : ℕ)
    (hu : ∀ d ∈ u, 0 < d ∧ d < D) :
    positiveMersenneSupportValue
        ((↑u : Set ℕ) ∪ Set.Ioi D) =
      positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail D := by
  let B : Set ℕ := (↑u : Set ℕ) ∪ Set.Ioi D
  rw [positiveMersenneSupportValue_eq_prefix_add_suffix B D]
  change mersenneSupportPrefix B D + positiveMersenneSupportSuffix B D = _
  have hpref : mersenneSupportPrefix B D =
      positiveMersenneSupportValue (↑u : Set ℕ) := by
    apply mersenneSupportPrefix_eq_coe_finset
    · intro d hd
      exact ⟨(hu d hd).1, (hu d hd).2.le⟩
    · intro d hdpos hdle
      constructor
      · intro hdB
        rcases hdB with hdu | hdD
        · exact hdu
        · change D < d at hdD
          omega
      · exact fun hdu => Or.inl hdu
  have hsuffix : positiveMersenneSupportSuffix B D = mersenneTail D := by
    unfold positiveMersenneSupportSuffix mersenneTail
    apply tsum_congr
    intro k
    have hmem : D + k + 1 ∈ B := by
      exact Or.inr (Set.mem_Ioi.mpr (by omega))
    rw [Set.indicator_of_mem hmem]
  rw [hpref, hsuffix]

/-! ## The zero endpoint is incompatible with a cofinite right tail -/

/-- A cofinite support supplies two distinct forced divisors at row
`2D+4`: the row itself and `D+2`. -/
theorem two_le_supportCoeff_two_mul_add_four_of_Ioi_subset
    (A : Set ℕ) (D : ℕ) (hcofinite : Set.Ioi D ⊆ A) :
    2 ≤ supportCoeff A (2 * D + 4) := by
  classical
  let F : Finset ℕ := {D + 2, 2 * D + 4}
  have hFcard : F.card = 2 := by
    have hne : D + 2 ≠ 2 * D + 4 := by omega
    dsimp [F]
    exact Finset.card_pair hne
  have hFsub :
      F ⊆ (2 * D + 4).divisors.filter (fun d => d ∈ A) := by
    intro d hd
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · apply Finset.mem_filter.mpr
      constructor
      · exact Nat.mem_divisors.mpr
          ⟨⟨2, by ring⟩, by omega⟩
      · exact hcofinite (Set.mem_Ioi.mpr (by omega))
    · apply Finset.mem_filter.mpr
      constructor
      · exact Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
      · exact hcofinite (Set.mem_Ioi.mpr (by omega))
  rw [supportCoeff_eq_card_filter]
  calc
    2 = F.card := hFcard.symm
    _ ≤ ((2 * D + 4).divisors.filter (fun d => d ∈ A)).card :=
      Finset.card_le_card hFsub

/-- If every rank after `D` is selected, a zero centred endpoint at row
`2D+1` becomes strictly negative within two coefficient rows.  Therefore it
cannot belong to any support whose value is strictly below one half. -/
theorem cofiniteRightTail_ne_zero_centeredEndpoint
    (A : Set ℕ) (D : ℕ)
    (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (hcofinite : Set.Ioi D ⊆ A) :
    mobiusCenteredHalfCarry A (2 * D + 1) ≠ 0 := by
  intro hzero
  have hself : 2 * D + 3 ∈ A :=
    hcofinite (Set.mem_Ioi.mpr (by omega))
  have hcoeffOne : 1 ≤ supportCoeff A (2 * D + 3) := by
    have hpos := supportCoeff_pos_of_mem_dvd A hself dvd_rfl (by omega)
    omega
  have hcoeffOneZ : (1 : ℤ) ≤ (supportCoeff A (2 * D + 3) : ℤ) := by
    exact_mod_cast hcoeffOne
  have hfirst := mobiusCenteredHalfCarry_succ A (2 * D + 1)
  have hfirstNonpos :
      mobiusCenteredHalfCarry A (2 * D + 2) ≤ 0 := by
    rw [show 2 * D + 1 + 1 = 2 * D + 2 by omega,
      show 2 * D + 1 + 2 = 2 * D + 3 by omega, hzero] at hfirst
    omega
  have hcoeffTwo : 2 ≤ supportCoeff A (2 * D + 4) :=
    two_le_supportCoeff_two_mul_add_four_of_Ioi_subset A D hcofinite
  have hcoeffTwoZ : (2 : ℤ) ≤ (supportCoeff A (2 * D + 4) : ℤ) := by
    exact_mod_cast hcoeffTwo
  have hsecond := mobiusCenteredHalfCarry_succ A (2 * D + 2)
  have hnegative : mobiusCenteredHalfCarry A (2 * D + 3) < 0 := by
    rw [show 2 * D + 2 + 1 = 2 * D + 3 by omega,
      show 2 * D + 2 + 2 = 2 * D + 4 by omega] at hsecond
    omega
  have hnonneg :=
    mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
      A hone hseries (2 * D + 3)
  omega

/-! ## Consumption by the final middle producer -/

/-- The first of the three exceptional final-middle cells, coordinate `-3`,
cannot precede an all-right tail.  The finite producer cell becomes centred
charge zero after the exact lazy-tail swap, while the same all-right word
puts the resulting cofinite support strictly below one half. -/
theorem finalMiddleCell_neg_three_not_last
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hcell :
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -3) :
    False := by
  classical
  let hs5 : 5 ≤ D := by omega
  let K := seamAdjacentCut D hs5
  let u : Finset ℕ := seamWordSupport K.below
  let B : Set ℕ := (↑u : Set ℕ) ∪ Set.Ioi D
  have hword : seamGreedyWord (D + 1) = K.below.extend false := by
    exact seamGreedyWord_succ_eq_middleBranch D hs5 hncarry hmiddle
  have hu : ∀ e ∈ u, 2 ≤ e ∧ e < D := by
    intro e he
    exact seamWordSupport_below he
  have hbase : seamWordSupport (seamGreedyWord (D + 1)) =
      u ∪ Finset.Ico (D + 1) (D + 1) := by
    rw [hword, seamWordSupport_extend_false (by omega)]
    simp [u]
  have hlazy : positiveMersenneSupportValue (↑u : Set ℕ) +
      mersenneTail D < (1 / 2 : ℝ) := by
    exact prefix_add_mersenneTail_lt_half_of_eventually_right
      (S := D + 1) (D := D) (u := u)
      (by omega) (by omega) hu hright hbase
  have hseries : erdosSupportSeries 2 B < (1 / 2 : ℝ) := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    rw [show B = (↑u : Set ℕ) ∪ Set.Ioi D by rfl,
      positiveMersenneSupportValue_union_Ioi_eq_add_tail]
    · exact hlazy
    · intro e he
      exact ⟨by have := (hu e he).1; omega, (hu e he).2⟩
  have hone : 1 ∉ B := by
    intro hmem
    rcases hmem with huone | hDone
    · have := (hu 1 huone).1
      omega
    · change D < 1 at hDone
      omega
  have hcofinite : Set.Ioi D ⊆ B := by
    intro e he
    exact Or.inr he
  have hU : (↑u : Set ℕ) ⊆ Set.Iio D := by
    intro e he
    exact Set.mem_Iio.mpr (hu e he).2
  have hproducer : producerCarry (insert D (↑u : Set ℕ)) D =
      4 * (K.remainder : ℤ) - (K.belowPulse : ℤ) - 4 := by
    simpa [K, u] using
      producerCarry_insert_seamBelowSupport_eq_middleCoordinate D hs5
  have hcellK :
      4 * (K.remainder : ℤ) - (K.belowPulse : ℤ) - 4 = -3 := by
    simpa [K] using hcell
  have hzero : mobiusCenteredHalfCarry B (2 * D + 1) = 0 := by
    rw [show B = (↑u : Set ℕ) ∪ Set.Ioi D by rfl,
      mobiusCenteredHalfCarry_union_Ioi_eq_producerCarry_add_three
        (↑u : Set ℕ) D (by omega) hU,
      hproducer, hcellK]
    norm_num
  exact (cofiniteRightTail_ne_zero_centeredEndpoint
    B D hone hseries hcofinite) hzero

#print axioms mobiusCenteredHalfCarry_add_two
#print axioms mobiusCenteredHalfCarry_add_two_mul
#print axioms mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
#print axioms cofiniteRightTail_ne_zero_centeredEndpoint
#print axioms integerHalfCarry_union_Ioi_eq_producerCarry_add_four
#print axioms mobiusCenteredHalfCarry_union_Ioi_eq_producerCarry_add_three
#print axioms positiveMersenneSupportValue_union_Ioi_eq_add_tail
#print axioms finalMiddleCell_neg_three_not_last

end

end Erdos249257
