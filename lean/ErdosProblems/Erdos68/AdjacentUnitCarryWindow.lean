import ErdosProblems.Erdos68.PrimeThresholdParity

/-!
# Erdős #68: finite rational adjacent-carry window

The adjacent-unit condition is already a width-one real interval for the
finite predecessor gap.  This companion module transports that statement
back to `ℚ`, where denominator clearing and modular arguments can consume it.
-/

namespace ErdosProblems.Erdos68

/-- The width-one adjacent-carry criterion over the executable rational
predecessor gap.  No infinite sum or real-valued remainder occurs in the
right-hand side. -/
theorem consecutive_unit_carries_iff_predecessorGapRat_width_one_window
    {m : ℕ} (hm : 3 ≤ m) :
    (factorialGapStepCarry m = 1 ∧
        factorialGapStepCarry (m + 1) = 1) ↔
      (m : ℚ) + 2 +
            (m + 1 : ℚ) / ((m.factorial : ℚ) - 1) +
            1 / (((m + 1).factorial : ℚ) - 1) <
          (m : ℚ) * (m + 1 : ℚ) *
            factorialGapPredecessorGapRat m ∧
        (m : ℚ) * (m + 1 : ℚ) *
              factorialGapPredecessorGapRat m ≤
          (m : ℚ) + 3 +
            (m + 1 : ℚ) / ((m.factorial : ℚ) - 1) +
            1 / (((m + 1).factorial : ℚ) - 1) := by
  rw [consecutive_unit_carries_iff_predecessorGap_width_one_window hm]
  rw [← factorialGapPredecessorGapRat_cast m]
  norm_cast

/-! ## Cleared integer window -/

/-- Positive common denominator for the adjacent-unit window. -/
def adjacentUnitCarryWindowDen (m : ℕ) : ℤ :=
  ((factorialGapPredecessorScaledRat m).den : ℤ) *
    ((m.factorial : ℤ) - 1) *
    (((m + 1).factorial : ℤ) - 1)

/-- Integer lower endpoint after clearing every denominator. -/
def adjacentUnitCarryWindowLowerNum (m : ℕ) : ℤ :=
  (m + 2 : ℤ) * adjacentUnitCarryWindowDen m +
    (m + 1 : ℤ) *
      ((factorialGapPredecessorScaledRat m).den : ℤ) *
      (((m + 1).factorial : ℤ) - 1) +
    ((factorialGapPredecessorScaledRat m).den : ℤ) *
      ((m.factorial : ℤ) - 1)

/-- Cleared integer state tested by the adjacent-unit window. -/
def adjacentUnitCarryWindowStateNum (m : ℕ) : ℤ :=
  (m : ℤ) * (m + 1 : ℤ) *
    factorialGapPredecessorGapNumerator m *
    ((m.factorial : ℤ) - 1) *
    (((m + 1).factorial : ℤ) - 1)

/-- **Pure integer adjacent-unit criterion.**  Two consecutive unit carries
occur exactly when the cleared predecessor numerator lies in one explicitly
computable integer interval.  Its length is the positive common denominator
`adjacentUnitCarryWindowDen m`; all quantities use only the finite prefix. -/
theorem consecutive_unit_carries_iff_integer_width_window
    {m : ℕ} (hm : 3 ≤ m) :
    (factorialGapStepCarry m = 1 ∧
        factorialGapStepCarry (m + 1) = 1) ↔
      adjacentUnitCarryWindowLowerNum m <
          adjacentUnitCarryWindowStateNum m ∧
        adjacentUnitCarryWindowStateNum m ≤
          adjacentUnitCarryWindowLowerNum m +
            adjacentUnitCarryWindowDen m := by
  rw [consecutive_unit_carries_iff_predecessorGapRat_width_one_window hm]
  rw [factorialGapPredecessorGapRat_eq_numerator_div_den]
  have hfacM : (1 : ℤ) < (m.factorial : ℤ) := by
    exact_mod_cast Nat.one_lt_factorial.mpr (by omega : 2 ≤ m)
  have hfacNext : (1 : ℤ) < ((m + 1).factorial : ℤ) := by
    exact_mod_cast Nat.one_lt_factorial.mpr (by omega : 2 ≤ m + 1)
  have hdenBase :
      (0 : ℤ) < ((factorialGapPredecessorScaledRat m).den : ℤ) := by
    positivity
  have hden : 0 < adjacentUnitCarryWindowDen m := by
    unfold adjacentUnitCarryWindowDen
    exact
      mul_pos
        (mul_pos hdenBase (sub_pos.mpr hfacM))
        (sub_pos.mpr hfacNext)
  have hfacMQ : (0 : ℚ) < (m.factorial : ℚ) - 1 := by
    exact_mod_cast sub_pos.mpr hfacM
  have hfacNextQ : (0 : ℚ) < ((m + 1).factorial : ℚ) - 1 := by
    exact_mod_cast sub_pos.mpr hfacNext
  have hdenBaseQ :
      (0 : ℚ) < ((factorialGapPredecessorScaledRat m).den : ℚ) := by
    positivity
  have hdenQ : (0 : ℚ) < adjacentUnitCarryWindowDen m := by
    exact_mod_cast hden
  have hleft :
      (m : ℚ) + 2 +
            (m + 1 : ℚ) / ((m.factorial : ℚ) - 1) +
            1 / (((m + 1).factorial : ℚ) - 1) =
        (adjacentUnitCarryWindowLowerNum m : ℚ) /
          adjacentUnitCarryWindowDen m := by
    unfold adjacentUnitCarryWindowLowerNum adjacentUnitCarryWindowDen
    push_cast
    field_simp [ne_of_gt hfacMQ, ne_of_gt hfacNextQ,
      ne_of_gt hdenBaseQ]
  have hstate :
      (m : ℚ) * (m + 1 : ℚ) *
            ((factorialGapPredecessorGapNumerator m : ℚ) /
              (factorialGapPredecessorScaledRat m).den) =
        (adjacentUnitCarryWindowStateNum m : ℚ) /
          adjacentUnitCarryWindowDen m := by
    unfold adjacentUnitCarryWindowStateNum adjacentUnitCarryWindowDen
    push_cast
    field_simp [ne_of_gt hfacMQ, ne_of_gt hfacNextQ,
      ne_of_gt hdenBaseQ]
  rw [hleft, hstate]
  have hright :
      (m : ℚ) + 3 +
            (m + 1 : ℚ) / ((m.factorial : ℚ) - 1) +
            1 / (((m + 1).factorial : ℚ) - 1) =
        ((adjacentUnitCarryWindowLowerNum m +
            adjacentUnitCarryWindowDen m : ℤ) : ℚ) /
          adjacentUnitCarryWindowDen m := by
    calc
      (m : ℚ) + 3 +
            (m + 1 : ℚ) / ((m.factorial : ℚ) - 1) +
            1 / (((m + 1).factorial : ℚ) - 1) =
          ((m : ℚ) + 2 +
            (m + 1 : ℚ) / ((m.factorial : ℚ) - 1) +
            1 / (((m + 1).factorial : ℚ) - 1)) + 1 := by ring
      _ = (adjacentUnitCarryWindowLowerNum m : ℚ) /
            adjacentUnitCarryWindowDen m + 1 := by rw [hleft]
      _ = ((adjacentUnitCarryWindowLowerNum m +
              adjacentUnitCarryWindowDen m : ℤ) : ℚ) /
            adjacentUnitCarryWindowDen m := by
        push_cast
        field_simp [ne_of_gt hdenQ]
  rw [hright]
  rw [div_lt_div_iff_of_pos_right hdenQ,
    div_le_div_iff_of_pos_right hdenQ]
  norm_cast

/-- Positive displacement of the cleared state above the lower endpoint. -/
def adjacentUnitCarryWindowOffset (m : ℕ) : ℤ :=
  adjacentUnitCarryWindowStateNum m -
    adjacentUnitCarryWindowLowerNum m

/-- The integer window in displacement form. -/
theorem consecutive_unit_carries_iff_positive_offset_le_den
    {m : ℕ} (hm : 3 ≤ m) :
    (factorialGapStepCarry m = 1 ∧
        factorialGapStepCarry (m + 1) = 1) ↔
      0 < adjacentUnitCarryWindowOffset m ∧
        adjacentUnitCarryWindowOffset m ≤
          adjacentUnitCarryWindowDen m := by
  rw [consecutive_unit_carries_iff_integer_width_window hm]
  unfold adjacentUnitCarryWindowOffset
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The offset has a forced complementary residue modulo the later
factorial gap.  This is the exact cofactor residue information which a
private-prime argument needs in addition to mere support. -/
theorem adjacentUnitCarryWindowOffset_modEq_neg_den_mul_gap
    (m : ℕ) :
    Int.ModEq (((m + 1).factorial : ℤ) - 1)
      (adjacentUnitCarryWindowOffset m)
      (-((factorialGapPredecessorScaledRat m).den : ℤ) *
        ((m.factorial : ℤ) - 1)) := by
  rw [Int.modEq_iff_dvd]
  unfold adjacentUnitCarryWindowOffset adjacentUnitCarryWindowStateNum
    adjacentUnitCarryWindowLowerNum adjacentUnitCarryWindowDen
  refine ⟨?_, ?_⟩
  · exact
      -((m : ℤ) * (m + 1 : ℤ) *
          factorialGapPredecessorGapNumerator m *
          ((m.factorial : ℤ) - 1)) +
        (m + 2 : ℤ) *
          ((factorialGapPredecessorScaledRat m).den : ℤ) *
          ((m.factorial : ℤ) - 1) +
        (m + 1 : ℤ) *
          ((factorialGapPredecessorScaledRat m).den : ℤ)
  · ring

/-- The same offset has a forced complementary residue modulo the earlier
factorial gap. -/
theorem adjacentUnitCarryWindowOffset_modEq_neg_mul_den
    (m : ℕ) :
    Int.ModEq ((m.factorial : ℤ) - 1)
      (adjacentUnitCarryWindowOffset m)
      (-(m : ℤ) * (m + 1 : ℤ) *
        ((factorialGapPredecessorScaledRat m).den : ℤ)) := by
  rw [Int.modEq_iff_dvd]
  unfold adjacentUnitCarryWindowOffset adjacentUnitCarryWindowStateNum
    adjacentUnitCarryWindowLowerNum adjacentUnitCarryWindowDen
  rw [Nat.factorial_succ]
  push_cast
  refine ⟨?_, ?_⟩
  · exact
      -((m : ℤ) * (m + 1 : ℤ) *
          factorialGapPredecessorGapNumerator m *
          (((m + 1 : ℤ) * (m.factorial : ℤ)) - 1)) +
        (m + 2 : ℤ) *
          ((factorialGapPredecessorScaledRat m).den : ℤ) *
          (((m + 1 : ℤ) * (m.factorial : ℤ)) - 1) +
        (m + 1 : ℤ) ^ 2 *
          ((factorialGapPredecessorScaledRat m).den : ℤ) +
        ((factorialGapPredecessorScaledRat m).den : ℤ)
  · ring

/-! ## Two-step reduced-orbit factorization -/

/-- The two transition normalizers telescope exactly: after two steps their
product converts the future reduced denominator into the raw denominator of
the adjacent-carry window.  This identity is independent of all carry
values. -/
theorem twoStep_den_mul_transitionNormalizers
    {m : ℕ} (hm : 3 ≤ m) :
    (factorialGapPredecessorScaledRat (m + 2)).den *
          factorialGapPredecessorTransitionNormalizer (m + 1) *
          factorialGapPredecessorTransitionNormalizer m =
      (factorialGapPredecessorScaledRat m).den *
          (m.factorial - 1) * ((m + 1).factorial - 1) := by
  have hnext :=
    factorialGapPredecessorScaledRat_succ_den_mul_transitionNormalizer
      (m := m + 1) (by omega)
  have hcurrent :=
    factorialGapPredecessorScaledRat_succ_den_mul_transitionNormalizer
      (m := m) (by omega)
  calc
    (factorialGapPredecessorScaledRat (m + 2)).den *
          factorialGapPredecessorTransitionNormalizer (m + 1) *
          factorialGapPredecessorTransitionNormalizer m =
        ((factorialGapPredecessorScaledRat (m + 1)).den *
          ((m + 1).factorial - 1)) *
          factorialGapPredecessorTransitionNormalizer m := by rw [hnext]
    _ = ((factorialGapPredecessorScaledRat (m + 1)).den *
          factorialGapPredecessorTransitionNormalizer m) *
          ((m + 1).factorial - 1) := by ac_rfl
    _ = ((factorialGapPredecessorScaledRat m).den *
          (m.factorial - 1)) * ((m + 1).factorial - 1) := by rw [hcurrent]

/-- Consequently the cleared adjacent-window denominator is exactly the
future reduced denominator multiplied by both transition normalizers. -/
theorem adjacentUnitCarryWindowDen_eq_twoStep_den
    {m : ℕ} (hm : 3 ≤ m) :
    adjacentUnitCarryWindowDen m =
      (factorialGapPredecessorScaledRat (m + 2)).den *
        factorialGapPredecessorTransitionNormalizer (m + 1) *
        factorialGapPredecessorTransitionNormalizer m := by
  unfold adjacentUnitCarryWindowDen
  have h := twoStep_den_mul_transitionNormalizers hm
  have hfacM : 1 ≤ m.factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hfacNext : 1 ≤ (m + 1).factorial :=
    Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (m + 1))
  have hcast := congrArg (fun x : ℕ => (x : ℤ)) h.symm
  simpa only [Nat.cast_mul, Nat.cast_sub hfacM,
    Nat.cast_sub hfacNext, Nat.cast_one] using hcast

/-- **Exact mixed-radix factorization of the cleared offset.**  The offset
splits into the positive reduced numerator two steps later, multiplied by
the two exact cancellation normalizers, plus one whole window denominator
times the weighted two-carry defect.  Thus the Archimedean window and the
prime-by-prime cancellation dynamics are literally the same integer. -/
theorem adjacentUnitCarryWindowOffset_eq_twoStep_factorization
    {m : ℕ} (hm : 3 ≤ m) :
    adjacentUnitCarryWindowOffset m =
      factorialGapPredecessorGapNumerator (m + 2) *
          factorialGapPredecessorTransitionNormalizer (m + 1) *
          factorialGapPredecessorTransitionNormalizer m +
        adjacentUnitCarryWindowDen m *
          (((m + 1 : ℕ) : ℤ) * factorialGapStepCarry m +
            factorialGapStepCarry (m + 1) - (m + 2 : ℤ)) := by
  let M : ℤ := m
  let U₀ : ℤ := factorialGapPredecessorGapNumerator m
  let U₁ : ℤ := factorialGapPredecessorGapNumerator (m + 1)
  let U₂ : ℤ := factorialGapPredecessorGapNumerator (m + 2)
  let V₀ : ℤ := (factorialGapPredecessorScaledRat m).den
  let V₁ : ℤ := (factorialGapPredecessorScaledRat (m + 1)).den
  let F : ℤ := (m.factorial : ℤ) - 1
  let H : ℤ := ((m + 1).factorial : ℤ) - 1
  let G₀ : ℤ := factorialGapPredecessorTransitionNormalizer m
  let G₁ : ℤ := factorialGapPredecessorTransitionNormalizer (m + 1)
  let b₀ : ℤ := factorialGapStepCarry m
  let b₁ : ℤ := factorialGapStepCarry (m + 1)
  have hrecM :=
    factorialGapPredecessorGapNumerator_mul_transitionNormalizer
      (m := m) (by omega)
  have hrecNext :=
    factorialGapPredecessorGapNumerator_mul_transitionNormalizer
      (m := m + 1) (by omega)
  have hdenFactorNat :=
    factorialGapPredecessorScaledRat_succ_den_mul_transitionNormalizer
      (m := m) (by omega)
  have hfacOne : 1 ≤ m.factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hdenFactor : V₁ * G₀ = V₀ * F := by
    have hcast := congrArg (fun x : ℕ => (x : ℤ)) hdenFactorNat
    simpa only [V₀, V₁, F, G₀, Nat.cast_mul,
      Nat.cast_sub hfacOne] using hcast
  change U₁ * G₀ = M * U₀ * F - V₀ - b₀ * V₀ * F at hrecM
  simp only [Nat.cast_add, Nat.cast_one] at hrecNext
  change
    U₂ * G₁ = (M + 1) * U₁ * H - V₁ - b₁ * V₁ * H at hrecNext
  unfold adjacentUnitCarryWindowOffset adjacentUnitCarryWindowStateNum
    adjacentUnitCarryWindowLowerNum adjacentUnitCarryWindowDen
  push_cast
  change
    M * (M + 1) * U₀ * F * H -
        ((M + 2) * (V₀ * F * H) + (M + 1) * V₀ * H + V₀ * F) =
      U₂ * G₁ * G₀ +
        (V₀ * F * H) * ((M + 1) * b₀ + b₁ - (M + 2))
  symm
  calc
    U₂ * G₁ * G₀ +
          (V₀ * F * H) * ((M + 1) * b₀ + b₁ - (M + 2)) =
        ((M + 1) * U₁ * H - V₁ - b₁ * V₁ * H) * G₀ +
          (V₀ * F * H) * ((M + 1) * b₀ + b₁ - (M + 2)) := by
      rw [hrecNext]
    _ =
        (M + 1) * (U₁ * G₀) * H - (V₁ * G₀) -
            b₁ * (V₁ * G₀) * H +
          (V₀ * F * H) * ((M + 1) * b₀ + b₁ - (M + 2)) := by
      ring
    _ =
        (M + 1) * (M * U₀ * F - V₀ - b₀ * V₀ * F) * H -
            V₀ * F - b₁ * (V₀ * F) * H +
          (V₀ * F * H) * ((M + 1) * b₀ + b₁ - (M + 2)) := by
      rw [hrecM, hdenFactor]
    _ =
        M * (M + 1) * U₀ * F * H -
          ((M + 2) * (V₀ * F * H) + (M + 1) * V₀ * H + V₀ * F) := by
      ring

/-- Under an adjacent unit pair the carry-defect term vanishes, leaving the
offset as a product of the future coprime numerator and the two exact
cancellation normalizers. -/
theorem adjacentUnitCarryWindowOffset_eq_twoStep_reducedNumerator
    {m : ℕ} (hm : 3 ≤ m)
    (hpair : factorialGapStepCarry m = 1 ∧
      factorialGapStepCarry (m + 1) = 1) :
    adjacentUnitCarryWindowOffset m =
      factorialGapPredecessorGapNumerator (m + 2) *
        factorialGapPredecessorTransitionNormalizer (m + 1) *
        factorialGapPredecessorTransitionNormalizer m := by
  rw [adjacentUnitCarryWindowOffset_eq_twoStep_factorization hm,
    hpair.1, hpair.2]
  push_cast
  ring

/-- Natural-number form of the adjacent-pair factorization.  Positivity of
the window offset removes every signed cast, while the canonical natural
numerator represents the positive reduced numerator exactly. -/
theorem adjacentUnitCarryWindowOffset_toNat_eq_twoStep_reducedNumerator
    {m : ℕ} (hm : 3 ≤ m)
    (hpair : factorialGapStepCarry m = 1 ∧
      factorialGapStepCarry (m + 1) = 1) :
    (adjacentUnitCarryWindowOffset m).toNat =
      factorialGapPredecessorGapNumeratorNat (m + 2) *
        factorialGapPredecessorTransitionNormalizer (m + 1) *
        factorialGapPredecessorTransitionNormalizer m := by
  have hoffPos : 0 < adjacentUnitCarryWindowOffset m :=
    ((consecutive_unit_carries_iff_positive_offset_le_den hm).mp hpair).1
  have hfactor :=
    adjacentUnitCarryWindowOffset_eq_twoStep_reducedNumerator hm hpair
  have hcast :
      ((adjacentUnitCarryWindowOffset m).toNat : ℤ) =
        (factorialGapPredecessorGapNumeratorNat (m + 2) : ℤ) *
          factorialGapPredecessorTransitionNormalizer (m + 1) *
          factorialGapPredecessorTransitionNormalizer m := by
    rw [Int.toNat_of_nonneg hoffPos.le,
      factorialGapPredecessorGapNumeratorNat_cast]
    exact hfactor
  exact_mod_cast hcast

/-- **Valuation-correct cancellation balance.**  For an adjacent unit pair,
the `q`-adic load of the positive offset is the sum of the loads in the
future reduced numerator and both exact transition normalizers.  No
disjoint-support assumption is made: a prime may occur on several terms,
as the exact `m = 52` computation requires. -/
theorem adjacentUnitCarryWindowOffset_toNat_factorization
    {m q : ℕ} (hm : 3 ≤ m)
    (hpair : factorialGapStepCarry m = 1 ∧
      factorialGapStepCarry (m + 1) = 1) :
    ((adjacentUnitCarryWindowOffset m).toNat).factorization q =
      (factorialGapPredecessorGapNumeratorNat (m + 2)).factorization q +
        (factorialGapPredecessorTransitionNormalizer (m + 1)).factorization q +
        (factorialGapPredecessorTransitionNormalizer m).factorization q := by
  rw [adjacentUnitCarryWindowOffset_toNat_eq_twoStep_reducedNumerator hm hpair]
  have hnumPos :
      0 < factorialGapPredecessorGapNumeratorNat (m + 2) := by
    have hnumPosInt :=
      factorialGapPredecessorGapNumerator_pos (m + 2)
    rw [← factorialGapPredecessorGapNumeratorNat_cast] at hnumPosInt
    exact_mod_cast hnumPosInt
  have hGNextPos :
      0 < factorialGapPredecessorTransitionNormalizer (m + 1) :=
    factorialGapPredecessorTransitionNormalizer_pos (by omega)
  have hGMPos :
      0 < factorialGapPredecessorTransitionNormalizer m :=
    factorialGapPredecessorTransitionNormalizer_pos (by omega)
  rw [Nat.factorization_mul
      (mul_ne_zero hnumPos.ne' hGNextPos.ne') hGMPos.ne',
    Nat.factorization_mul hnumPos.ne' hGNextPos.ne']
  rfl

/-- If a prime survives in the reduced denominator two steps later, the
future numerator is prime-free there by reduced coprimality.  Consequently
the entire offset valuation is carried by the two cancellation normalizers,
with overlap retained additively rather than discarded. -/
theorem adjacentUnitCarryWindowOffset_toNat_factorization_of_prime_dvd_den
    {m q : ℕ} (hm : 3 ≤ m)
    (hpair : factorialGapStepCarry m = 1 ∧
      factorialGapStepCarry (m + 1) = 1)
    (hq : q.Prime)
    (hqDen : q ∣ (factorialGapPredecessorScaledRat (m + 2)).den) :
    ((adjacentUnitCarryWindowOffset m).toNat).factorization q =
      (factorialGapPredecessorTransitionNormalizer (m + 1)).factorization q +
        (factorialGapPredecessorTransitionNormalizer m).factorization q := by
  rw [adjacentUnitCarryWindowOffset_toNat_factorization hm hpair]
  have hmod :
      factorialGapPredecessorGapNumeratorNat (m + 2) % q ≠ 0 :=
    factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_prime_dvd_den
      hq hqDen
  have hnotDvd :
      ¬q ∣ factorialGapPredecessorGapNumeratorNat (m + 2) := by
    intro hdiv
    exact hmod (Nat.mod_eq_zero_of_dvd hdiv)
  rw [Nat.factorization_eq_zero_of_not_dvd hnotDvd, zero_add]

/-- **Exact prime-power two-step collision law.**  Suppose `q ^ e` divides
the later factorial gap and `q` survives in the reduced denominator two
steps later.  For an adjacent unit pair, the entire power `q ^ e` occurs in
the two cancellation normalizers exactly when it already occurs in the
complementary old-denominator factor.  Thus the forced residue controls
every available `q`-adic layer, not merely prime support. -/
theorem primePow_dvd_twoStep_transitionNormalizers_iff_dvd_complement
    {m q e : ℕ} (hm : 3 ≤ m)
    (hpair : factorialGapStepCarry m = 1 ∧
      factorialGapStepCarry (m + 1) = 1)
    (hq : q.Prime)
    (hqPowLaterGap : q ^ e ∣ (m + 1).factorial - 1)
    (hqFutureDen : q ∣
      (factorialGapPredecessorScaledRat (m + 2)).den) :
    q ^ e ∣ factorialGapPredecessorTransitionNormalizer (m + 1) *
          factorialGapPredecessorTransitionNormalizer m ↔
      q ^ e ∣ (factorialGapPredecessorScaledRat m).den *
          (m.factorial - 1) := by
  have hoffPos : 0 < adjacentUnitCarryWindowOffset m :=
    ((consecutive_unit_carries_iff_positive_offset_le_den hm).mp hpair).1
  have hfacMOne : 1 ≤ m.factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hfacNextOne : 1 ≤ (m + 1).factorial := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (m + 1))
  have hqPowLaterGapZ :
      ((q ^ e : ℕ) : ℤ) ∣ ((m + 1).factorial : ℤ) - 1 := by
    exact_mod_cast hqPowLaterGap
  have hresidue :=
    adjacentUnitCarryWindowOffset_modEq_neg_den_mul_gap m
  have hqPowDiff :
      ((q ^ e : ℕ) : ℤ) ∣ adjacentUnitCarryWindowOffset m -
        (-((factorialGapPredecessorScaledRat m).den : ℤ) *
          ((m.factorial : ℤ) - 1)) := by
    have hreverse := hqPowLaterGapZ.trans hresidue.dvd
    exact dvd_neg.mp (by simpa only [neg_sub] using hreverse)
  have hqPowOffsetZ_iff :
      ((q ^ e : ℕ) : ℤ) ∣ adjacentUnitCarryWindowOffset m ↔
        ((q ^ e : ℕ) : ℤ) ∣
          ((factorialGapPredecessorScaledRat m).den : ℤ) *
            ((m.factorial : ℤ) - 1) := by
    constructor
    · intro hqPowOffset
      have hqPowNegComplement :
          ((q ^ e : ℕ) : ℤ) ∣
            -((factorialGapPredecessorScaledRat m).den : ℤ) *
              ((m.factorial : ℤ) - 1) := by
        convert Int.dvd_sub hqPowOffset hqPowDiff using 1 <;> ring
      exact dvd_neg.mp (by simpa only [neg_mul] using hqPowNegComplement)
    · intro hqPowComplement
      have hqPowNegComplement :
          ((q ^ e : ℕ) : ℤ) ∣
            -((factorialGapPredecessorScaledRat m).den : ℤ) *
              ((m.factorial : ℤ) - 1) := by
        simpa only [neg_mul] using dvd_neg.mpr hqPowComplement
      convert Int.dvd_add hqPowDiff hqPowNegComplement using 1 <;> ring
  have hqPowOffset_iff :
      q ^ e ∣ (adjacentUnitCarryWindowOffset m).toNat ↔
        q ^ e ∣ (factorialGapPredecessorScaledRat m).den *
          (m.factorial - 1) := by
    have hoffCast :
        (((adjacentUnitCarryWindowOffset m).toNat : ℕ) : ℤ) =
          adjacentUnitCarryWindowOffset m := by
      rw [Int.toNat_of_nonneg hoffPos.le]
    have hcomplementCast :
        (((factorialGapPredecessorScaledRat m).den *
            (m.factorial - 1) : ℕ) : ℤ) =
          ((factorialGapPredecessorScaledRat m).den : ℤ) *
            ((m.factorial : ℤ) - 1) := by
      push_cast
      norm_num [Nat.cast_sub hfacMOne]
    constructor
    · intro hqPowOffset
      have hqPowOffsetZ :
          ((q ^ e : ℕ) : ℤ) ∣
            (((adjacentUnitCarryWindowOffset m).toNat : ℕ) : ℤ) := by
        exact_mod_cast hqPowOffset
      rw [hoffCast] at hqPowOffsetZ
      have hqPowComplementZ := hqPowOffsetZ_iff.mp hqPowOffsetZ
      rw [← hcomplementCast] at hqPowComplementZ
      exact_mod_cast hqPowComplementZ
    · intro hqPowComplement
      have hqPowComplementZ :
          ((q ^ e : ℕ) : ℤ) ∣
            (((factorialGapPredecessorScaledRat m).den *
              (m.factorial - 1) : ℕ) : ℤ) := by
        exact_mod_cast hqPowComplement
      rw [hcomplementCast] at hqPowComplementZ
      have hqPowOffsetZ := hqPowOffsetZ_iff.mpr hqPowComplementZ
      rw [← hoffCast] at hqPowOffsetZ
      exact_mod_cast hqPowOffsetZ
  rw [← hqPowOffset_iff,
    adjacentUnitCarryWindowOffset_toNat_eq_twoStep_reducedNumerator hm hpair]
  have hqNumMod :
      factorialGapPredecessorGapNumeratorNat (m + 2) % q ≠ 0 :=
    factorialGapPredecessorGapNumeratorNat_mod_ne_zero_of_prime_dvd_den
      hq hqFutureDen
  have hqNum :
      ¬q ∣ factorialGapPredecessorGapNumeratorNat (m + 2) := by
    intro hdiv
    exact hqNumMod (Nat.mod_eq_zero_of_dvd hdiv)
  have hqPowNumCoprime :
      Nat.Coprime (q ^ e)
        (factorialGapPredecessorGapNumeratorNat (m + 2)) :=
    (hq.coprime_pow_of_not_dvd hqNum).symm
  constructor
  · intro hdiv
    simpa only [mul_assoc] using
      (dvd_mul_of_dvd_right hdiv
        (factorialGapPredecessorGapNumeratorNat (m + 2)))
  · intro hdiv
    have hdiv' :
        q ^ e ∣ factorialGapPredecessorGapNumeratorNat (m + 2) *
          (factorialGapPredecessorTransitionNormalizer (m + 1) *
            factorialGapPredecessorTransitionNormalizer m) := by
      simpa only [mul_assoc] using hdiv
    exact hqPowNumCoprime.dvd_of_dvd_mul_left hdiv'

end ErdosProblems.Erdos68
