import Erdos249257.BooleanMobiusSkipRow

/-!
# Doubling a below-half exact Boolean--Möbius row

An exact quotient row which is still strictly below one half and contains
rank two has enough residue slack to be extended through a pure binary upper
window.  The construction preserves the entire old support.
-/

namespace Erdos249257

open scoped BigOperators

/-! ## Doubling an exact row which is still below one half -/

/-- The rank-two residue is always at least one third. -/
theorem one_third_le_localMersenneFraction_two (M : ℕ) :
    (1 / 3 : ℚ) ≤ localMersenneFraction M 2 := by
  have hmod : M % 2 = 0 ∨ M % 2 = 1 := by
    have := Nat.mod_lt M (by omega : 0 < 2)
    omega
  rcases hmod with hmod | hmod <;>
    norm_num [localMersenneFraction, hmod]

/-- The elementary slack needed for the doubling window. -/
theorem three_mul_sub_two_lt_two_pow_pred
    {n : ℕ} (hn : 6 ≤ n) :
    3 * (n - 2) < 2 ^ (n - 1) := by
  have hsmall : n - 2 ≤ 2 ^ (n - 3) := by
    have h := nat_le_two_pow_pred (n - 2)
    rw [show n - 2 - 1 = n - 3 by omega] at h
    exact h
  have hpos : 0 < 2 ^ (n - 3) := Nat.two_pow_pos _
  have hsplit : 2 ^ (n - 1) = 4 * 2 ^ (n - 3) := by
    rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
    ring
  omega

/-- If an exact quotient row is still below one half and contains rank two,
then its missing quotient at row `2n-1` fits in the pure upper window
`{n+1, ..., 2n-1}`.  The rank-two residue supplies one third of a full
window of slack, while all old residues together cost at most `n-1`. -/
theorem localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * n - 1) < 2 ^ (n - 1) := by
  let M := 2 * n - 1
  let P := 2 ^ (n - 1)
  let T := 2 ^ (M - 1)
  let Q := localPrefixQuotient D M
  let Fn := localFractionMass D n
  let FM := localFractionMass D M
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hDtwo : ∀ d ∈ D, 2 ≤ d := fun d hd ↦ (hD d hd).1
  have hscaleN :
      (2 : ℚ) ^ n * localMersennePrefixValue D =
        (localPrefixQuotient D n : ℚ) + Fn := by
    simpa [Fn] using
      (scaled_localMersennePrefixValue (D := D) (M := n) hDtwo)
  have hscaleM :
      (2 : ℚ) ^ M * localMersennePrefixValue D = (Q : ℚ) + FM := by
    simpa [Q, FM] using
      (scaled_localMersennePrefixValue (D := D) (M := M) hDtwo)
  have hhalfN : (2 : ℚ) ^ n * (1 / 2 : ℚ) = (P : ℚ) := by
    dsimp [P]
    calc
      (2 : ℚ) ^ n * (1 / 2 : ℚ) =
          2 ^ ((n - 1) + 1) * (1 / 2 : ℚ) := by congr 2 <;> omega
      _ = (2 : ℚ) ^ (n - 1) := by rw [pow_succ]; ring
      _ = ((2 ^ (n - 1) : ℕ) : ℚ) := by norm_num
  have hhalfM : (2 : ℚ) ^ M * (1 / 2 : ℚ) = (T : ℚ) := by
    dsimp [T]
    calc
      (2 : ℚ) ^ M * (1 / 2 : ℚ) =
          2 ^ ((M - 1) + 1) * (1 / 2 : ℚ) := by congr 2 <;> omega
      _ = (2 : ℚ) ^ (M - 1) := by rw [pow_succ]; ring
      _ = ((2 ^ (M - 1) : ℕ) : ℚ) := by norm_num
  have hPposNat : 1 ≤ P := by
    dsimp [P]
    exact Nat.one_le_pow _ _ (by norm_num)
  have hdeficitN :
      (2 : ℚ) ^ n * ((1 / 2 : ℚ) - localMersennePrefixValue D) =
        1 - Fn := by
    rw [mul_sub, hhalfN, hscaleN, hquot]
    rw [Nat.cast_sub hPposNat]
    ring
  have hscaleFactor : (2 : ℚ) ^ M = (P : ℚ) * (2 : ℚ) ^ n := by
    dsimp [M, P]
    rw [show 2 * n - 1 = (n - 1) + n by omega, pow_add]
    norm_num
  have hdeficitM :
      (2 : ℚ) ^ M * ((1 / 2 : ℚ) - localMersennePrefixValue D) =
        (P : ℚ) * (1 - Fn) := by
    rw [hscaleFactor, mul_assoc, hdeficitN]
  have hFnonneg : 0 ≤ FM := by
    dsimp [FM, localFractionMass]
    exact Finset.sum_nonneg fun d hd ↦
      (localMersenneFraction_pos (M := M) (hDtwo d hd)).le
  have hscaledBelow : (Q : ℚ) + FM < (T : ℚ) := by
    have h := mul_lt_mul_of_pos_left hbelow
      (pow_pos (by norm_num : (0 : ℚ) < 2) M)
    rw [hscaleM, hhalfM] at h
    exact h
  have hQltCast : (Q : ℚ) < (T : ℚ) := by linarith
  have hQlt : Q < T := by exact_mod_cast hQltCast
  have hQle : Q ≤ T := hQlt.le
  have honeSub : 1 ≤ T - Q := by omega
  have hAcast :
      ((localBinarySuffix D 1 M : ℕ) : ℚ) =
        (T : ℚ) - (Q : ℚ) - 1 := by
    unfold localBinarySuffix
    change (((T - Q - 1 : ℕ) : ℚ)) = _
    rw [Nat.cast_sub honeSub, Nat.cast_sub hQle]
    norm_num
  have hdeficitAtM :
      (2 : ℚ) ^ M * ((1 / 2 : ℚ) - localMersennePrefixValue D) =
        (T : ℚ) - (Q : ℚ) - FM := by
    rw [mul_sub, hhalfM, hscaleM]
    ring
  have hAeq :
      ((localBinarySuffix D 1 M : ℕ) : ℚ) =
        (P : ℚ) * (1 - Fn) + FM - 1 := by
    rw [hAcast]
    calc
      (T : ℚ) - (Q : ℚ) - 1 =
          ((T : ℚ) - (Q : ℚ) - FM) + FM - 1 := by ring
      _ = (2 : ℚ) ^ M *
            ((1 / 2 : ℚ) - localMersennePrefixValue D) + FM - 1 := by
              rw [hdeficitAtM]
      _ = (P : ℚ) * (1 - Fn) + FM - 1 := by rw [hdeficitM]
  have hFnLower : (1 / 3 : ℚ) ≤ Fn := by
    calc
      (1 / 3 : ℚ) ≤ localMersenneFraction n 2 :=
        one_third_le_localMersenneFraction_two n
      _ ≤ Fn := by
        dsimp [Fn, localFractionMass]
        exact Finset.single_le_sum
          (fun d hd ↦ (localMersenneFraction_pos
            (M := n) (hDtwo d hd)).le) htwo
  have hFMcard : FM ≤ (D.card : ℚ) := by
    simpa [FM] using
      (localFractionMass_le_card_skippedCore (D := D) (M := M) hDtwo)
  have hcard : D.card ≤ n - 1 := by
    have h := card_le_sub_two_of_mem_lt (D := D) (c := n + 1)
      (fun d hd ↦ ⟨(hD d hd).1, Nat.lt_succ_of_le (hD d hd).2⟩)
    omega
  have hFMbound : FM ≤ (n - 1 : ℕ) := by
    have hcardCast : (D.card : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by
      exact_mod_cast hcard
    exact hFMcard.trans hcardCast
  have hthirdP : ((n - 2 : ℕ) : ℚ) < (P : ℚ) / 3 := by
    have hgrowth := three_mul_sub_two_lt_two_pow_pred hn
    have hgrowthCast :
        ((3 * (n - 2) : ℕ) : ℚ) < (P : ℚ) := by
      exact_mod_cast hgrowth
    push_cast at hgrowthCast
    linarith
  have hPFn : (P : ℚ) / 3 ≤ (P : ℚ) * Fn := by
    have hPnonneg : (0 : ℚ) ≤ (P : ℚ) := by positivity
    have h := mul_le_mul_of_nonneg_left hFnLower hPnonneg
    simpa [div_eq_mul_inv] using h
  have hAltCast :
      ((localBinarySuffix D 1 M : ℕ) : ℚ) < (P : ℚ) := by
    rw [hAeq]
    have hn2cast : (((n - 1 : ℕ) : ℚ) - 1) = ((n - 2 : ℕ) : ℚ) := by
      calc
        (((n - 1 : ℕ) : ℚ) - 1) = (((n - 1) - 1 : ℕ) : ℚ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ n - 1)]
          norm_num
        _ = ((n - 2 : ℕ) : ℚ) := by congr 1 <;> omega
    linarith
  have hAlt : localBinarySuffix D 1 M < P := by
    exact_mod_cast hAltCast
  simpa [M, P] using hAlt

/-- A below-half exact row containing rank two has an exact extension at
endpoint `2n-1`, and every newly inserted rank lies strictly above `n`.
This support-separation form is the input needed to locate a later first
crossing if the extension lands above one half. -/
theorem exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, d ∉ D → n < d) ∧
      2 ∈ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * n - 1) ∧
      localPrefixQuotient E (2 * n - 1) =
        2 ^ ((2 * n - 1) - 1) - 1 := by
  let M := 2 * n - 1
  obtain ⟨y, hylen, hybool, hyvalue⟩ :=
    exists_boolean_word_of_lt_two_pow
      (localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below
        hn hD htwo hquot hbelow)
  let H := upperSupportFromWord M y
  refine ⟨D ∪ H, Finset.subset_union_left, ?_,
    Finset.mem_union_left H htwo, ?_, ?_⟩
  · intro d hdE hdD
    have hdH : d ∈ H := by
      rw [Finset.mem_union] at hdE
      exact hdE.resolve_left hdD
    have hdlo := upperSupportFromWord_lower_bound
      (M := M) (y := y) (by simp [M, hylen]; omega) hdH
    simp [M, hylen] at hdlo
    omega
  · intro d hd
    rw [Finset.mem_union] at hd
    rcases hd with hdD | hdH
    · exact ⟨(hD d hdD).1, (hD d hdD).2.trans (by omega)⟩
    · have hdlo := upperSupportFromWord_lower_bound
          (M := M) (y := y) (by simp [M, hylen]; omega) hdH
      have hdhi := upperSupportFromWord_le_top hdH
      constructor
      · simp [M, hylen] at hdlo
        omega
      · exact hdhi
  · have hdisj : Disjoint D H := by
      rw [Finset.disjoint_left]
      intro d hdD hdH
      have hdlo := upperSupportFromWord_lower_bound
        (M := M) (y := y) (by simp [M, hylen]; omega) hdH
      have hdhi := (hD d hdD).2
      simp [M, hylen] at hdlo
      omega
    have hunion : localPrefixQuotient (D ∪ H) M =
        localPrefixQuotient D M + localPrefixQuotient H M := by
      unfold localPrefixQuotient
      rw [Finset.sum_union hdisj]
    have hH : localPrefixQuotient H M = Nat.ofDigits 2 y := by
      apply localPrefixQuotient_upperSupportFromWord
      · simp [M, hylen]
        omega
      · exact hybool
      · simp [M, hylen]
        omega
      · simp [M, hylen]
        omega
    have hDtwo : ∀ d ∈ D, 2 ≤ d := fun d hd ↦ (hD d hd).1
    have hscaled := scaled_localMersennePrefixValue
      (D := D) (M := M) hDtwo
    have hpowPos : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
    have hlt := mul_lt_mul_of_pos_left hbelow hpowPos
    rw [hscaled] at hlt
    have hFnonneg : 0 ≤ localFractionMass D M := by
      unfold localFractionMass
      exact Finset.sum_nonneg fun d hd ↦
        (localMersenneFraction_pos (M := M) (hDtwo d hd)).le
    have hq : (localPrefixQuotient D M : ℚ) < (2 : ℚ) ^ (M - 1) := by
      have hhalf : (2 : ℚ) ^ M * (1 / 2 : ℚ) =
          (2 : ℚ) ^ (M - 1) := by
        have hMpos : 1 ≤ M := by dsimp [M]; omega
        calc
          (2 : ℚ) ^ M * (1 / 2 : ℚ) =
              2 ^ ((M - 1) + 1) * (1 / 2 : ℚ) := by congr 2 <;> omega
          _ = (2 : ℚ) ^ (M - 1) := by rw [pow_succ]; ring
      rw [hhalf] at hlt
      linarith
    have hqNat : localPrefixQuotient D M < 2 ^ (M - 1) := by
      exact_mod_cast hq
    have hsuffix : localPrefixQuotient D M + localBinarySuffix D 1 M =
        2 ^ (M - 1) - 1 := by
      unfold localBinarySuffix
      omega
    rw [hunion, hH, hyvalue]
    simpa [M] using hsuffix

/-- Compatibility projection of the strict-support extension theorem. -/
theorem exists_exactRowExtension_two_mul_sub_one_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      2 ∈ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * n - 1) ∧
      localPrefixQuotient E (2 * n - 1) =
        2 ^ ((2 * n - 1) - 1) - 1 := by
  obtain ⟨E, hDE, _hnew, htwoE, hE, hquotE⟩ :=
    exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below
      hn hD htwo hquot hbelow
  exact ⟨E, hDE, htwoE, hE, hquotE⟩

/-- Proposition-valued corollary of the literal extension theorem. -/
theorem exactLocalMersenneHalfRow_two_mul_sub_one_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    ExactLocalMersenneHalfRow (2 * n - 1) := by
  obtain ⟨E, _hsub, _htwoE, hE, hEq⟩ :=
    exists_exactRowExtension_two_mul_sub_one_of_exact_below
      hn hD htwo hquot hbelow
  exact ⟨E, hE, hEq⟩

end Erdos249257
