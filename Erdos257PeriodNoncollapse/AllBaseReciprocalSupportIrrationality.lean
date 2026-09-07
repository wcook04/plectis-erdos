import Erdos257PeriodNoncollapse.ReciprocalSupportIrrationality

/-!
# Reciprocal-summable support irrationality at every integer base

The binary close-return theorem is stronger than its original statement
suggests. For every radix b ≥ 2, the displacement of a periodic tail atom
from its zero-shift value is at most twice the corresponding binary
displacement. Hence the binary LCM/Cesàro close returns are simultaneous
close returns at every integer base. An exact integer-orbit argument then
rules out rationality.

This yields the unconditional theorem

  A.Infinite → Summable (reciprocalSupportTerm A) →
    Irrational (erdosSupportSeries b A)

for every integer b ≥ 2, without pairwise coprimality, periodicity, density,
or a powerful-support hypothesis.
-/

namespace Erdos257PeriodNoncollapse

open Filter Set

noncomputable section

/-- The conductor-d shifted tail atom in radix b. -/
noncomputable def shiftedRadixAtom (b N d : ℕ) : ℝ :=
  if d = 0 then 0
  else (b : ℝ) ^ (N % d) / ((b : ℝ) ^ d - 1)

/-- The radix atom restricted to a support. -/
noncomputable def shiftedRadixSupportAtom
    (b : ℕ) (A : Set ℕ) (N d : ℕ) : ℝ :=
  Set.indicator A (shiftedRadixAtom b N) d

theorem shiftedRadixAtom_nonneg
    (b N d : ℕ) (hb : 2 ≤ b) :
    0 ≤ shiftedRadixAtom b N d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom]
  · rw [shiftedRadixAtom, if_neg hd.ne']
    have hb1 : (1 : ℝ) < (b : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
    have hden : (0 : ℝ) < (b : ℝ) ^ d - 1 := by
      have : (1 : ℝ) < (b : ℝ) ^ d := one_lt_pow₀ hb1 hd.ne'
      linarith
    positivity

theorem shiftedRadixAtom_zero
    (b d : ℕ) :
    shiftedRadixAtom b 0 d = (1 : ℝ) / ((b : ℝ) ^ d - 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom]
  · simp [shiftedRadixAtom, hd.ne']

theorem shiftedRadixAtom_zero_le
    (b N d : ℕ) (hb : 2 ≤ b) :
    shiftedRadixAtom b 0 d ≤ shiftedRadixAtom b N d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom]
  · rw [shiftedRadixAtom_zero, shiftedRadixAtom, if_neg hd.ne']
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (le_trans (by norm_num) hb)
    have hden : (0 : ℝ) ≤ (b : ℝ) ^ d - 1 := by
      have : (1 : ℝ) ≤ (b : ℝ) ^ d := one_le_pow₀ hb1
      linarith
    exact div_le_div_of_nonneg_right (one_le_pow₀ hb1) hden

theorem shiftedRadixAtom_zero_lt_of_lt
    (b N d : ℕ) (hb : 2 ≤ b) (hN : 0 < N) (hNd : N < d) :
    shiftedRadixAtom b 0 d < shiftedRadixAtom b N d := by
  have hd : 0 < d := hN.trans hNd
  rw [shiftedRadixAtom_zero, shiftedRadixAtom, if_neg hd.ne',
    Nat.mod_eq_of_lt hNd]
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
  have hden : (0 : ℝ) < (b : ℝ) ^ d - 1 := by
    have : (1 : ℝ) < (b : ℝ) ^ d := one_lt_pow₀ hb1 hd.ne'
    linarith
  exact div_lt_div_of_pos_right (one_lt_pow₀ hb1 hN.ne') hden

theorem shiftedRadixAtom_le_pow_mul_zero
    (b N d : ℕ) (hb : 2 ≤ b) :
    shiftedRadixAtom b N d ≤
      (b : ℝ) ^ N * ((1 : ℝ) / ((b : ℝ) ^ d - 1)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom]
  · rw [shiftedRadixAtom, if_neg hd.ne']
    have hb0 : (1 : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (le_trans (by norm_num) hb)
    have hb1 : (1 : ℝ) < (b : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
    have hden : (0 : ℝ) < (b : ℝ) ^ d - 1 := by
      have : (1 : ℝ) < (b : ℝ) ^ d := one_lt_pow₀ hb1 hd.ne'
      linarith
    have hmod : N % d ≤ N := Nat.mod_le _ _
    have hp : (b : ℝ) ^ (N % d) ≤ (b : ℝ) ^ N :=
      pow_le_pow_right₀ hb0 hmod
    calc
      (b : ℝ) ^ (N % d) / ((b : ℝ) ^ d - 1) =
          (b : ℝ) ^ (N % d) * (1 / ((b : ℝ) ^ d - 1)) := by ring
      _ ≤ (b : ℝ) ^ N * (1 / ((b : ℝ) ^ d - 1)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)

theorem summable_shiftedRadixSupportAtom
    (b : ℕ) (A : Set ℕ) (N : ℕ) (hb : 2 ≤ b) :
    Summable (shiftedRadixSupportAtom b A N) := by
  have hbase := summable_erdosSupport_indicator b A hb
  have hscaled : Summable (fun d : ℕ =>
      (b : ℝ) ^ N *
        Set.indicator A (fun d => (1 : ℝ) / ((b : ℝ) ^ d - 1)) d) :=
    hbase.mul_left ((b : ℝ) ^ N)
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hscaled
  · exact Set.indicator_nonneg
      (fun d _ => shiftedRadixAtom_nonneg b N d hb) d
  · by_cases hdA : d ∈ A
    · simp only [shiftedRadixSupportAtom, Set.indicator_of_mem hdA]
      exact shiftedRadixAtom_le_pow_mul_zero b N d hb
    · simp [shiftedRadixSupportAtom, hdA]

/-- A radix atom advances by multiplication by b, with one unit carry at
its wrap point. -/
theorem shiftedRadixAtom_step
    (b N d : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) * shiftedRadixAtom b N d -
        shiftedRadixAtom b (N + 1) d =
      if 0 < d ∧ d ∣ N + 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom]
  · have hb1 : (1 : ℝ) < (b : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
    by_cases hd1 : d = 1
    · subst d
      have hden1 : (b : ℝ) - 1 ≠ 0 := by linarith
      simp only [shiftedRadixAtom, one_ne_zero, if_false, Nat.mod_one,
        pow_zero, Nat.zero_lt_one, Nat.one_dvd, and_self, if_true, pow_one]
      field_simp [hden1]
    have hone : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
    have hsuccmod : (N + 1) % d = (N % d + 1) % d := by
      rw [Nat.add_mod, hone]
    have hden : (b : ℝ) ^ d - 1 ≠ 0 := by
      have : (1 : ℝ) < (b : ℝ) ^ d := one_lt_pow₀ hb1 hd.ne'
      linarith
    by_cases hwrap : d ∣ N + 1
    · have hsucc : (N + 1) % d = 0 := Nat.mod_eq_zero_of_dvd hwrap
      have hmodlt : N % d < d := Nat.mod_lt _ hd
      have hmod : N % d + 1 = d := by
        have hdvd : d ∣ N % d + 1 := by
          apply Nat.dvd_of_mod_eq_zero
          rw [← hsuccmod]
          exact hsucc
        have hle : d ≤ N % d + 1 := Nat.le_of_dvd (by omega) hdvd
        omega
      rw [if_pos ⟨hd, hwrap⟩]
      simp only [shiftedRadixAtom, if_neg hd.ne', hsucc, pow_zero]
      rw [show N % d = d - 1 by omega]
      have hpow :
          (b : ℝ) * (b : ℝ) ^ (d - 1) = (b : ℝ) ^ d := by
        calc
          (b : ℝ) * (b : ℝ) ^ (d - 1) =
              (b : ℝ) ^ (d - 1) * b := by ring
          _ = (b : ℝ) ^ ((d - 1) + 1) := (pow_succ _ _).symm
          _ = (b : ℝ) ^ d := by congr 1; omega
      field_simp [hden]
      rw [hpow]
    · have hsucc0 : (N + 1) % d ≠ 0 := by
        intro hzero
        exact hwrap (Nat.dvd_of_mod_eq_zero hzero)
      have hmodlt : N % d < d := Nat.mod_lt _ hd
      have hnextlt : N % d + 1 < d := by
        have hle : N % d + 1 ≤ d := by omega
        apply lt_of_le_of_ne hle
        intro heq
        apply hsucc0
        rw [hsuccmod, heq, Nat.mod_self]
      have hsucc : (N + 1) % d = N % d + 1 := by
        rw [hsuccmod, Nat.mod_eq_of_lt hnextlt]
      rw [if_neg (fun h => hwrap h.2)]
      simp only [shiftedRadixAtom, if_neg hd.ne', hsucc]
      rw [pow_succ]
      ring

theorem shiftedRadixSupportAtom_step
    (b : ℕ) (A : Set ℕ) [DecidablePred (· ∈ A)]
    (N d : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) * shiftedRadixSupportAtom b A N d -
        shiftedRadixSupportAtom b A (N + 1) d =
      if d ∈ A ∧ 0 < d ∧ d ∣ N + 1 then 1 else 0 := by
  classical
  by_cases hdA : d ∈ A
  · simp only [shiftedRadixSupportAtom, Set.indicator_of_mem hdA, hdA,
      true_and]
    exact shiftedRadixAtom_step b N d hb
  · simp [shiftedRadixSupportAtom, hdA]

/-- Summing the atom recurrences gives the exact integral support
coefficient pulse. -/
theorem tsum_shiftedRadixSupportAtom_step
    (b : ℕ) (A : Set ℕ) (N : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) * (∑' d : ℕ, shiftedRadixSupportAtom b A N d) -
        (∑' d : ℕ, shiftedRadixSupportAtom b A (N + 1) d) =
      (supportCoeff A (N + 1) : ℝ) := by
  classical
  have hsN := summable_shiftedRadixSupportAtom b A N hb
  have hsS := summable_shiftedRadixSupportAtom b A (N + 1) hb
  calc
    (b : ℝ) * (∑' d, shiftedRadixSupportAtom b A N d) -
          ∑' d, shiftedRadixSupportAtom b A (N + 1) d =
        (∑' d, (b : ℝ) * shiftedRadixSupportAtom b A N d) -
          ∑' d, shiftedRadixSupportAtom b A (N + 1) d := by
            rw [tsum_mul_left]
    _ = ∑' d, ((b : ℝ) * shiftedRadixSupportAtom b A N d -
          shiftedRadixSupportAtom b A (N + 1) d) :=
      ((hsN.mul_left (b : ℝ)).tsum_sub hsS).symm
    _ = ∑' d, (if d ∈ A ∧ 0 < d ∧ d ∣ N + 1 then 1 else 0) :=
      tsum_congr (shiftedRadixSupportAtom_step b A N · hb)
    _ = (supportCoeff A (N + 1) : ℝ) := by
      rw [tsum_eq_sum (s := (N + 1).divisors)]
      · rw [supportCoeff_cast_eq_sum_indicator]
        apply Finset.sum_congr rfl
        intro d hddiv
        have hdiv : d ∣ N + 1 := (Nat.mem_divisors.mp hddiv).1
        have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv (by omega)
        by_cases hdA : d ∈ A
        · simp [hdA, hpos, hdiv]
        · simp [hdA]
      · intro d hdnot
        have hndvd : ¬ d ∣ N + 1 := by
          intro hdiv
          exact hdnot (Nat.mem_divisors.mpr ⟨hdiv, by omega⟩)
        simp [hndvd]

theorem tsum_shiftedRadixSupportAtom_zero
    (b : ℕ) (A : Set ℕ) :
    (∑' d : ℕ, shiftedRadixSupportAtom b A 0 d) =
      erdosSupportSeries b A := by
  unfold erdosSupportSeries shiftedRadixSupportAtom
  apply tsum_congr
  intro d
  by_cases hdA : d ∈ A
  · simp [hdA, shiftedRadixAtom_zero]
  · simp [hdA]

theorem shiftedRadixSupportAtom_zero_strictMinimum
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (N : ℕ) (hN : 0 < N) :
    (∑' d : ℕ, shiftedRadixSupportAtom b A 0 d) <
      ∑' d : ℕ, shiftedRadixSupportAtom b A N d := by
  obtain ⟨d, hdA, hNd⟩ := hA.exists_gt N
  exact Summable.tsum_lt_tsum_of_nonneg (i := d)
    (fun e => Set.indicator_nonneg
      (fun k _ => shiftedRadixAtom_nonneg b 0 k hb) e)
    (fun e => by
      classical
      by_cases heA : e ∈ A
      · simpa [shiftedRadixSupportAtom, heA] using
          shiftedRadixAtom_zero_le b N e hb
      · simp [shiftedRadixSupportAtom, heA])
    (by
      simpa [shiftedRadixSupportAtom, hdA] using
        shiftedRadixAtom_zero_lt_of_lt b N d hb hN hNd)
    (summable_shiftedRadixSupportAtom b A N hb)

/-! ## Binary-to-radix displacement transfer -/

/-- A radix-b atom moves from its initial value by at most twice the
corresponding binary atom. The constant is uniform in b, N, and d. -/
theorem shiftedRadixAtom_sub_zero_le_two_mul_binary_sub_zero
    (b N d : ℕ) (hb : 2 ≤ b) :
    shiftedRadixAtom b N d - shiftedRadixAtom b 0 d ≤
      2 * (shiftedMersenneAtom N d - shiftedMersenneAtom 0 d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom, shiftedMersenneAtom]
  let r := N % d
  have hrd : r < d := Nat.mod_lt _ hd
  by_cases hr0 : r = 0
  · simp [shiftedRadixAtom, shiftedMersenneAtom, hd.ne', r, hr0]
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  have hdenb : (0 : ℝ) < (b : ℝ) ^ d - 1 := by
    have : (1 : ℝ) < (b : ℝ) ^ d := one_lt_pow₀ hb1 hd.ne'
    linarith
  have hden2 : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) hd.ne'
    linarith
  have hk : 0 < d - r := Nat.sub_pos_of_lt hrd
  have hpowbk : (0 : ℝ) < (b : ℝ) ^ (d - r) := by positivity
  have hpow2k : (0 : ℝ) < (2 : ℝ) ^ (d - r) := by positivity
  have hpow2r : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  have hpowb_ge : (2 : ℝ) ^ (d - r) ≤ (b : ℝ) ^ (d - r) :=
    (pow_le_pow_left₀ (by norm_num) hbR) (d - r)
  have hupper :
      ((b : ℝ) ^ r - 1) / ((b : ℝ) ^ d - 1) ≤
        1 / (b : ℝ) ^ (d - r) := by
    rw [div_le_div_iff₀ hdenb hpowbk]
    have hpowadd : (b : ℝ) ^ r * (b : ℝ) ^ (d - r) = (b : ℝ) ^ d := by
      rw [← pow_add]
      congr 1
      omega
    have hone : (1 : ℝ) ≤ (b : ℝ) ^ (d - r) :=
      one_le_pow₀ (by linarith)
    calc
      ((b : ℝ) ^ r - 1) * (b : ℝ) ^ (d - r) =
          (b : ℝ) ^ r * (b : ℝ) ^ (d - r) -
            (b : ℝ) ^ (d - r) := by ring
      _ = (b : ℝ) ^ d - (b : ℝ) ^ (d - r) := by rw [hpowadd]
      _ ≤ (b : ℝ) ^ d - 1 := sub_le_sub_left hone _
      _ = 1 * ((b : ℝ) ^ d - 1) := by ring
  have hmiddle :
      1 / (b : ℝ) ^ (d - r) ≤ 1 / (2 : ℝ) ^ (d - r) := by
    exact one_div_le_one_div_of_le (by positivity) hpowb_ge
  have hlower :
      1 / (2 : ℝ) ^ (d - r) ≤
        2 * (((2 : ℝ) ^ r - 1) / ((2 : ℝ) ^ d - 1)) := by
    rw [div_le_iff₀ hpow2k]
    have hpowadd : (2 : ℝ) ^ r * (2 : ℝ) ^ (d - r) = (2 : ℝ) ^ d := by
      rw [← pow_add]
      congr 1
      omega
    have hhalf : (2 : ℝ) ^ r ≤ 2 * ((2 : ℝ) ^ r - 1) := by
      nlinarith
    have hdenne : (2 : ℝ) ^ d - 1 ≠ 0 := ne_of_gt hden2
    rw [div_eq_mul_inv]
    field_simp [hdenne]
    nlinarith
  rw [shiftedRadixAtom, if_neg hd.ne', shiftedRadixAtom_zero,
    shiftedMersenneAtom, if_neg hd.ne', shiftedMersenneAtom_zero]
  change ((b : ℝ) ^ r / ((b : ℝ) ^ d - 1) -
      1 / ((b : ℝ) ^ d - 1)) ≤
    2 * ((2 : ℝ) ^ r / ((2 : ℝ) ^ d - 1) -
      1 / ((2 : ℝ) ^ d - 1))
  have hleft :
      (b : ℝ) ^ r / ((b : ℝ) ^ d - 1) -
          1 / ((b : ℝ) ^ d - 1) =
        ((b : ℝ) ^ r - 1) / ((b : ℝ) ^ d - 1) := by ring
  have hright :
      (2 : ℝ) ^ r / ((2 : ℝ) ^ d - 1) -
          1 / ((2 : ℝ) ^ d - 1) =
        ((2 : ℝ) ^ r - 1) / ((2 : ℝ) ^ d - 1) := by ring
  rw [hleft, hright]
  exact hupper.trans (hmiddle.trans hlower)

theorem shiftedRadixSupportAtom_sub_zero_le_two_mul_binary_sub_zero
    (b : ℕ) (A : Set ℕ) (N d : ℕ) (hb : 2 ≤ b) :
    shiftedRadixSupportAtom b A N d -
        shiftedRadixSupportAtom b A 0 d ≤
      2 * (shiftedSupportAtom A N d - shiftedSupportAtom A 0 d) := by
  classical
  by_cases hdA : d ∈ A
  · simpa [shiftedRadixSupportAtom, shiftedSupportAtom, hdA] using
      shiftedRadixAtom_sub_zero_le_two_mul_binary_sub_zero b N d hb
  · simp [shiftedRadixSupportAtom, shiftedSupportAtom, hdA]

/-- Every binary close return supplied by reciprocal summability transfers
to a close return at radix b. -/
theorem exists_shiftedRadixSupportAtom_closeReturn_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b)
    (hsum : Summable (reciprocalSupportTerm A))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧
      (∑' d : ℕ, shiftedRadixSupportAtom b A N d) <
        (∑' d : ℕ, shiftedRadixSupportAtom b A 0 d) + ε := by
  obtain ⟨N, hN, hnear⟩ :=
    exists_shiftedSupportAtom_closeReturn_of_summable_reciprocal
      A hsum (ε / 2) (by linarith)
  refine ⟨N, hN, ?_⟩
  have hradN := summable_shiftedRadixSupportAtom b A N hb
  have hrad0 := summable_shiftedRadixSupportAtom b A 0 hb
  have hbinN := summable_shiftedSupportAtom A N
  have hbin0 := summable_shiftedSupportAtom A 0
  have hsumle :
      (∑' d : ℕ, (shiftedRadixSupportAtom b A N d -
        shiftedRadixSupportAtom b A 0 d)) ≤
      ∑' d : ℕ, 2 * (shiftedSupportAtom A N d -
        shiftedSupportAtom A 0 d) := by
    exact Summable.tsum_le_tsum
      (fun d => shiftedRadixSupportAtom_sub_zero_le_two_mul_binary_sub_zero
        b A N d hb)
      (hradN.sub hrad0)
      ((hbinN.sub hbin0).mul_left 2)
  rw [(hradN.tsum_sub hrad0), (hbinN.sub hbin0).tsum_mul_left,
    (hbinN.tsum_sub hbin0)] at hsumle
  linarith

/-! ## Integer-gap endgame -/

/-- Every infinite support with convergent reciprocal mass gives an
irrational reciprocal-power subseries at every integer base b ≥ 2. -/
theorem irrational_erdosSupportSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (reciprocalSupportTerm A)) :
    Irrational (erdosSupportSeries b A) := by
  by_contra hrat
  have hvalue : HasRationalValue (erdosSupportSeries b A) :=
    (hasRationalValue_iff_not_irrational _).2 hrat
  obtain ⟨p, v, hv, hratValue⟩ := hvalue
  let T : ℕ → ℝ := fun N =>
    ∑' d : ℕ, shiftedRadixSupportAtom b A N d
  let u : ℕ → ℤ := Nat.rec p
    (fun N z => (b : ℤ) * z - ((v * supportCoeff A (N + 1) : ℕ) : ℤ))
  have hu0 : u 0 = p := rfl
  have huSucc : ∀ N : ℕ,
      u (N + 1) =
        (b : ℤ) * u N - ((v * supportCoeff A (N + 1) : ℕ) : ℤ) := by
    intro N
    rfl
  have hT0 : T 0 = erdosSupportSeries b A := by
    exact tsum_shiftedRadixSupportAtom_zero b A
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have huCast : ∀ N : ℕ, ((u N).cast : ℝ) = (v : ℝ) * T N := by
    intro N
    induction N with
    | zero =>
        rw [hu0, hT0, hratValue]
        field_simp
    | succ N ih =>
        rw [huSucc]
        push_cast
        rw [ih]
        have hstep := tsum_shiftedRadixSupportAtom_step b A N hb
        change (b : ℝ) * ((v : ℝ) * T N) -
            (v : ℝ) * supportCoeff A (N + 1) = (v : ℝ) * T (N + 1)
        change (b : ℝ) * T N - T (N + 1) =
            supportCoeff A (N + 1) at hstep
        nlinarith
  obtain ⟨N, hN, hnear⟩ :=
    exists_shiftedRadixSupportAtom_closeReturn_of_summable_reciprocal
      b A hb hsum (1 / (v : ℝ)) (by positivity)
  have hstrict :=
    shiftedRadixSupportAtom_zero_strictMinimum b A hb hA N hN
  have hstrictT : T 0 < T N := by
    simpa [T] using hstrict
  have hnearT : T N < T 0 + 1 / (v : ℝ) := by
    simpa [T] using hnear
  have hgapPos : (0 : ℝ) < ((u N - u 0 : ℤ) : ℝ) := by
    push_cast
    rw [huCast N, huCast 0]
    nlinarith [mul_pos hvR (sub_pos.mpr hstrictT)]
  have hgapLt : ((u N - u 0 : ℤ) : ℝ) < 1 := by
    push_cast
    rw [huCast N, huCast 0]
    have htailGap : T N - T 0 < 1 / (v : ℝ) := by
      exact sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hnearT)
    have hmul := mul_lt_mul_of_pos_left htailGap hvR
    have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvR
    rw [show (v : ℝ) * (1 / (v : ℝ)) = 1 by field_simp] at hmul
    nlinarith
  have hgapPosInt : 0 < u N - u 0 := by exact_mod_cast hgapPos
  have hgapLtInt : u N - u 0 < 1 := by exact_mod_cast hgapLt
  omega

#print axioms shiftedRadixAtom_sub_zero_le_two_mul_binary_sub_zero
#print axioms exists_shiftedRadixSupportAtom_closeReturn_of_summable_reciprocal
#print axioms irrational_erdosSupportSeries_of_summable_reciprocal

end

end Erdos257PeriodNoncollapse
