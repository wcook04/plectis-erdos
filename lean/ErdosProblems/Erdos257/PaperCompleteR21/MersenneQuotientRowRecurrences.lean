import Erdos249257.BooleanMobiusExactTransition
import Erdos249257.BooleanMobiusSkipRow
import Erdos249257.BooleanMobiusCriticalCapacityGeometric
import Erdos249257.BooleanMobiusGlobalRepair

/-!
Paper-form restatements of four asserted environments from the long
Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`.

Notation of the paper (`record:257bm-d2`, `record:257bm-d3`):
`q(M,d) = localMersenneQuotient M d`, `Q(D,M) = localPrefixQuotient D M`,
`S(D,k,M) = localBinarySuffix D k M`, `H(D,k,n) = localRepairInteger D k n`,
`c_D(n) = endpointDivisorContribution D n`, `w(c) = mersenneWeightRat c`,
`X_D(2) = localMersennePrefixValue D`.

* `record:257bm-i1a` (`a257_front.tex:4424`), "The next floor quotient":
  `paper_next_floor_quotient`, `paper_next_floor_quotient_no_fixed_point`,
  `paper_next_quotient_sum`.
* `record:257bm-i1c` (`a257_front.tex:4451`), "The signed endpoint recurrence":
  `paper_signed_endpoint_recurrence`, `paper_endpoint_term_counts_divisors`,
  `paper_signed_endpoint_defect_succ`,
  `paper_repair_integer_eq_endpoint_defect`.
* `record:257bm-i6` (`a257_front.tex:4515`), "An unconditional bound with one
  extra bit": `paper_unconditional_bound_one_extra_bit`.
* `record:257bm-c10` (`a257_front.tex:4186`), "A finite sum from a skipped
  prefix": `paper_exact_row_from_skipped_prefix`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257

/-! ## `record:257bm-i1a` -- the next floor quotient -/

/-- Paper display of `record:257bm-i1a`: for `d ≥ 2` and `M ≥ 0`,
`q(M+1,d) = 2 q(M,d) + 1_{d | M+1}`. -/
theorem paper_next_floor_quotient {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient (M + 1) d =
      2 * localMersenneQuotient M d + (if d ∣ M + 1 then 1 else 0) :=
  localMersenneQuotient_endpoint_succ hd

/-- The reason the environment gives for the display:
`q(M,d) = ∑_{j=1}^{⌊M/d⌋} 2^(M-jd)`. -/
theorem paper_floor_quotient_geometric_sum {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = ∑ j ∈ Finset.Icc 1 (M / d), 2 ^ (M - j * d) := by
  classical
  rw [localMersenneQuotient_eq_geometric hd, localMersenneGeometricQuotient,
    Finset.mul_sum]
  have hdiv : M / d * d + M % d = M := Nat.div_add_mod' M d
  have himg : Finset.Icc 1 (M / d) =
      (Finset.range (M / d)).image (fun i ↦ M / d - i) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨M / d - j, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [himg, Finset.sum_image
    (by intro x hx y hy hxy
        simp only [Finset.coe_range, Set.mem_Iio] at hx hy
        have hxy' : M / d - x = M / d - y := hxy
        omega)]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  have hle : i * d ≤ M / d * d := Nat.mul_le_mul_right d (by omega)
  have hsub : (M / d - i) * d = M / d * d - i * d := by rw [Nat.sub_mul]
  have hexp : M - (M / d - i) * d = M % d + i * d := by omega
  rw [hexp, pow_add, ← pow_mul, Nat.mul_comm d i]

/-- "A quotient doubles or doubles plus one; it does not remain unchanged
except when both values are zero." -/
theorem paper_next_floor_quotient_no_fixed_point {M d : ℕ} (hd : 2 ≤ d)
    (hfix : localMersenneQuotient (M + 1) d = localMersenneQuotient M d) :
    localMersenneQuotient M d = 0 ∧ localMersenneQuotient (M + 1) d = 0 := by
  have hstep := localMersenneQuotient_endpoint_succ (M := M) (d := d) hd
  split_ifs at hstep <;> omega

/-- "Summing over a fixed finite support gives the corresponding update with
added term `c_D(M+1)`." -/
theorem paper_next_quotient_sum {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M + endpointDivisorContribution D (M + 1) :=
  localPrefixQuotient_succ hD

/-! ## `record:257bm-i1c` -- the signed endpoint recurrence -/

/-- Paper display of `record:257bm-i1c`: the signed next-step expression is
`H(D,k,n) = 2 S(D,k,n-1) + 1 - c_D(n)`. -/
theorem paper_signed_endpoint_recurrence (D : Finset ℕ) (k n : ℕ) :
    localRepairInteger D k n =
      2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
        (endpointDivisorContribution D n : ℤ) :=
  rfl

/-- "The last term counts the selected exponents dividing the new endpoint." -/
theorem paper_endpoint_term_counts_divisors {D : Finset ℕ} {n : ℕ}
    (hn : 0 < n) :
    endpointDivisorContribution D n = (D.filter fun d ↦ d ∣ n).card ∧
      endpointDivisorContribution D n = supportCoeff (↑D : Set ℕ) n :=
  ⟨rfl, endpointDivisorContribution_eq_supportCoeff hn⟩

/-- The same recurrence in the untruncated signed form. -/
theorem paper_signed_endpoint_defect_succ {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    localEndpointDefect D (M + 1) =
      2 * localEndpointDefect D M + 1 -
        (endpointDivisorContribution D (M + 1) : ℤ) :=
  localEndpointDefect_succ hM hD

/-- Below the endpoint target the two forms agree literally. -/
theorem paper_repair_integer_eq_endpoint_defect {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hbelow : localPrefixQuotient D M ≤ halfEndpointTarget M) :
    localRepairInteger D 1 (M + 1) = localEndpointDefect D (M + 1) :=
  localRepairInteger_eq_localEndpointDefect_succ hM hD hbelow

/-! ## `record:257bm-i6` -- an unconditional bound with one extra bit -/

/-- Paper display of `record:257bm-i6`: for every `c ≥ 4` and every below-half
core `D ⊆ [2,c)` with deficit `< w(c)`, `S(D,1,2c-2) < 2^(c-1)`; the support
cardinality bound `|D| ≤ c-2` quoted in the same environment is recorded as
the second clause. -/
theorem paper_unconditional_bound_one_extra_bit {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 1) ∧ D.card ≤ c - 2 := by
  classical
  refine ⟨localBinarySuffix_two_mul_sub_two_lt_upperHalfCapacity
    hc hD hbelow hskip, ?_⟩
  have hsub : D ⊆ Finset.Ico 2 c := fun d hd ↦ Finset.mem_Ico.mpr (hD d hd)
  calc D.card ≤ (Finset.Ico 2 c).card := Finset.card_le_card hsub
    _ = c - 2 := by simp

/-- The sharper additive estimate the environment records before using
`|D| ≤ c-2 ≤ 2^(c-2)`: `S(D,1,2c-2) < 2^(c-2) + |D|`. -/
theorem paper_sharper_additive_estimate {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) + D.card := by
  classical
  set M := 2 * c - 2 with hMdef
  have hM1 : 1 ≤ M := by omega
  have hscaled := scaled_localMersennePrefixValue (D := D) (M := M)
    (fun d hd ↦ (hD d hd).1)
  have hFnonneg : 0 ≤ localFractionMass D M :=
    Finset.sum_nonneg fun d hd ↦
      (localMersenneFraction_pos (M := M) (hD d hd).1).le
  have hFcard : localFractionMass D M ≤ (D.card : ℚ) := by
    unfold localFractionMass
    calc ∑ d ∈ D, localMersenneFraction M d
        ≤ ∑ _d ∈ D, (1 : ℚ) :=
          Finset.sum_le_sum fun d hd ↦
            (localMersenneFraction_lt_one (hD d hd).1).le
      _ = (D.card : ℚ) := by simp
  have hpowM : (2 : ℚ) ^ M * (1 / 2 : ℚ) = (2 : ℚ) ^ (M - 1) := by
    calc (2 : ℚ) ^ M * (1 / 2 : ℚ)
        = 2 ^ ((M - 1) + 1) * (1 / 2 : ℚ) := by congr 2 <;> omega
      _ = (2 : ℚ) ^ (M - 1) := by rw [pow_succ]; ring
  have hposM : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
  have hQlt : (localPrefixQuotient D M : ℚ) < (2 : ℚ) ^ (M - 1) := by
    have hmul := mul_lt_mul_of_pos_left hbelow hposM
    rw [hscaled, hpowM] at hmul
    linarith
  have hden : (0 : ℚ) < (2 : ℚ) ^ c - 1 := by
    have h4 : (2 : ℚ) ^ 4 ≤ (2 : ℚ) ^ c := pow_le_pow_right₀ (by norm_num) hc
    norm_num at h4
    linarith
  have hkey : (2 : ℚ) ^ (M - 1) - (localPrefixQuotient D M : ℚ) -
      localFractionMass D M < (2 : ℚ) ^ M / ((2 : ℚ) ^ c - 1) := by
    have h := mul_lt_mul_of_pos_left hskip hposM
    rw [mul_sub, hpowM, hscaled, show mersenneWeightRat c =
      1 / ((2 : ℚ) ^ c - 1) from rfl] at h
    calc (2 : ℚ) ^ (M - 1) - (localPrefixQuotient D M : ℚ) -
            localFractionMass D M
        = (2 : ℚ) ^ (M - 1) -
            ((localPrefixQuotient D M : ℚ) + localFractionMass D M) := by ring
      _ < (2 : ℚ) ^ M * (1 / ((2 : ℚ) ^ c - 1)) := h
      _ = (2 : ℚ) ^ M / ((2 : ℚ) ^ c - 1) := by ring
  have hsplit : (2 : ℚ) ^ M / ((2 : ℚ) ^ c - 1) <
      (2 : ℚ) ^ (c - 2) + 1 / 2 := by
    rw [div_lt_iff₀ hden]
    have hcc : (2 : ℚ) ^ c = 4 * (2 : ℚ) ^ (c - 2) := by
      have hsum : (c - 2) + 2 = c := by omega
      calc (2 : ℚ) ^ c = 2 ^ ((c - 2) + 2) := by rw [hsum]
        _ = 2 ^ (c - 2) * 2 ^ 2 := pow_add _ _ _
        _ = 4 * 2 ^ (c - 2) := by ring
    have hMM : (2 : ℚ) ^ M = 4 * ((2 : ℚ) ^ (c - 2)) ^ 2 := by
      have hsum : (c - 2) * 2 + 2 = M := by omega
      calc (2 : ℚ) ^ M = 2 ^ ((c - 2) * 2 + 2) := by rw [hsum]
        _ = 2 ^ ((c - 2) * 2) * 2 ^ 2 := pow_add _ _ _
        _ = ((2 : ℚ) ^ (c - 2)) ^ 2 * 2 ^ 2 := by rw [pow_mul]
        _ = 4 * ((2 : ℚ) ^ (c - 2)) ^ 2 := by ring
    have hP4 : (4 : ℚ) ≤ (2 : ℚ) ^ (c - 2) := by
      calc (4 : ℚ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (c - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hMM, hcc]
    nlinarith [hP4]
  have hsuffix : (localBinarySuffix D 1 M : ℚ) =
      (2 : ℚ) ^ (M - 1) - (localPrefixQuotient D M : ℚ) - 1 := by
    unfold localBinarySuffix
    have hQnat : localPrefixQuotient D M < 2 ^ (M - 1) := by exact_mod_cast hQlt
    have hone : (1 : ℕ) ≤ 2 ^ (M - 1) := Nat.one_le_pow _ _ (by norm_num)
    have hid : (2 ^ (M - 1) - localPrefixQuotient D M - 1 : ℕ) +
        localPrefixQuotient D M + 1 = 2 ^ (M - 1) := by omega
    have hcast := congrArg (fun x : ℕ ↦ (x : ℚ)) hid
    push_cast at hcast
    linarith
  have hfinal : ((localBinarySuffix D 1 M : ℕ) : ℚ) <
      ((2 ^ (c - 2) + D.card : ℕ) : ℚ) := by
    push_cast
    rw [hsuffix]
    linarith
  exact_mod_cast hfinal

private lemma self_le_two_pow : ∀ m : ℕ, m ≤ 2 ^ m := by
  intro m
  induction m with
  | zero => norm_num
  | succ m ih =>
      have hone : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
      calc m + 1 ≤ 2 ^ m + 1 := by omega
        _ ≤ 2 ^ m + 2 ^ m := by omega
        _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

/-- The remaining clauses of `record:257bm-i6`: the chain
`|D| ≤ c-2 ≤ 2^(c-2)`, the fact that the critical-capacity inequality would
follow by excluding the integer band `[2^(c-2), 2^(c-2)+c-3]`, and the count
of `c-2` integers in that band. -/
theorem paper_capacity_band_exclusion {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    D.card ≤ c - 2 ∧ c - 2 ≤ 2 ^ (c - 2) ∧
      (Finset.Icc (2 ^ (c - 2)) (2 ^ (c - 2) + (c - 3))).card = c - 2 ∧
      (localBinarySuffix D 1 (2 * c - 2) ∉
          Finset.Icc (2 ^ (c - 2)) (2 ^ (c - 2) + (c - 3)) →
        localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) := by
  classical
  have hcard : D.card ≤ c - 2 :=
    (paper_unconditional_bound_one_extra_bit hc hD hbelow hskip).2
  have hadd := paper_sharper_additive_estimate hc hD hbelow hskip
  refine ⟨hcard, self_le_two_pow (c - 2), by rw [Nat.card_Icc]; omega, ?_⟩
  intro hout
  simp only [Finset.mem_Icc, not_and_or, not_le] at hout
  omega

/-! ## `record:257bm-c10` -- a finite sum from a skipped prefix -/

/-- Paper display of `record:257bm-c10`: for `c ≥ 4` and
`D ⊆ {2,…,c-1}` with `0 < 1/2 - X_D(2) < 1/(2^c-1)` there is `E` with
`D ⊆ E ⊆ {2,…,2c-2}` and `Q(E,2c-2) = 2^(2c-3) - 1`.

The support-extension clause `D ⊆ E` is the reason this is proved here rather
than quoted from `exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCore`,
whose conclusion forgets it. -/
theorem paper_exact_row_from_skipped_prefix {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * c - 2) ∧
      localPrefixQuotient E (2 * c - 2) = 2 ^ (2 * c - 3) - 1 := by
  classical
  let M := 2 * c - 2
  obtain ⟨y, hylen, hybool, hyvalue⟩ :=
    exists_upperHalfBooleanWord_of_skippedCore hc hD hbelow hskip
  let H := upperSupportFromWord M y
  refine ⟨D ∪ H, Finset.subset_union_left, ?_, ?_⟩
  · intro d hd
    rw [Finset.mem_union] at hd
    rcases hd with hdD | hdH
    · have hdcore := hD d hdD
      exact ⟨hdcore.1, by omega⟩
    · have hdlo := upperSupportFromWord_lower_bound
          (M := M) (y := y) (by simp [M, hylen]; omega) hdH
      have hdhi := upperSupportFromWord_le_top hdH
      refine ⟨?_, hdhi⟩
      simp [M, hylen] at hdlo
      omega
  · have hdisj : Disjoint D H := by
      rw [Finset.disjoint_left]
      intro d hdD hdH
      have hdlo := upperSupportFromWord_lower_bound
        (M := M) (y := y) (by simp [M, hylen]; omega) hdH
      have hdlt := (hD d hdD).2
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
    have hDadm : localPrefixQuotient D M ≤ 2 ^ (M - 1) - 1 := by
      have hscaled := scaled_localMersennePrefixValue
        (D := D) (M := M) (fun d hd ↦ (hD d hd).1)
      have hpowPos : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
      have hlt := mul_lt_mul_of_pos_left hbelow hpowPos
      rw [hscaled] at hlt
      have hFnonneg : 0 ≤ localFractionMass D M := by
        unfold localFractionMass
        exact Finset.sum_nonneg fun d hd ↦
          (localMersenneFraction_pos (M := M) (hD d hd).1).le
      have hq : (localPrefixQuotient D M : ℚ) < (2 : ℚ) ^ (M - 1) := by
        have hhalf : (2 : ℚ) ^ M * (1 / 2 : ℚ) = (2 : ℚ) ^ (M - 1) := by
          have hMpos : 1 ≤ M := by dsimp [M]; omega
          calc
            (2 : ℚ) ^ M * (1 / 2 : ℚ) =
                2 ^ ((M - 1) + 1) * (1 / 2 : ℚ) := by congr 2 <;> omega
            _ = (2 : ℚ) ^ (M - 1) := by rw [pow_succ]; ring
        rw [hhalf] at hlt
        linarith
      have hqNat : localPrefixQuotient D M < 2 ^ (M - 1) := by
        exact_mod_cast hq
      omega
    have hsuffix : localPrefixQuotient D M + localBinarySuffix D 1 M =
        2 ^ (M - 1) - 1 := by
      unfold localBinarySuffix
      have hMpos : 1 ≤ M := by dsimp [M]; omega
      have hpowOne : 1 ≤ 2 ^ (M - 1) := Nat.one_le_pow _ _ (by norm_num)
      have hQpow : localPrefixQuotient D M < 2 ^ (M - 1) := by omega
      omega
    have htarget : M - 1 = 2 * c - 3 := by dsimp [M]; omega
    rw [show (2 * c - 2) = M from rfl, hunion, hH, hyvalue, ← htarget]
    simpa [M] using hsuffix

#print axioms paper_next_floor_quotient
#print axioms paper_floor_quotient_geometric_sum
#print axioms paper_sharper_additive_estimate
#print axioms paper_capacity_band_exclusion
#print axioms paper_next_floor_quotient_no_fixed_point
#print axioms paper_next_quotient_sum
#print axioms paper_signed_endpoint_recurrence
#print axioms paper_endpoint_term_counts_divisors
#print axioms paper_signed_endpoint_defect_succ
#print axioms paper_repair_integer_eq_endpoint_defect
#print axioms paper_unconditional_bound_one_extra_bit
#print axioms paper_exact_row_from_skipped_prefix

end ErdosProblems.Erdos257.PaperCompleteR21
