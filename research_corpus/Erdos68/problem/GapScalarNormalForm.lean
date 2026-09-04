import ErdosProblems.Erdos68.FactorialGapPlateauCore

/-!
# Erdős #68: gap scalar normal form and carry-stream reconstruction

The rounding carries `b_j = factorialGapStepCarry j` determine the
predecessor-gap scalar `factorialGapPredecessorGap m` through an exact finite
expansion with an explicit positive remainder:

`g_m = (∑_{j=m}^{J} (b_j + ε_j) · (m-1)!/j!) + (m-1)!/J! · g_(J+1)`

where `ε_j = 1/(j!-1)`.  The rearranged radix recurrence behind it is

`g_(m+1) = m · g_m - b_m - ε_m`.

Combined with the sharp three-window reading of the carry (`b_m = 1` exactly
when `1 + ε_m < m · g_m ≤ 2 + ε_m`), a finite block of certified digits gives
an exact domination certificate for `m · g_m`, hence a non-unit-carry
certificate at index `m` — one frontier miss of Erdős #68 per block.

No theorem here proves cofinality; each application certifies one index.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- Real prefix increment used throughout. -/
theorem real_prefix_eq_prev_add (m : ℕ) (hm : 2 ≤ m) :
    (((factorialGapPrefix m : ℚ) : ℝ)) =
      (((factorialGapPrefix (m - 1) : ℚ) : ℝ)) +
        1 / ((m.factorial : ℝ) - 1) := by
  exact_mod_cast factorialGapPrefix_eq_prev_add hm

/-- Rearranged radix recurrence: consecutive predecessor gaps satisfy the
exact affine recursion with the rounding carry as the subtracted digit. -/
theorem predGap_succ_eq (m : ℕ) (hm : 2 ≤ m) :
    factorialGapPredecessorGap (m + 1) =
      (m : ℝ) * factorialGapPredecessorGap m -
        (factorialGapStepCarry m : ℝ) -
          1 / ((m.factorial : ℝ) - 1) := by
  have hprefix := real_prefix_eq_prev_add m hm
  have hstep := strictFacTop_factorialGapPrefix_step (m := m) hm
  have hfacCast : ((m.factorial : ℝ)) =
      (m : ℝ) * ((m - 1).factorial : ℝ) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = k + 1 := ⟨m - 1, by omega⟩
    subst hk
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hdenNe : ((m.factorial : ℝ) - 1) ≠ 0 := by
    rw [hfacCast]
    have hge : ((m - 1).factorial : ℝ) ≥ (1 : ℝ) := by
      have hpos : (0 : ℕ) < (m - 1).factorial := Nat.factorial_pos _
      have hone : (1 : ℕ) ≤ (m - 1).factorial := by omega
      exact_mod_cast hone
    have hmG : (m : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hm
    refine ne_of_gt ?_
    nlinarith
  have hepsSplit : ((m.factorial : ℝ)) / ((m.factorial : ℝ) - 1) =
      (1 : ℝ) + 1 / ((m.factorial : ℝ) - 1) := by
    field_simp
    ring
  have hg : factorialGapPredecessorGap m =
      ((strictFacTop ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℤ) : ℝ) -
        ((m - 1).factorial : ℝ) * ((factorialGapPrefix (m - 1) : ℚ) : ℝ) := rfl
  show ((strictFacTop ((factorialGapPrefix (m + 1 - 1) : ℚ) : ℝ)
            (m + 1 - 1) : ℤ) : ℝ) -
        ((m + 1 - 1).factorial : ℝ) *
          ((factorialGapPrefix (m + 1 - 1) : ℚ) : ℝ) = _
  simp only [Nat.add_sub_cancel]
  have hstepR :
      ((strictFacTop ((factorialGapPrefix m : ℚ) : ℝ) m : ℤ) : ℝ) =
        (m : ℝ) *
            ((strictFacTop ((factorialGapPrefix (m - 1) : ℚ) : ℝ)
                (m - 1) : ℤ) : ℝ) +
          1 - (factorialGapStepCarry m : ℝ) := by
    exact_mod_cast hstep
  rw [hstepR, hg, hprefix, mul_add]
  have hprod : ((m.factorial : ℝ)) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) =
      (m : ℝ) * ((m - 1).factorial : ℝ) *
        ((factorialGapPrefix (m - 1) : ℚ) : ℝ) := by
    rw [hfacCast]
  rw [hprod]
  have hepsProd : ((m.factorial : ℝ)) *
      (1 / ((m.factorial : ℝ) - 1)) =
      (1 : ℝ) + 1 / ((m.factorial : ℝ) - 1) := by
    have hdenNe' : ((m.factorial : ℝ) - 1) ≠ 0 := hdenNe
    field_simp [hdenNe']
    try ring
  rw [hepsProd]
  ring

/-- One unrolling step of the carry-stream expansion, in the direction used
by induction: the gap at `m` splits into the current carry contribution plus
the rescaled successor gap. -/
theorem predGap_split (m : ℕ) (hm : 2 ≤ m) :
    factorialGapPredecessorGap m =
      ((factorialGapStepCarry m : ℝ) + 1 / ((m.factorial : ℝ) - 1)) /
        (m : ℝ) +
        factorialGapPredecessorGap (m + 1) / (m : ℝ) := by
  rw [predGap_succ_eq m hm]
  have hmNe : ((m : ℝ)) ≠ 0 := by positivity
  field_simp [hmNe]
  try ring

/-- Weight lemma: factorial ratio across one index. -/
private theorem factorialReal_succ_div {n : ℕ} :
    ((n.factorial : ℝ) / ((n + 1).factorial : ℝ)) =
      1 / ((n + 1 : ℕ) : ℝ) := by
  have h1 : ((n + 1).factorial : ℝ) = ((n + 1 : ℕ) : ℝ) * ((n.factorial : ℝ)) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hC : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hA : ((n.factorial : ℝ)) ≠ 0 := by positivity
  symm
  rw [div_eq_iff hC, h1, div_mul_eq_mul_div,
    mul_comm ((n + 1 : ℕ) : ℝ) ((n.factorial : ℝ)),
    div_self (mul_ne_zero hA hC)]

/-- Multiplicative distribution over a division: isolated so that no
`Finset.sum` is ever exposed to `field_simp`. -/
private theorem mul_add_div (x y w z : ℝ) :
    x * ((y + w) / z) = x * (y / z) + x * (w / z) := by
  rw [add_div, mul_add]

private theorem mul_div_swap (x y z : ℝ) :
    x * (y / z) = y * (x / z) := by
  field_simp

/-- **Exact finite carry-stream expansion.**  The predecessor gap at `m`
equals the weighted carry stream from `m` through `m+k` plus the explicitly
rescaled terminal gap at `m+k+1`. -/
theorem predGap_eq_carry_stream (m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    factorialGapPredecessorGap m =
      ∑ j ∈ Finset.Icc m (m + k),
        (((factorialGapStepCarry j : ℝ) + 1 / ((j.factorial : ℝ) - 1)) *
          (((m - 1).factorial : ℝ) / (j.factorial : ℝ))) +
        (((m - 1).factorial : ℝ) / ((m + k).factorial : ℝ)) *
          factorialGapPredecessorGap (m + k + 1) := by
  induction k with
  | zero =>
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.add_zero]
      rw [predGap_split m hm]
      have hw1 : (((m - 1).factorial : ℝ) / ((m : ℕ).factorial : ℝ)) =
          1 / (m : ℝ) := by
        have hw0 : ((m - 1).factorial : ℝ) /
            ((m - 1 + 1).factorial : ℝ) =
            1 / ((m - 1 + 1 : ℕ) : ℝ) := factorialReal_succ_div (n := m - 1)
        have him : m - 1 + 1 = m := by omega
        rwa [him] at hw0
      rw [hw1]
      push_cast
      ring
  | succ k ih =>
      have hsplitSum :
          Finset.Icc m (m + (k + 1)) =
            insert (m + k + 1) (Finset.Icc m (m + k)) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hrec := predGap_split (m + k + 1) (by omega)
      set c : ℝ := ((m + k + 1 : ℕ) : ℝ) with hcdef
      have hcPos : (0 : ℝ) < c := by rw [hcdef]; positivity
      set W : ℝ := ((m - 1).factorial : ℝ) / ((m + k).factorial : ℝ) with hWdef
      set W' : ℝ := ((m - 1).factorial : ℝ) /
        ((m + k + 1).factorial : ℝ) with hWpdef
      have hD : ((m + k + 1).factorial : ℝ) =
          ((m + k).factorial : ℝ) * ((m + k + 1 : ℕ) : ℝ) := by
        have hnat : (m + k + 1).factorial =
            (m + k + 1) * (m + k).factorial := Nat.factorial_succ _
        rw [hnat]
        push_cast
        ring
      have hcW : W = c * W' := by
        rw [hWdef, hWpdef, hD]
        have hB : ((m + k).factorial : ℝ) ≠ 0 := by positivity
        have hCC : ((m + k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hB, hCC]
        try ring
      rw [hsplitSum]
      rw [Finset.sum_insert (by simp [Finset.mem_Icc] <;> omega)]
      rw [ih]
      have hE : (((m + k + 1).factorial : ℝ) - 1) ≠ 0 := by
        have h6 : ((3 : ℕ).factorial) ≤ (m + k + 1).factorial :=
          Nat.factorial_le (show 3 ≤ m + k + 1 from by omega)
        norm_num at h6
        have hge2 : (2 : ℕ) ≤ (m + k + 1).factorial := by omega
        have h2r : ((m + k + 1).factorial : ℝ) ≥ (2 : ℝ) := by
          calc ((m + k + 1).factorial : ℝ)
              = (((m + k + 1).factorial : ℕ) : ℝ) := rfl
            _ ≥ ((2 : ℕ) : ℝ) := by exact_mod_cast hge2
            _ = (2 : ℝ) := by norm_num
        linarith
      have hWr : W / c = W' := by
        rw [hWdef, hWpdef, hD]
        simp only [hcdef]
        have hB : ((m + k).factorial : ℝ) ≠ 0 := by positivity
        have hCC : ((m + k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hB, hCC]
      have hkey : W * factorialGapPredecessorGap (m + k + 1) =
          ((factorialGapStepCarry (m + k + 1) : ℝ) +
              1 / (((m + k + 1).factorial : ℝ) - 1)) * W' +
            W' * factorialGapPredecessorGap (m + k + 2) := by
        rw [hrec, mul_add]
        have s2 : W * (((factorialGapStepCarry (m + k + 1) : ℝ) +
              1 / (((m + k + 1).factorial : ℝ) - 1)) / c) =
            ((factorialGapStepCarry (m + k + 1) : ℝ) +
              1 / (((m + k + 1).factorial : ℝ) - 1)) * (W / c) :=
          mul_div_swap _ _ _
        have s3 : W * (factorialGapPredecessorGap (m + k + 2) / c) =
            factorialGapPredecessorGap (m + k + 2) * (W / c) :=
          mul_div_swap _ _ _
        rw [s2, s3, hWr]
        ring
      rw [hkey, ← hWpdef]
      have hbridge : (((m - 1).factorial : ℝ) /
            (((m + (k + 1)).factorial : ℕ) : ℝ)) *
          factorialGapPredecessorGap (m + (k + 1) + 1)
          = W' * factorialGapPredecessorGap (m + (k + 1) + 1) := by
        have hidx : m + (k + 1) = m + k + 1 := by omega
        rw [hidx, hWpdef]
      rw [hbridge]
      have heqg : factorialGapPredecessorGap (m + k + 2) =
          factorialGapPredecessorGap (m + (k + 1) + 1) :=
        congrArg factorialGapPredecessorGap (by omega)
      rw [heqg]
      try ring

/-- The remainder of the finite expansion is positive and bounded by its
weight, because every predecessor gap lies in `(0, 1]`. -/
theorem carry_stream_remainder_bounds (m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    (0 : ℝ) < ((m - 1).factorial : ℝ) / ((m + k).factorial : ℝ) *
        factorialGapPredecessorGap (m + k + 1) ∧
      ((m - 1).factorial : ℝ) / ((m + k).factorial : ℝ) *
        factorialGapPredecessorGap (m + k + 1) ≤
        ((m - 1).factorial : ℝ) / ((m + k).factorial : ℝ) := by
  obtain ⟨hpos, hle⟩ := factorialGapPredecessorGap_pos_le_one (m + k + 1)
  have hwPos : (0 : ℝ) < ((m - 1).factorial : ℝ) / ((m + k).factorial : ℝ) := by
    refine div_pos ?_ (by positivity)
    have hfact : (0 : ℕ) < (m - 1).factorial := Nat.factorial_pos _
    positivity
  constructor
  · nlinarith
  · nlinarith

/-- **Sharp three-window reading of the carry.**  The unit carry occurs
exactly when the scaled predecessor gap lands in `(1 + ε_m, 2 + ε_m]`. -/
theorem factorialGapStepCarry_eq_one_iff_scaled_gap (m : ℕ) (hm : 3 ≤ m) :
    factorialGapStepCarry m = 1 ↔
      1 + 1 / ((m.factorial : ℝ) - 1) <
          (m : ℝ) * factorialGapPredecessorGap m ∧
        (m : ℝ) * factorialGapPredecessorGap m ≤
          2 + 1 / ((m.factorial : ℝ) - 1) := by
  have hbDef : factorialGapStepCarry m =
      -⌊(1 : ℝ) + 1 / ((m.factorial : ℝ) - 1) -
        (m : ℝ) * factorialGapPredecessorGap m⌋ := rfl
  set x : ℝ := (1 : ℝ) + 1 / ((m.factorial : ℝ) - 1) -
    (m : ℝ) * factorialGapPredecessorGap m with hx
  rw [hbDef]
  have hflip : (-⌊x⌋ = 1) ↔ (⌊x⌋ = (-1 : ℤ)) := by
    constructor <;> intro h <;> omega
  rw [hflip, Int.floor_eq_iff]
  have hz : (((-1 : ℤ) : ℝ) + (1 : ℝ)) = (0 : ℝ) := by norm_num
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩ <;> linarith [hx, h1, h2, hz]
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith [hx, h2], by linarith [hx, h1]⟩

/-- Frontier consumer: a strictly dominant scaled gap forces a non-unit
carry, i.e. a strict-successor divisibility miss at index `m`. -/
theorem factorialGapStepCarry_ne_one_of_scaled_gap_gt (m : ℕ) (hm : 3 ≤ m)
    (hgt : 2 + 1 / ((m.factorial : ℝ) - 1) <
        (m : ℝ) * factorialGapPredecessorGap m) :
    factorialGapStepCarry m ≠ 1 := by
  intro hunit
  have hiff := factorialGapStepCarry_eq_one_iff_scaled_gap m hm
  have hub := hiff.mp hunit
  linarith

/-- **Digit-stream certificate.**  If the finite weighted carry stream from
`m` through `m+k` dominates `(2 + ε_m)/m`, then index `m` is a frontier miss.
All hypotheses are integer-checkable given certified digits `b_j`. -/
theorem factorialGapStepCarry_ne_one_of_stream_domination
    (m : ℕ) (hm : 3 ≤ m) (k : ℕ)
    (hdom :
      (2 + 1 / ((m.factorial : ℝ) - 1)) / (m : ℝ) <
        ∑ j ∈ Finset.Icc m (m + k),
          (((factorialGapStepCarry j : ℝ) + 1 / ((j.factorial : ℝ) - 1)) *
            (((m - 1).factorial : ℝ) / (j.factorial : ℝ)))) :
    factorialGapStepCarry m ≠ 1 := by
  have hexact := predGap_eq_carry_stream m (by omega) k
  obtain ⟨hremPos, _⟩ := carry_stream_remainder_bounds m (by omega) k
  have hsumLt : (∑ j ∈ Finset.Icc m (m + k),
      (((factorialGapStepCarry j : ℝ) + 1 / ((j.factorial : ℝ) - 1)) *
        (((m - 1).factorial : ℝ) / (j.factorial : ℝ)))) <
      factorialGapPredecessorGap m := by
    rw [hexact]
    linarith
  have hge : (2 + 1 / ((m.factorial : ℝ) - 1)) / (m : ℝ) <
      factorialGapPredecessorGap m := lt_trans hdom hsumLt
  have hmPos : (0 : ℝ) < (m : ℝ) := by positivity
  have hmul : (2 + 1 / ((m.factorial : ℝ) - 1)) <
      (m : ℝ) * factorialGapPredecessorGap m := by
    rw [mul_comm]
    exact (div_lt_iff₀ hmPos).mp hge
  exact factorialGapStepCarry_ne_one_of_scaled_gap_gt m hm hmul

#print axioms predGap_succ_eq
#print axioms predGap_eq_carry_stream
#print axioms carry_stream_remainder_bounds
#print axioms factorialGapStepCarry_eq_one_iff_scaled_gap
#print axioms factorialGapStepCarry_ne_one_of_stream_domination

end ErdosProblems.Erdos68
