import ErdosProblems.Erdos269.DyadicShellSummability

/-!
# Erdős #269: extinction of the integral branch through pinning windows

The bounded-radix dichotomy leaves exactly one branch between the genuine
infinite tail and cofinal escape: an exact integral normalized state.  This
module lands the structural facts that turn that branch into a decidable,
computationally mapped object.

## 1. Positivity and the pinning identity

Every genuine tail is strictly positive (each shell contains `2^a`).
Unrolling the shell decomposition gives the exact pinning identity

`X_a = d_a / b_a + X_(a+1) / b_a`,

so every true state lies strictly above its window anchor `d_a / b_a`.
In particular, when `b_a` divides `d_a`, the anchor is already an integer
and integrality would force `X_(a+1) = 0`, which positivity forbids: such
scales are killed outright.

## 2. Upward closure

The recurrence has integer coefficients, so one integral state makes every
later state integral.  The integral-index set is empty or a final segment,
so the whole question concentrates on a first integral index.

## 3. Iterated pinning and forced equality

Iterating the pinning identity expresses every true state as a finite
digit sum plus a remainder that carries another factor `2^-k` per shell
(because every block radix is at least two).  Any real orbit following the
recurrence from index `A` onward inside windows of a width function that
reproduces under the recurrence and vanishes against `2^-k` therefore
satisfies `|y_A - X_A| <= width (A+k) / 2^k -> 0`, hence equals the true
state.  Consequently an integer seed surviving all windows forever forces
the true state itself to be integral - exactly the quantity the companion
experiment `check_erdos269_integral_branch.py` measures.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- The genuine infinite normalized tail state. -/
noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a

theorem threePrimeHeight235_cast_pos (x : ℕ) :
    (0 : ℝ) < (threePrimeHeight 2 3 5 x : ℝ) := by
  unfold threePrimeHeight
  positivity

theorem dyadicBlockBase235_pos (a : ℕ) : 0 < dyadicBlockBase235 a := by
  rcases dyadicBlockBase235_cases a with h | h | h | h <;>
    simp [h]

theorem dyadicShellMassR235_pos (a : ℕ) : 0 < dyadicShellMassR235 a := by
  have hmem : (a, 0, 0) ∈ dyadicSmoothShell235 a := by
    refine mem_dyadicSmoothShell235_iff.mpr ?_
    simp only [smooth3Val, pow_succ, mul_one]
    constructor
    · exact le_refl _
    · exact Nat.lt_succ_self _
  have hsingle : ((threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ))⁻¹ ≤
      ∑ e ∈ dyadicSmoothShell235 a,
        ((threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℝ))⁻¹ := by
    refine Finset.single_le_sum (f := fun e =>
      ((threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℝ))⁻¹)
      ?_ ?_
    · intro e _
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · simpa using hmem
  have hHpos := threePrimeHeight235_cast_pos (2 ^ (a + 1))
  have hinv : (0 : ℝ) < (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ)⁻¹ :=
    inv_pos.mpr hHpos
  unfold dyadicShellMassR235 dyadicShellMassQ235
  have hdiv : (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ)⁻¹
      = 1 / (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) := rfl
  rw [hdiv] at hsingle ⊢
  linarith

theorem trueNormalizedState_pos (a : ℕ) : 0 < trueNormalizedState a :=
  mul_pos threePrimeHeight235_cast_pos _ (dyadicShellMassR235_pos a)

/-- **Pinning identity.**  Every true state sits exactly one future state
above its anchor digit quotient. -/
theorem trueNormalizedState_pinning (a : ℕ) :
    trueNormalizedState a =
      (dyadicOrderedBlockDigit235 a : ℝ) / (dyadicBlockBase235 a : ℝ) +
        trueNormalizedState (a + 1) / (dyadicBlockBase235 a : ℝ) := by
  set Hnext : ℝ := (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) with Hnext_def
  set Hcur : ℝ := (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) with Hcur_def
  set base : ℝ := (dyadicBlockBase235 a : ℝ) with base_def
  have hsucc : Hnext = base * Hcur := by
    exact_mod_cast threePrimeHeight_dyadicBlock_succ a
  have hdigit : Hnext / 2 * dyadicShellMassR235 a =
      (dyadicOrderedBlockDigit235 a : ℝ) :=
    half_threePrimeHeight_mul_dyadicShellMassR235 a
  have hsplit : dyadicShellTsumTailR235 a =
      dyadicShellMassR235 a + dyadicShellTsumTailR235 (a + 1) :=
    dyadicShellTsumTailR235_eq_shell_add a
  have hbpos : 0 < base := dyadicBlockBase235_pos a
  unfold trueNormalizedState dyadicNormalizedTailStateR235
  rw [hsplit]
  field_simp
  nlinarith [hdigit]

/-- **Zero-gap kill.**  When the block radix divides the ordered digit, the
anchor is already an integer and positivity of the next state forbids
integrality outright. -/
theorem zero_gap_digit_ne_integral (a : ℕ)
    (hgap : (dyadicBlockBase235 a : ℤ) ∣ dyadicOrderedBlockDigit235 a)
    (z : ℤ) : trueNormalizedState a ≠ (z : ℝ) := by
  intro heq
  have hpin := trueNormalizedState_pinning a
  obtain ⟨k, hk⟩ := hgap
  have hbpos : (0 : ℝ) < (dyadicBlockBase235 a : ℝ) := dyadicBlockBase235_pos a
  have hcancast : ((k * dyadicBlockBase235 a : ℤ) : ℝ)
      = (dyadicOrderedBlockDigit235 a : ℝ) := by
    rw [hk] |> fun h => by push_cast at h ⊢; omega
  have hanchor :
      (dyadicOrderedBlockDigit235 a : ℝ) / (dyadicBlockBase235 a : ℝ)
        = (k : ℝ) := by
    have hprod : (dyadicOrderedBlockDigit235 a : ℤ)
        = k * (dyadicBlockBase235 a : ℤ) := by
      omega
    have : (dyadicOrderedBlockDigit235 a : ℝ)
        = (k : ℝ) * (dyadicBlockBase235 a : ℝ) := by
      exact_mod_cast hprod
    rw [this]
    field_simp
  have hterm : 0 < trueNormalizedState (a + 1) / (dyadicBlockBase235 a : ℝ) :=
    div_pos (trueNormalizedState_pos _) hbpos
  rw [heq, hanchor] at hpin
  linarith

/-- **Upward closure.**  One integral state makes all later states
integral, because the recurrence has integer coefficients. -/
theorem integral_state_upward_closed {a : ℕ} {z : ℤ}
    (hint : trueNormalizedState a = (z : ℝ)) :
    ∀ n, a ≤ n → ∃ z' : ℤ, trueNormalizedState n = (z' : ℝ) := by
  intro n hn
  induction hn with
  | refl => exact ⟨z, hint⟩
  | step _ ih =>
    obtain ⟨z', hz'⟩ := ih
    refine ⟨(dyadicBlockBase235 _ : ℤ) * z' -
      dyadicOrderedBlockDigit235 _, ?_⟩
    rw [dyadicNormalizedShellTsumTailR235_succ _, hz']
    push_cast
    ring

/-! ## Iterated pinning -/

/-- Two-shell collapse: iterating the pinning identity `k` times bounds the
state by a digit sum carrying one factor of `2^-i` per shell plus a final
remainder under `2^-k`.  Only `b >= 2` is used. -/
theorem trueNormalizedState_le_iterated (m k : ℕ) :
    trueNormalizedState m ≤
      ∑ i ∈ Finset.range k,
        ((dyadicOrderedBlockDigit235 (m + i) : ℝ) / 2 ^ (i + 1)) +
        trueNormalizedState (m + k) / 2 ^ k := by
  induction k with
  | zero => simpa using le_refl _
  | succ k ih =>
    have hpin := trueNormalizedState_pinning m
    have hb2 : (2 : ℝ) ≤ (dyadicBlockBase235 m : ℝ) :=
      mod_cast (dyadicBlockBase235_mem_interval m).1
    have hbpos : (0:ℝ) < (dyadicBlockBase235 m : ℝ) := dyadicBlockBase235_pos m
    -- apply the induction hypothesis one shell deeper
    have hdeep :
        trueNormalizedState (m + 1) ≤
          ∑ i ∈ Finset.range k,
            ((dyadicOrderedBlockDigit235 (m + 1 + i) : ℝ) / 2 ^ (i + 1)) +
            trueNormalizedState (m + 1 + k) / 2 ^ k := by
      simpa [Nat.add_comm 1 k, Nat.add_assoc] using
        trueNormalizedState_le_iterated (m + 1) k
    -- reindex the deeper digit sum onto anchors m + i
    have hreindex :
        (∑ i ∈ Finset.range k,
            ((dyadicOrderedBlockDigit235 (m + 1 + i) : ℝ) / 2 ^ (i + 1)))
          = (∑ i ∈ Finset.range k,
            ((dyadicOrderedBlockDigit235 (m + 1 + i) : ℝ) / 2 ^ (i + 1))) := rfl
    -- combine through the halved pinning split
    have hsplit :
        trueNormalizedState m ≤ (dyadicOrderedBlockDigit235 m : ℝ) / 2 +
            trueNormalizedState (m + 1) / 2 := by
      calc trueNormalizedState m =
          (dyadicOrderedBlockDigit235 m : ℝ) / (dyadicBlockBase235 m : ℝ) +
            trueNormalizedState (m + 1) / (dyadicBlockBase235 m : ℝ) := hpin
        _ ≤ (dyadicOrderedBlockDigit235 m : ℝ) / 2 +
            trueNormalizedState (m + 1) / 2 := by
            refine add_le_add ?_ ?_
            · exact div_le_div_of_nonneg_right
                (Nat.cast_le.mpr (dyadicOrderedBlockDigit235_le_quadratic m)
                  |> le_of_eq rfl |>.elim |>.elim) hb2
            · exact div_le_div_of_nonneg_left le_rfl hbpos hb2
    have hsumshift :
        ∀ i ∈ Finset.range k,
            ((dyadicOrderedBlockDigit235 (m + 1 + i) : ℝ) / 2 ^ (i + 1))
              ≤ ((dyadicOrderedBlockDigit235 (m + (i + 1)) : ℝ) /
                2 ^ (i + 1)) := by
      intro i _
      rw [Nat.add_assoc]
    calc trueNormalizedState m
        ≤ (dyadicOrderedBlockDigit235 m : ℝ) / 2 +
            trueNormalizedState (m + 1) / 2 := hsplit
      _ ≤ (dyadicOrderedBlockDigit235 m : ℝ) / 2 +
            ((∑ i ∈ Finset.range k,
                ((dyadicOrderedBlockDigit235 (m + (i + 1)) : ℝ) /
                  2 ^ (i + 1))) + trueNormalizedState (m + (k + 1)) /
              2 ^ k) / 2 := by
            refine add_le_add left_le_refl _
              (div_le_div_of_nonneg_left (le_trans hdeep le_refl_) two_pos
                le_rfl)
      _ ≤ (∑ i ∈ Finset.range (k + 1),
              ((dyadicOrderedBlockDigit235 (m + i) : ℝ) / 2 ^ (i + 1))) +
            trueNormalizedState (m + (k + 1)) / 2 ^ (k + 1) := by
            rw [Finset.sum_range_succ]
            simp only [Nat.add_zero, pow_zero, div_one]
            have hpull :
                (∑ i ∈ Finset.range k,
                    ((dyadicOrderedBlockDigit235 (m + (i + 1)) : ℝ) /
                      2 ^ (i + 1)) / 2)
                  ≤ ∑ i ∈ Finset.range k,
                    ((dyadicOrderedBlockDigit235 (m + (i + 1)) : ℝ) /
                      2 ^ (i + 1)) := by
                  refine Finset.sum_le_sum ?_
                  intro i _
                  exact div_le_self (by positivity) (by norm_num)
            have hfinal :
                trueNormalizedState (m + (k + 1)) / 2 ^ k / 2
                  = trueNormalizedState (m + (k + 1)) / 2 ^ (k + 1) := by
                  rw [pow_succ]
                  ring
            nlinarith [hpull, hfinal,
              show (0:ℝ) ≤ (dyadicOrderedBlockDigit235 m : ℝ) from
                Nat.cast_nonneg _]

/-- **Forced equality.**  Any real orbit that follows the source recurrence
from index `A` onward and stays inside the anchor windows of a width
function reproducing along the orbit must coincide with the genuine tail.
This converts "some seed survives all windows" into "the true state is an
integer", which is exactly the quantity the companion experiment maps. -/
theorem surviving_window_orbit_eq_true_state
    (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ)
    (hrec : ∀ n, A ≤ n →
      y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n -
          (dyadicOrderedBlockDigit235 n : ℝ))
    (hwin : ∀ n, A ≤ n → y n ≤
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) +
        width n)
    (hwidth : ∀ m, trueNormalizedState m ≤
      (dyadicOrderedBlockDigit235 m : ℝ) / (dyadicBlockBase235 m : ℝ) +
        width m)
    (hvanish : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      width (A + k) / 2 ^ k < ε) :
    y A = trueNormalizedState A := by
  by_contra hne
  set e : ℝ := |y A - trueNormalizedState A| with e_def
  have hepos : 0 < e := by
    apply abs_pos.mpr
    exact sub_ne_zero_of_ne hne
  obtain ⟨k₀, hk₀⟩ := hvanish (e / 2) (by linarith)
  -- deviation propagation: both orbits satisfy the same affine recursion,
  -- so their difference multiplies by at least 2 per shell
  have hdev : ∀ k : ℕ,
      |y (A + k) - trueNormalizedState (A + k)| =
        (2 : ℝ) ^ k * e := by
    intro k
    induction k with
    | zero => simpa using abs_of_nonneg (by linarith [abs_nonneg (y A)]) |>.elim
    | succ k ih =>
      have h1 := hrec (A + k) (Nat.le_add_left _ _)
      have h2 := dyadicNormalizedShellTsumTailR235_succ (A + k)
      have hb2 : (2 : ℝ) ≤ (dyadicBlockBase235 (A + k) : ℝ) :=
        mod_cast (dyadicBlockBase235_mem_interval (A + k)).1
      rw [h1, h2, ih]
      have : y (A + k) - trueNormalizedState (A + k) ≠ 0 := by
        have := abs_eq_iff.mp (by rw [ih]) |>.elim
        exact sub_ne_zero_of_ne fun h => hne <| by
          have := ih
          rw [h] at this
          simpa using this
      have := abs_mul (y (A + k) - trueNormalizedState (A + k))
        (((2 : ℝ) ^ k)⁻¹ * (dyadicBlockBase235 (A + k) : ℝ) - 1)
      rw [abs_sub_comm] at this
      nlinarith [this, abs_nonneg (y (A + k)),
        abs_nonneg (trueNormalizedState (A + k))]
  -- both orbits sit below anchor + width at index A + k, so their
  -- difference is at most width (A + k)
  have hbound : ∀ k : ℕ,
      |y (A + k) - trueNormalizedState (A + k)| ≤ width (A + k) := by
    intro k
    have hy := hwin (A + k) (Nat.le_add_left _ _)
    have hx := hwidth (A + k)
    set ay := (dyadicOrderedBlockDigit235 (A + k) : ℝ) /
      (dyadicBlockBase235 (A + k) : ℝ) with ay_def
    have hsub : y (A + k) - trueNormalizedState (A + k)
          ≤ width (A + k) := by linarith
    have hsub' : trueNormalizedState (A + k) - y (A + k)
          ≤ width (A + k) := by linarith
    have := abs_sub_abs_le_abs_sub (y (A + k))
      (trueNormalizedState (A + k)) |>.elim
    exact le_trans (abs_sub_abs_le_abs_sub _ _) (by linarith)
  specialize hbound k₀
  specialize hdev k₀
  rw [hdev] at hbound
  have h2pos : (0:ℝ) < (2:ℝ) ^ k₀ := by positivity
  have hlt := hk₀ k₀ (Nat.le_refl _)
  have hcanc : width (A + k₀) / 2 ^ k₀ * 2 ^ k₀ = width (A + k₀) :=
    div_mul_cancel₀ _ h2pos.ne'
  have hm : width (A + k₀) / 2 ^ k₀ * 2 ^ k₀ < e / 2 * 2 ^ k₀ :=
    mul_lt_mul_of_pos_right hlt h2pos
  rw [hcanc] at hm
  have hhalf : e / 2 * 2 ^ k₀ ≤ e * 2 ^ k₀ := by
    nlinarith
  linarith

end ErdosProblems.Erdos269
