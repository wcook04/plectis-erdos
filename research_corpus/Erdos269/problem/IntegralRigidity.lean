import ErdosProblems.Erdos269.IntegralBranchExtinction

/-!
# Erdős #269: window-residue rigidity of integral states

Under the integrality hypothesis `X_A = w`, the pinning telescope yields
the exact identity `X_(A+k) + N_k = w * B_k` with

`B_0 = 1`,   `B_(k+1) = b_(A+k) * B_k`,
`N_0 = 0`,   `N_(k+1) = b_(A+k) * N_k + d_(A+k)`.

At `k + 1` this reads

`X_(A+k+1) + (b_(A+k) * N_k + d_(A+k)) = w * M_k`,
`M_k = prod_{j<=k} b_(A+j) >= 2^(k+1)`,

which is exactly the congruence consumed by the companion experiment
(`check_erdos269_two_adic_rigidity.py`): the least residue of
`-(b_(A+k) * N_k + d_(A+k))` modulo `M_k` must equal the true state
whenever that state fits inside `(0, hi]` with `hi < M_k`.  A residue
outside the enclosure refutes integrality at index `A`.

This module lands the algebraic skeleton.  The numeric refutations live in
the experiment receipt; their Lean-side consumption needs the cubic width
bound (tracked in the Task Ledger together with the uniform-depth target).
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- Exact companion sums of the integrality hypothesis. -/
noncomputable def rigidityN (A : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => (dyadicBlockBase235 (A + k) : ℤ) * rigidityN A k
      + dyadicOrderedBlockDigit235 (A + k)

theorem rigidityN_succ (A k : ℕ) :
    rigidityN A (k + 1)
      = (dyadicBlockBase235 (A + k) : ℤ) * rigidityN A k
        + dyadicOrderedBlockDigit235 (A + k) := rfl

/-- Radix products along the orbit. -/
noncomputable def rigidityB (A : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (dyadicBlockBase235 (A + k) : ℝ) * rigidityB A k

theorem rigidityB_succ (A k : ℕ) :
    rigidityB A (k + 1)
      = (dyadicBlockBase235 (A + k) : ℝ) * rigidityB A k := rfl

theorem rigidityB_ge_two_pow (A k : ℕ) :
    (2 : ℝ) ^ k ≤ rigidityB A k := by
  induction k with
  | zero => simp [rigidityB]
  | succ k ih =>
    rw [rigidityB_succ, pow_succ]
    have hb2 : (2 : ℝ) ≤ (dyadicBlockBase235 (A + k) : ℝ) :=
      mod_cast (dyadicBlockBase235_mem_interval (A + k)).1
    have hnonneg : (0 : ℝ) ≤ (2 : ℝ) ^ k := pow_nonneg (by norm_num) k
    have hBnonneg : (0 : ℝ) ≤ rigidityB A k := le_trans hnonneg ih
    have hmul : (2 : ℝ) * rigidityB A k
        ≤ (dyadicBlockBase235 (A + k) : ℝ) * rigidityB A k :=
      mul_le_mul_of_nonneg_right hb2 hBnonneg
    linarith [ih, hmul]

/-! ### Deduplication against the generic window algebra

`rigidityN` and `rigidityB` are not new recursions.  They are the generic
first-order affine window accumulators `windowForcing` / `windowBase` of
`RestrictedFloorSum` instantiated at the dyadic radix word
`b_n = dyadicBlockBase235 n` and the ordered digit word
`e_n = dyadicOrderedBlockDigit235 n`.  Recording that identification lets the
window-algebra lemmas of `RestrictedFloorSum` (summation by parts, constant
scaling, affine unrolling) apply verbatim to the rigidity telescope, and stops
the two vocabularies from drifting apart. -/

/-- The rigidity anchor sum **is** the generic `windowForcing` at the dyadic
radix word and the ordered block digits. -/
theorem rigidityN_eq_windowForcing (A k : ℕ) :
    rigidityN A k
      = windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
          (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) A k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hw : windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
          (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) A (k + 1)
        = (dyadicBlockBase235 (A + k) : ℤ)
            * windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
                (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) A k
          + (dyadicOrderedBlockDigit235 (A + k) : ℤ) := rfl
    rw [rigidityN_succ, hw, ih]

/-- The rigidity radix product **is** the generic `windowBase` at the dyadic
radix word, cast to `ℝ`.  In particular it is an integer. -/
theorem rigidityB_eq_windowBase (A k : ℕ) :
    rigidityB A k
      = ((windowBase (fun n => (dyadicBlockBase235 n : ℤ)) A k : ℤ) : ℝ) := by
  induction k with
  | zero => simp [rigidityB, windowBase]
  | succ k ih =>
    have hb : windowBase (fun n => (dyadicBlockBase235 n : ℤ)) A (k + 1)
        = (dyadicBlockBase235 (A + k) : ℤ)
            * windowBase (fun n => (dyadicBlockBase235 n : ℤ)) A k := rfl
    rw [rigidityB_succ, ih, hb]
    push_cast
    ring

/-- **Telescope identity.**  Under the integrality hypothesis at `A`, every
true state satisfies `X_(A+k) + N_k = w * B_k`. -/
theorem rigidity_telescope {A : ℕ} {w : ℤ}
    (hint : trueNormalizedState A = (w : ℝ)) (k : ℕ) :
    trueNormalizedState (A + k) + (rigidityN A k : ℝ)
      = (w : ℝ) * rigidityB A k := by
  induction k with
  | zero =>
    simp only [rigidityN, rigidityB, add_zero, mul_one]
    simpa using hint
  | succ k ih =>
    have hrec0 := dyadicNormalizedShellTsumTailR235_succ (A + k)
    rw [show (A + k) + 1 = A + (k + 1) from rfl] at hrec0
    -- the same recurrence, phrased on `trueNormalizedState` (a definitional
    -- abbreviation of the normalized tail state)
    have hrec : trueNormalizedState (A + (k + 1))
        = (dyadicBlockBase235 (A + k) : ℝ) * trueNormalizedState (A + k)
          - (dyadicOrderedBlockDigit235 (A + k) : ℝ) := hrec0
    rw [rigidityN_succ, rigidityB_succ]
    push_cast
    linear_combination hrec + (dyadicBlockBase235 (A + k) : ℝ) * ih

/-- **Window-residue rigidity at depth `k`.**  Restating the telescope one
shell deeper: the state at `A+k+1` plus the anchor sum equals `w * M_k`
with `M_k = rigidityB A (k+1) >= 2^(k+1)`.  Consequently the least residue
of `-(b_(A+k) * N_k + d_(A+k))` modulo the integer radix product must hit
the enclosure of the true state exactly once the modulus exceeds that
enclosure - otherwise no integral state exists at `A`. -/
theorem rigidity_state_eq_residue {A : ℕ} {w : ℤ}
    (hint : trueNormalizedState A = (w : ℝ)) (k : ℕ) :
    trueNormalizedState (A + k + 1)
        + ((rigidityN A (k + 1) : ℝ))
      = (w : ℝ) * rigidityB A (k + 1) :=
  rigidity_telescope hint (k + 1)

/-- The pinning telescope stated purely in the shared window-algebra
vocabulary of `RestrictedFloorSum`: no separate rigidity recursion is needed,
and both companion sums are visibly integers. -/
theorem rigidity_telescope_window {A : ℕ} {w : ℤ}
    (hint : trueNormalizedState A = (w : ℝ)) (k : ℕ) :
    trueNormalizedState (A + k)
        + ((windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
              (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) A k : ℤ) : ℝ)
      = (w : ℝ)
          * ((windowBase (fun n => (dyadicBlockBase235 n : ℤ)) A k : ℤ) : ℝ) := by
  rw [← rigidityN_eq_windowForcing, ← rigidityB_eq_windowBase]
  exact rigidity_telescope hint k

end ErdosProblems.Erdos269
