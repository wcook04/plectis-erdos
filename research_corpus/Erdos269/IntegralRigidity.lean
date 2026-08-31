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
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hb2 hnonneg)
    nlinarith [ih, hnonneg]

/-- **Telescope identity.**  Under the integrality hypothesis at `A`, every
true state satisfies `X_(A+k) + N_k = w * B_k`. -/
theorem rigidity_telescope {A : ℕ} {w : ℤ}
    (hint : trueNormalizedState A = (w : ℝ)) (k : ℕ) :
    trueNormalizedState (A + k) + (rigidityN A k : ℝ)
      = (w : ℝ) * rigidityB A k := by
  induction k with
  | zero =>
    simp only [rigidityN, rigidityB, Nat.cast_zero, add_zero,
      Nat.cast_one, mul_one]
    simpa using hint
  | succ k ih =>
    have hrec := dyadicNormalizedShellTsumTailR235_succ (A + k)
    rw [show (A + k) + 1 = A + (k + 1) from rfl] at hrec
    rw [rigidityN_succ, rigidityB_succ, hrec, ih]
    push_cast
    ring

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

end ErdosProblems.Erdos269
