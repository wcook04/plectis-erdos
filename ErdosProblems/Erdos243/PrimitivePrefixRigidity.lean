import ErdosProblems.Erdos243.DynamicCancellation

/-!
# Erdős #243: primitive prefix rigidity

Suppose a reduced tail has no cancellation on a block and satisfies
`u (n + 1) + v n = a n * u n` and `v (n + 1) = a n * v n` there.  The first
two theorems give the exact finite-block transfer and approximation formula;
the last two isolate the divisibility forced by a complete prefix product.

The approximation numerator is the terminal primitive numerator itself, so
ordinary rational separation yields only its positivity.  No theorem here
proves that an actual #243 orbit has arbitrarily long cancellation-free
blocks, produces a large prefix gcd, or derives a contradiction.
-/

namespace ErdosProblems.Erdos243

/-- Product of the digits in a cancellation-free block beginning at `r`. -/
def primitiveBlockA (a : ℕ → ℕ) (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => a (r + k) * primitiveBlockA a r k

/-- Second coefficient in the two-term transfer across the same block. -/
def primitiveBlockB (a : ℕ → ℕ) (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      a (r + k) * primitiveBlockB a r k + primitiveBlockA a r k

/-- A cancellation-free reduced block collapses to the two scalar data
`primitiveBlockA` and `primitiveBlockB`.  The numerator identity is stated
over `ℤ` so no truncated subtraction can hide a side condition. -/
theorem primitiveBlock_transfer
    (a u v : ℕ → ℕ)
    (hU : ∀ n, u (n + 1) + v n = a n * u n)
    (hV : ∀ n, v (n + 1) = a n * v n)
    (r k : ℕ) :
    (u (r + k) : ℤ) =
        (primitiveBlockA a r k : ℤ) * u r -
          (primitiveBlockB a r k : ℤ) * v r ∧
      v (r + k) = primitiveBlockA a r k * v r := by
  induction k with
  | zero =>
      simp [primitiveBlockA, primitiveBlockB]
  | succ k ih =>
      rcases ih with ⟨ihu, ihv⟩
      have hstepU :
          (u ((r + k) + 1) : ℤ) =
            (a (r + k) : ℤ) * u (r + k) - v (r + k) := by
        have h := hU (r + k)
        have h' :
            (u ((r + k) + 1) : ℤ) + v (r + k) =
              (a (r + k) : ℤ) * u (r + k) := by
          exact_mod_cast h
        linarith
      constructor
      · rw [Nat.add_succ, hstepU, ihu]
        simp only [primitiveBlockA, primitiveBlockB]
        push_cast
        rw [ihv]
        push_cast
        ring
      · rw [Nat.add_succ, hV, ihv]
        simp [primitiveBlockA]
        ring

/-- Exact finite-window approximation identity.  Its right-hand numerator is
the terminal primitive numerator itself, so ordinary rational separation
recovers only the already-known lower bound `u (r+k) ≥ 1`. -/
theorem primitiveBlock_approximation_exact
    (a u v : ℕ → ℕ)
    (hU : ∀ n, u (n + 1) + v n = a n * u n)
    (hV : ∀ n, v (n + 1) = a n * v n)
    (r k : ℕ)
    (hv : 0 < v r)
    (hA : 0 < primitiveBlockA a r k) :
    (u r : ℚ) / v r -
        (primitiveBlockB a r k : ℚ) / primitiveBlockA a r k =
      (u (r + k) : ℚ) /
        ((primitiveBlockA a r k : ℚ) * v r) := by
  have htransfer :=
    (primitiveBlock_transfer a u v hU hV r k).1
  have htransferQ :
      (u (r + k) : ℚ) =
        (primitiveBlockA a r k : ℚ) * u r -
          (primitiveBlockB a r k : ℚ) * v r := by
    exact_mod_cast htransfer
  have hv0 : (v r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hv)
  have hA0 : (primitiveBlockA a r k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hA)
  field_simp
  rw [htransferQ]
  ring

/-- Every common divisor of a complete preceding digit product and the next
Sylvester factor `a-1` must divide the centred error. -/
theorem primitivePrefix_gcd_dvd_error
    {Q A a u : ℕ} {e : ℤ}
    (hidentity :
      (Q : ℤ) * A = ((a : ℤ) - 1) * u + e) :
    (Int.gcd (A : ℤ) ((a : ℤ) - 1) : ℤ) ∣ e := by
  let d : ℤ := Int.gcd (A : ℤ) ((a : ℤ) - 1)
  have hdA : d ∣ (A : ℤ) := Int.gcd_dvd_left _ _
  have hda : d ∣ (a : ℤ) - 1 := Int.gcd_dvd_right _ _
  have hdQA : d ∣ (Q : ℤ) * A :=
    dvd_mul_of_dvd_right hdA (Q : ℤ)
  have hdau : d ∣ ((a : ℤ) - 1) * u :=
    dvd_mul_of_dvd_left hda (u : ℤ)
  have hde : e = (Q : ℤ) * A - ((a : ℤ) - 1) * u := by
    linarith
  rw [hde]
  exact Int.dvd_sub hdQA hdau

/-- Pointwise consequence: every earlier digit divisor of the complete
prefix product contributes its overlap with `a-1` to the same error. -/
theorem primitiveDigit_gcd_dvd_error
    {Q A a u digit : ℕ} {e : ℤ}
    (hdigit : digit ∣ A)
    (hidentity :
      (Q : ℤ) * A = ((a : ℤ) - 1) * u + e) :
    (Int.gcd (digit : ℤ) ((a : ℤ) - 1) : ℤ) ∣ e := by
  let d : ℤ := Int.gcd (digit : ℤ) ((a : ℤ) - 1)
  have hddigit : d ∣ (digit : ℤ) := Int.gcd_dvd_left _ _
  have hda : d ∣ (a : ℤ) - 1 := Int.gcd_dvd_right _ _
  have hdAint : (digit : ℤ) ∣ (A : ℤ) := by exact_mod_cast hdigit
  have hdA : d ∣ (A : ℤ) := dvd_trans hddigit hdAint
  have hdQA : d ∣ (Q : ℤ) * A :=
    dvd_mul_of_dvd_right hdA (Q : ℤ)
  have hdau : d ∣ ((a : ℤ) - 1) * u :=
    dvd_mul_of_dvd_left hda (u : ℤ)
  have hde : e = (Q : ℤ) * A - ((a : ℤ) - 1) * u := by
    linarith
  rw [hde]
  exact Int.dvd_sub hdQA hdau

end ErdosProblems.Erdos243
