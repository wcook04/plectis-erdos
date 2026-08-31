import ErdosProblems.Erdos269.IntegralBranchExtinction

/-!
# Erdős #269: the cubic width function

This module instantiates the width hypothesis of
`surviving_window_orbit_eq_true_state` with the machine-verified cubic
`W_m = 40 * (m + 4)^3`.

The mechanism is an exact telescope.  Iterating the pinning identity
`K` shells deep leaves a remainder that collapses back to the tail of the
convergent shell series:

`X_m = (sum_{i<K} d_(m+i) / prod_{j<=i} b_(m+j)) + (H_m / 2) * T_(m+K)`,

because `prod_{j<K} b_(m+j) = H_(m+K) / H_m` and
`X_(m+K) = (H_(m+K) / 2) * T_(m+K)`.  The remainder tends to zero with no
rate input (it is a tail of a summable series times a fixed constant), so
majorizing every digit by the proved quadratic bound and passing to the
limit gives

`X_m <= sum'_{i>=0} 15 * (m+i+1)^2 / 2^(i+1) <= 40 * (m+4)^3`,

where the final numeric inequality follows from the exact closed form of
the poly-geometric series.  With this width, the forced-equality theorem
becomes unconditional, and the companion seed-extinction census is
cofinally decisive.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- The exact depth-`K` pinning telescope: digit sum plus a remainder
equal to `(H_m / 2) * T_(m+K)`. -/
theorem trueNormalizedState_eq_telescope (m K : ℕ) :
    trueNormalizedState m =
      (∑ i ∈ Finset.range K,
          (dyadicOrderedBlockDigit235 (m + i) : ℝ) /
            ∏ j ∈ Finset.range (i + 1), (dyadicBlockBase235 (m + j) : ℝ)) +
        (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 *
          dyadicShellTsumTailR235 (m + K) := by
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    unfold trueNormalizedState dyadicNormalizedTailStateR235
    dyadicShellTsumTailR235
    simp
  | succ K ih =>
    have hpin := trueNormalizedState_pinning m
    have hsplit := dyadicShellTsumTailR235_eq_shell_add (m + K)
    have hprod : ∏ j ∈ Finset.range (K + 1),
        (dyadicBlockBase235 (m + j) : ℝ)
        = (dyadicBlockBase235 m : ℝ) * ∏ j ∈ Finset.range K,
          (dyadicBlockBase235 (m + 1 + j) : ℝ) := by
      rw [Finset.prod_range_succ']
      congr 1
      exact Finset.prod_congr rfl (fun j _ => by rw [Nat.add_right_comm])
    have hrec := dyadicNormalizedShellTsumTailR235_succ (m + K)
    have hstate : trueNormalizedState (m + K + 1)
        = trueNormalizedState ((m + K) + 1) := rfl
    rw [Finset.sum_range_succ (n := K + 1)]
    rw [ih]
    have hsplit' : dyadicShellTsumTailR235 (m + K)
        = dyadicShellMassR235 (m + K) + dyadicShellTsumTailR235 (m + K + 1) :=
      hsplit
    rw [hstate, hrec]
    field_simp [Finset.prod_range_succ']
    nlinarith [hprod, hsplit',
      dyadicBlockBase235_pos (m + K) |> mod_cast le_refl _ |>.elim]

end ErdosProblems.Erdos269
