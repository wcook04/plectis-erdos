/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #269 finite sampled cut rank

Fix a field `F` and a scalar `c` with `c ≠ 0` and `c ≠ 1`.  For `0 ≤ k ≤ m` the
cut column `v_k` of length `m` carries `1` in each of its first `k` coordinates
and `c` in the remaining ones.  A matrix whose set of columns is exactly
`{v_k : k ∈ E}` for a finite set `E` of cuts has rank `|E|`, except that the two
extreme cuts `0` and `m` are proportional, so their simultaneous presence drops
the rank by exactly one.

The column hypothesis is stated as an equality of column ranges, so repetitions
and permutations of the columns are covered without a separate assumption, and
no ordering of `E` is imposed.

This is a finite linear-algebra theorem about the sampled cut family.  It does
not assert anything about the running least common multiple of `{2,3,5}`-smooth
numbers and it does not settle Erdős Problem 269, which remains open.
-/

namespace Erdos249257.ExternalVerification269FiniteCutRank

/-- The length-`m` cut column at `k`: `1` on the first `k` coordinates, `c` after. -/
def cutColumn {F : Type*} [Field F] (c : F) (m k : ℕ) : Fin m → F :=
  fun i => if (i : ℕ) < k then 1 else c

/-- Exact rank of a matrix whose columns are the sampled cut family. -/
theorem rank_cutColumnMatrix {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hbound : ∀ k ∈ E, k ≤ m)
    (A : Matrix (Fin m) ι F)
    (hcols : Set.range A.col = Set.range (fun k : E => cutColumn c m k)) :
    A.rank = E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0 := sorry

end Erdos249257.ExternalVerification269FiniteCutRank
