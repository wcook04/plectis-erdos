/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos269.PaperR7FiniteCutRank

namespace Erdos249257.ExternalVerification269FiniteCutRank

/-- The length-`m` cut column at `k`: `1` on the first `k` coordinates, `c` after. -/
abbrev cutColumn := @ErdosProblems.Erdos269.PaperR7.cutVector

/-- Exact rank of a matrix whose columns are the sampled cut family. -/
theorem rank_cutColumnMatrix {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hbound : ∀ k ∈ E, k ≤ m)
    (A : Matrix (Fin m) ι F)
    (hcols : Set.range A.col = Set.range (fun k : E => cutColumn c m k)) :
    A.rank = E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0 :=
  ErdosProblems.Erdos269.PaperR7.rank_cutMatrix c hc0 hc1 hm E hbound A hcols

end Erdos249257.ExternalVerification269FiniteCutRank
