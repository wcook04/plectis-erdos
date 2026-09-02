/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #249 carry-rank frontier

This Mathlib-only challenge exposes the complete carry anti-compression chain:
the rationality/tempered-orbit equivalence, exact recovery of totient channels
from adjacent carry sections, certificate-driven rank transport, the resulting
all-level rank lower bound under hypothetical non-irrationality, the exact
tail-integrality/divisibility bridge, and the joint modular-period/unbounded-
rank frontier.

The final theorem is not an irrationality proof.  Eventual periodicity modulo
the orbit multiplier is quotient compression and does not supply a finite
`ℚ`-rank upper bound for the integral carry.
-/

namespace Erdos249257.ExternalVerification249CarryRankFrontier

noncomputable section

noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Filter.Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N)
      Filter.atTop (nhds 0)

def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)

def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)

abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)

def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ =>
      totientKernelSeq (j.val + 1) (2 * r.val + 1)

abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))

def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val

structure SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ℕ → ℚ) where
  rowIndex : ι → ℕ
  det_ne_zero :
    Matrix.det (fun i j : ι => family j (rowIndex i)) ≠ 0

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

def CarrySectionsEventuallyPeriodicMod
    (v h N₀ : ℕ) (u : ℕ → ℤ) : Prop :=
  ∀ j r n : ℕ, N₀ ≤ n →
    u (2 ^ j * n + r) ≡ u (2 ^ j * (n + h) + r) [ZMOD (v : ℤ)]

/-- Subexponential binary coefficient tails are non-irrational exactly when
they admit a positive-multiplier integral tempered orbit. -/
theorem not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    ¬ Irrational (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
        IsTemperedBinaryOrbit c v u := by
  sorry

/-- Every positive-residue totient channel is the scaled difference of two
adjacent carry sections. -/
theorem totient_carryKernel_diff
    {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u)
    {j r : ℕ} (hr : 0 < r) :
    (fun n => (v : ℚ) * totientKernelSeq j r n) =
      fun n => 2 * carryKernelSeq u j (r - 1) n -
        carryKernelSeq u j r n := by
  sorry

/-- A separated canonical totient minor forces at least `2^e - 1` rational
dimensions among the carry sections through level `e`. -/
theorem finrank_canonicalCarryKernel_ge_of_certificate
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (e : ℕ)
    (cert : SeparatedMinorCertificate (canonicalTotientKernelFamily e)) :
    2 ^ e - 1 ≤
      Module.finrank ℚ
        (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by
  sorry

/-- Hypothetical non-irrationality produces one tempered integral carry with
rank at least `2^e - 1` at every dyadic level. -/
theorem not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e))) := by
  sorry

/-- Tail-difference integrality is exactly divisibility of the corresponding
carry displacement. -/
theorem carryShift_dvd_iff_tailDiff_mem_int
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    (v : ℤ) ∣ u (N + k) - u N ↔
      totientTail (N + k) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- The exact rationality frontier: one rationality-supplied carry is both
uniformly eventually periodic modulo its multiplier and of unbounded
torsion-free dyadic-section rank. -/
theorem not_irrational_totientSeries_implies_mod_period_and_unbounded_rank
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u := by
  sorry

end

end Erdos249257.ExternalVerification249CarryRankFrontier
