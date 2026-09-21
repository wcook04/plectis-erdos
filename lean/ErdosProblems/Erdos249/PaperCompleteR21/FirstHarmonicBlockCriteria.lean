import Erdos249257.FirstHarmonicPivot

/-! Paper-form restatements of the long #249 paper's exponential-sum block:

* `thm:hgap-real` — a real-part saving of `9X/10` on a dyadic block, under
  the room condition `16(2X+h+L+2) ≤ 2^L`, produces a certificate in that
  block;
* `thm:hgap-subset` — the same implication for any nonempty finite subset
  `T ⊆ [0,2X)`, which generalises the block form;
* `thm:hgap-norm` — the complex norm saving `21X/25` implies the real-part
  saving, and the cofinal block norm condition implies irrationality of `S`.

Here `D(h,N,L) = windowDiscrepancy h N L`, `C h N L = certifiedKill h N L`,
`Re E(h,N,L) = cos(2π·(D mod 2^L)/2^L)` and `E(h,N,L) = windowFirstExp h N L`. -/

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller

/-- The paper's `Re E(h,N,L)` written out as a cosine of the normalised
endpoint residue. -/
theorem windowFirstCos_unfolded (h N L : ℕ) :
    windowFirstCos h N L
      = Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))) :=
  rfl

/-! ### `thm:hgap-real` — a real-part bound gives a certificate -/

/-- **A real-part bound gives a certificate.**  For all `h, X, L` with `0 < X`
and `16(2X+h+L+2) ≤ 2^L`, a saving `∑_{N=X}^{2X-1} Re E(h,N,L) ≤ 9X/10`
produces some `N ∈ [X,2X)` with `C h N L`. -/
theorem exists_certifiedKill_of_block_real_part_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L :=
  exists_certifiedKill_of_first_harmonic_gap hX hroom hgap

/-! ### `thm:hgap-subset` — the same implication for a nonempty subset -/

/-- **The same implication for a nonempty subset.**  For any nonempty finite
`T ⊆ [0,2X)` and the same room condition, a saving
`∑_{N ∈ T} Re E(h,N,L) ≤ (9/10)|T|` produces some `N ∈ T` with `C h N L`. -/
theorem exists_certifiedKill_of_subset_real_part_bound {h X L : ℕ}
    (T : Finset ℕ)
    (hTlt : ∀ N ∈ T, N < 2 * X)
    (hTne : T.Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ T,
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * T.card) :
    ∃ N ∈ T, certifiedKill h N L :=
  exists_certifiedKill_of_first_harmonic_gap_subset T hTlt hTne hroom hgap

/-- **The subset form generalises the block form.**  Taking `T = [X,2X)`
recovers the previous theorem; no density or partition hypothesis is used. -/
theorem block_real_part_bound_of_subset_form {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  refine exists_certifiedKill_of_subset_real_part_bound (X := X) (Finset.Ico X (2 * X))
    (fun N hN => (Finset.mem_Ico.mp hN).2) ⟨X, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    hroom ?_
  have hcard : (Finset.Ico X (2 * X)).card = X := by
    rw [Nat.card_Ico]
    omega
  rw [hcard]
  exact hgap

/-! ### `thm:hgap-norm` — a norm bound gives the real-part criterion -/

/-- The block norm condition, written out. -/
theorem blockNormCondition_unfolded :
    DTWFirstHarmonicNormGap ↔
      ∀ h : ℕ, 0 < h → ∀ X₀ : ℕ, ∃ X L : ℕ,
        max X₀ 1 ≤ X ∧
        16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
        ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X :=
  Iff.rfl

/-- **The complex norm bound implies the real-part bound.**  Since
`Re z ≤ ‖z‖` and `21/25 < 9/10`, a norm saving of `21X/25` gives a real-part
saving of `9X/10`. -/
theorem real_part_bound_of_norm_bound {h X L : ℕ} (hX : (0 : ℝ) ≤ X)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    (21 / 25 : ℝ) < 9 / 10 ∧
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X := by
  refine ⟨by norm_num, ?_⟩
  calc
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L)
        = (∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L).re := by simp
    _ ≤ ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ := Complex.re_le_norm _
    _ ≤ (21 / 25 : ℝ) * X := hgap
    _ ≤ (9 / 10 : ℝ) * X := by nlinarith

/-- **A norm bound gives a certificate.** -/
theorem exists_certifiedKill_of_block_norm_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L :=
  exists_certifiedKill_of_first_harmonic_norm_gap hX hroom hgap

/-- **The block norm condition implies irrationality of `S`.** -/
theorem irrational_of_blockNormCondition (hgap : DTWFirstHarmonicNormGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_first_harmonic_norm_gap hgap

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.windowFirstCos_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_real_part_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_subset_real_part_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.block_real_part_bound_of_subset_form
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.blockNormCondition_unfolded
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.real_part_bound_of_norm_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_norm_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_blockNormCondition
