import Erdos249257.CertificateKernel

/-!
Paper-form restatement of the long Erdős #257 `thm` at
`paper/reasoning-parts/erdos257/a257_front.tex:2068` ("Residue-class support"):
for integers `b ≥ 2`, `m ≥ 1` and any residue `c`, the series
`∑_{n ≥ 1, n ≡ c (mod m)} (b^n − 1)^{-1}` is irrational.

The existing tree theorem `irrational_erdosSupportSeries_residueClass` is stated
for a natural residue and for the support `{n | n % m = c % m}`, which also
contains `0` when `m ∣ c`.  The paper's support is restricted to `n ≥ 1` and its
residue is an arbitrary integer, so the restatement below carries both.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21
open Erdos249257

/-- Long `thm` "Residue-class support" (line 2068): for `b ≥ 2`, `m ≥ 1` and any
integer residue `c`, the series over the positive `n ≡ c (mod m)` is
irrational. -/
theorem irrational_residueClass_positive_support
    (b m : ℕ) (c : ℤ) (hb : 2 ≤ b) (hm : 1 ≤ m) :
    Irrational (erdosSupportSeries b
      {n : ℕ | 0 < n ∧ (n : ℤ) % (m : ℤ) = c % (m : ℤ)}) := by
  classical
  have hmz : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hnn : 0 ≤ c % (m : ℤ) := Int.emod_nonneg c (ne_of_gt hmz)
  have hlt : c % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos c hmz
  set c' : ℕ := (c % (m : ℤ)).toNat with hc'def
  have hc'cast : ((c' : ℕ) : ℤ) = c % (m : ℤ) := Int.toNat_of_nonneg hnn
  have hc'lt : c' < m := by
    have h : ((c' : ℕ) : ℤ) < (m : ℤ) := by rw [hc'cast]; exact hlt
    exact_mod_cast h
  have hc'mod : c' % m = c' := Nat.mod_eq_of_lt hc'lt
  have key : ∀ a : ℕ, ((a : ℤ) % (m : ℤ) = c % (m : ℤ) ↔ a % m = c' % m) := by
    intro a
    rw [hc'mod, ← hc'cast, ← Int.natCast_mod]
    constructor <;> intro h <;> exact_mod_cast h
  have hset : erdosSupportSeries b
        {n : ℕ | 0 < n ∧ (n : ℤ) % (m : ℤ) = c % (m : ℤ)}
      = erdosSupportSeries b {n : ℕ | n % m = c' % m} := by
    unfold erdosSupportSeries
    refine tsum_congr fun a => ?_
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [Set.indicator_apply]
      norm_num
    · have hiff : (a ∈ {n : ℕ | 0 < n ∧ (n : ℤ) % (m : ℤ) = c % (m : ℤ)})
          ↔ (a ∈ {n : ℕ | n % m = c' % m}) := by
        simp only [Set.mem_setOf_eq]
        exact ⟨fun h => (key a).mp h.2, fun h => ⟨ha, (key a).mpr h⟩⟩
      by_cases h : a ∈ {n : ℕ | 0 < n ∧ (n : ℤ) % (m : ℤ) = c % (m : ℤ)}
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
  rw [hset]
  exact irrational_erdosSupportSeries_residueClass b m c' hb hm

#print axioms irrational_residueClass_positive_support
end ErdosProblems.Erdos257.PaperCompleteR21
