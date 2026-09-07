/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.PaperCompleteR7.GenericCertificates

/-!
# Source transport: generic certificate soundness and the tail-period law

The challenge vocabulary is redeclared with the source bodies, so the two
transported statements are token-identical to the trusted challenge.
-/

namespace Erdos249257.ExternalVerification249GenericCertificateSoundness

noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

def window (c : ℕ → ℕ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((c (N + h + 1 + j) : ℤ) - (c (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

def Kill (c : ℕ → ℕ) (h N L : ℕ) : Prop :=
  (N : ℤ) + h + L + 2 < window c h N L % 2 ^ L ∧
    window c h N L % 2 ^ L < 2 ^ L - ((N : ℤ) + h + L + 2)

open ErdosProblems.Erdos249.PaperCompleteR7.GenericCertificates in
theorem generic_soundness (c : ℕ → ℕ) (hg : ∀ n, c n ≤ n)
    {h N L : ℕ} (hkill : Kill c h N L) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∉ Set.range ((↑) : ℤ → ℝ) := by
  have hkill' :
      ErdosProblems.Erdos249.PaperCompleteR7.GenericCertificates.Kill c h N L := by
    simpa only [Kill,
      ErdosProblems.Erdos249.PaperCompleteR7.GenericCertificates.Kill,
      window,
      ErdosProblems.Erdos249.PaperCompleteR7.GenericCertificates.window]
      using hkill
  simpa only [binaryCoeffTail, Erdos257PeriodNoncollapse.binaryCoeffTail] using
    ErdosProblems.Erdos249.PaperCompleteR7.GenericCertificates.generic_soundness
      c hg hkill'

theorem generic_tail_period (c : ℕ → ℕ) (hg : ∀ n, c n ≤ n)
    (p : ℤ) (e m h N : ℕ) (hm : 0 < m) (heN : e ≤ N)
    (hdiv : m ∣ 2 ^ h - 1)
    (hseries : binaryCoeffSeries c = (p : ℝ) / ((2 : ℝ) ^ e * (m : ℝ))) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∈ Set.range ((↑) : ℤ → ℝ) := by
  have hseries' :
      Erdos257PeriodNoncollapse.binaryCoeffSeries c =
        (p : ℝ) / ((2 : ℝ) ^ e * (m : ℝ)) := by
    simpa only [binaryCoeffSeries, Erdos257PeriodNoncollapse.binaryCoeffSeries]
      using hseries
  simpa only [binaryCoeffTail, Erdos257PeriodNoncollapse.binaryCoeffTail] using
    ErdosProblems.Erdos249.PaperCompleteR7.GenericCertificates.generic_tail_period
      c hg p e m h N hm heN hdiv hseries'

end Erdos249257.ExternalVerification249GenericCertificateSoundness
