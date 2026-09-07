/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.ParityPerturbedRationalControl

/-!
# Source transport for the parity-perturbed rational control in Erdős #249

The declarations below restate the Mathlib-only challenge vocabulary and
transport the exact source theorems without strengthening their hypotheses.
-/

namespace Erdos249257.ExternalVerification249ParityPerturbedRationalControl

open Module Filter

noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)

def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)

abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))

def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val

noncomputable def digit (x : ℝ) : ℤ := ⌊4 * x + 2 / 3⌋

noncomputable def step (x : ℝ) : ℝ := 4 * x - (digit x : ℝ)

noncomputable def rem (x : ℝ) : ℕ → ℝ
  | 0 => x
  | m + 1 => step (rem x m)

noncomputable def dig (x : ℝ) (m : ℕ) : ℤ := digit (rem x m)

noncomputable abbrev S : ℝ := binaryCoeffSeries Nat.totient

noncomputable def xi : ℝ := 5 / 4 - S

noncomputable def delta (n : ℕ) : ℤ :=
  if n % 2 = 0 ∧ 2 ≤ n then dig xi (n / 2 - 1) else 0

noncomputable def control (n : ℕ) : ℕ := ((Nat.totient n : ℤ) + delta n).toNat

/-- The challenge vocabulary reproduces the source construction verbatim, so
the two control sequences agree. -/
private theorem control_eq_source :
    control = ErdosProblems.Erdos249.ParityPerturbedRationalControl.control := by
  have hdigit : ∀ x : ℝ,
      digit x = ErdosProblems.Erdos249.ParityPerturbedRationalControl.digit x :=
    fun _ => rfl
  have hstep : ∀ x : ℝ,
      step x = ErdosProblems.Erdos249.ParityPerturbedRationalControl.step x :=
    fun _ => rfl
  have hrem : ∀ (x : ℝ) (m : ℕ),
      rem x m = ErdosProblems.Erdos249.ParityPerturbedRationalControl.rem x m := by
    intro x m
    induction m with
    | zero => rfl
    | succ m ih =>
        simp only [rem, ErdosProblems.Erdos249.ParityPerturbedRationalControl.rem]
        rw [ih, hstep]
  have hdig : ∀ (x : ℝ) (m : ℕ),
      dig x m = ErdosProblems.Erdos249.ParityPerturbedRationalControl.dig x m := by
    intro x m
    simp only [dig, ErdosProblems.Erdos249.ParityPerturbedRationalControl.dig]
    rw [hrem, hdigit]
  have hdelta : ∀ n : ℕ,
      delta n = ErdosProblems.Erdos249.ParityPerturbedRationalControl.delta n := by
    intro n
    simp only [delta, ErdosProblems.Erdos249.ParityPerturbedRationalControl.delta]
    split_ifs with h
    · exact hdig xi (n / 2 - 1)
    · rfl
  funext n
  simp only [control, ErdosProblems.Erdos249.ParityPerturbedRationalControl.control]
  rw [hdelta]

theorem parity_perturbed_rational_control :
    (∀ n, control n ≤ n) ∧ (∀ n, n % 2 = 1 → control n = Nat.totient n) ∧
      (∀ n, |(control n : ℤ) - Nat.totient n| ≤ 2) ∧
      binaryCoeffSeries control = 5 / 4 := by
  rw [control_eq_source]
  exact
    ErdosProblems.Erdos249.ParityPerturbedRationalControl.parity_perturbed_rational_control

theorem control_series : binaryCoeffSeries control = 5 / 4 := by
  rw [control_eq_source]
  exact ErdosProblems.Erdos249.ParityPerturbedRationalControl.control_series

theorem not_irrational_control : ¬ Irrational (binaryCoeffSeries control) := by
  rw [control_eq_source]
  exact ErdosProblems.Erdos249.ParityPerturbedRationalControl.not_irrational_control

theorem control_temperedOrbit_carryRank_unbounded :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit control v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            finrank ℚ
              (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by
  rw [control_eq_source]
  exact
    ErdosProblems.Erdos249.ParityPerturbedRationalControl.control_temperedOrbit_carryRank_unbounded

theorem finrank_canonicalCarryKernel_ge_of_oddAgree {c : ℕ → ℕ}
    (hodd : ∀ n, n % 2 = 1 → c n = Nat.totient n)
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit c v u) (e : ℕ) :
    2 ^ e - 1 ≤
      finrank ℚ
        (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) :=
  ErdosProblems.Erdos249.ParityPerturbedRationalControl.finrank_canonicalCarryKernel_ge_of_oddAgree
    hodd hv hu e

end Erdos249257.ExternalVerification249ParityPerturbedRationalControl
